from functools import singledispatch
from itertools import combinations
from typing import List, Union

from .converter import Converter
from ..utils import *
from ...constraints.constraints import *
from ...objects.configuration import Configuration


class PhaverConverter(Converter):
    def __init__(self, config: Configuration):
        self._model = ""
        self._conf = ""
        self.config: Configuration = config

    def convert(self, ha: HybridAutomaton, system_vars: Set[Variable]=set()):
        self._reset()
        self._preprocessing(ha, system_vars)

        contr_var = get_ha_vars(ha)
        contr_var_decl = "contr_var: {};".format(", ".join([str(v) for v in contr_var]))

        synclabs = "synclabs: stllab;"

        modes_str_list = list()
        for mode in ha.get_modes():
            mode_str = [
                "loc mode_{}: while".format(mode.id),
                    # invariant
                    " & ".join([obj2phaver(inv) for inv in mode.invariant]),
                # dynamics
                "wait {",
                    " & ".join(["{}' == {}".format(v.id, obj2phaver(mode.dynamics[v])) for v in mode.dynamics]),
                "};"
            ]

            modes_str_list.append("\n".join(mode_str))

            for jp in ha.get_next_edges(mode):
                guard = "true" if len(jp.guard) <= 0 else " & ".join([obj2phaver(g) for g in jp.guard])
                jp_str = [
                    "when",
                    guard,
                    "sync stllab do",
                    "{",
                        " & ".join(["{}' == {}".format(v, obj2phaver(e)) for v, e in jp.reset]),
                    "}} goto mode_{};".format(jp.get_trg().id)
                ]
                modes_str_list.append("\n".join(jp_str))

        # make initial
        v_set = get_ha_vars(ha)

        v_set = v_set.difference(system_vars)

        bound_box = ha.get_bound_box()
        initial_modes = set(filter(lambda x: x.is_initial(), ha.get_modes()))
        
        init_bounds = list()
        for v in v_set:
            assert v in bound_box

            bb = bound_box[v]
            init_bounds.append(obj2phaver(And([bb.left <= v, v <= bb.right])))

        init_bound = " & ".join(init_bounds)
        init_conds = " , ".join(["mode_{} & {}".format(m.id, init_bound) for m in initial_modes])


        self._model = "\n".join([contr_var_decl, synclabs, 
                                 "\n".join(modes_str_list),
                                 "initially: {};".format(init_conds)])

        # make config
        common_section = self.config.get_section("common")
        g_n = common_section.get_value("goal")

        sys_name = common_section.get_value("system-name")
        sys_finals = common_section.get_value("system-finals")

        finals = sys_finals.split(",")

        final_modes = set(filter(lambda x: x.is_final(), ha.get_modes()))
        final_mode_ids = set(map(lambda x: "mode_{}".format(x.id), final_modes))

        final_mode_composed = list(product(finals, final_mode_ids))

        final_conds = " , ".join(["{}~{} & true".format(m1, m2) for m1, m2 in final_mode_composed])


        basic_conf = [
            "REACH_USE_CONVEX_HULL = true;",
            "REACH_USE_CONSTRAINT_HULL = true;",

            "composed = {} & {} ;".format(sys_name, g_n),

            "forbidden = composed.{{ {} }};".format(final_conds),
            "echo \"\";",
            "echo \"Computing reachable states:\";",

            "reach = composed.reachable;",

            "res = reach;",
            "res.intersection_assign(forbidden);",
            "echo \"\";",
            "echo \"Reachable forbidden states:\";",
            "res.print;",
            "echo \"\";",
            "echo \"Reachable forbidden states empty?\";",
            "res.is_empty;",
            "echo \"\";"
        ]

        self._conf = "\n".join(basic_conf)



    def write(self, file_name: str):
        common_section = self.config.get_section("common")
        g_n, b = common_section.get_value("goal"), common_section.get_value("bound")

        if int(b) <= 0:
            bound = "ub"
        else:
            bound = "b{}".format(b)

        f = open("{}.pha".format(file_name), "r")
        orig_ha = f.read()
        f.close()

        f_n = "{}_{}_{}.pha".format(file_name, g_n, bound)
        c_n = "{}_{}_{}.cfg".format(file_name, g_n, bound)

        f = open(f_n, "w")
        self._model = "\n".join([orig_ha, "automaton {}".format(g_n), self._model, "end"])
        f.write(self._model)
        f.close()

        f = open(c_n, "w")
        f.write(self._conf)
        f.close()

        print("write hybrid automaton to {} and config to {}".format(f_n, c_n))

    def _reset(self):
        self._string = ""

    @classmethod
    def _preprocessing(cls, ha: HybridAutomaton, system_vars: Set[Variable]):
        v_s = get_ha_vars(ha)

        # do not consider system variables
        # v_s = v_s.difference(system_vars)
        for jp in get_jumps(ha):
            r_v = {v for v, _ in jp.reset}
            s_r = {(v, v) for v in v_s.difference(r_v)}
            jp.add_reset(*s_r)


@singledispatch
def obj2phaver(const: Union[Formula, Expr]):
    raise Exception("fail to translate to flowstar object ({})".format(const))


@obj2phaver.register(Variable)
def _(const: Variable):
    return const.id


@obj2phaver.register(Constant)
def _(const: Constant):
    return const.value


@obj2phaver.register(And)
def _(const: And):
    return ' & '.join([obj2phaver(c) for c in const.children])


@obj2phaver.register(Or)
def _(const: Or):
    return ' | '.join([obj2phaver(c) for c in const.children])


@obj2phaver.register(Geq)
def _(const: Geq):
    return "{} >= {}".format(obj2phaver(const.left), obj2phaver(const.right))


@obj2phaver.register(Gt)
def _(const: Gt):
    return "{} > {}".format(obj2phaver(const.left), obj2phaver(const.right))


@obj2phaver.register(Leq)
def _(const: Leq):
    return "{} <= {}".format(obj2phaver(const.left), obj2phaver(const.right))


@obj2phaver.register(Lt)
def _(const: Geq):
    return "{} < {}".format(obj2phaver(const.left), obj2phaver(const.right))


@obj2phaver.register(Eq)
def _(const: Eq):
    return "{} == {}".format(obj2phaver(const.left), obj2phaver(const.right))


@obj2phaver.register(Add)
def _(const: Add):
    return "({} + {})".format(obj2phaver(const.left), obj2phaver(const.right))


@obj2phaver.register(Sub)
def _(const: Sub):
    return "({} - {})".format(obj2phaver(const.left), obj2phaver(const.right))


@obj2phaver.register(Neg)
def _(const: Neg):
    return "(- {})".format(obj2phaver(const.child))


@obj2phaver.register(Mul)
def _(const: Mul):
    return "({} * {})".format(obj2phaver(const.left), obj2phaver(const.right))


@obj2phaver.register(Div)
def _(const: Div):
    return "(" + obj2phaver(const.left) + " / " + obj2phaver(const.right) + ")"
