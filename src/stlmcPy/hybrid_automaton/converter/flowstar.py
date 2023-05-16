from functools import singledispatch
from typing import Union

from .converter import Converter
from ..utils import *
from ...constraints.constraints import *
from ...objects.configuration import Configuration


class FlowStarConverter(Converter):
    def __init__(self, config: Configuration):
        self._string = ""
        self.config: Configuration = config

    def convert(self, ha: HybridAutomaton):
        self._reset()
        preprocessing(ha)

        modes_str_list = list()
        for mode in ha.get_modes():
            mode_str = "mode_{}{{\n".format(mode.id)
            mode_str += "poly ode 1\n{" if mode.is_initial() else "nonpoly ode\n{"
            # mode_str += "poly ode 1\n{"
            # mode_str += "poly ode 3\n{"

            for v in mode.dynamics:
                e = mode.dynamics[v]
                mode_str += "{}\' = {}\n".format(v, str(obj2fs(e))).replace("**", "^")
            mode_str += "}\n"

            mode_str += "inv {\n"
            for inv in mode.invariant:
                mode_str += "{}\n".format(obj2fs(inv)) \
                    .replace(">", ">=").replace("<", "<=") \
                    .replace(">==", ">=").replace("<==", "<=").replace("**", "^")
            mode_str += "}\n}"
            modes_str_list.append(mode_str)
        modes_str = "modes {{\n {}\n}}\n".format("\n".join(modes_str_list))

        trans_str_list = list()
        jumps = get_jumps(ha)
        for transition in jumps:
            assert isinstance(transition, Transition)
            t_str = "mode_{} -> mode_{}\n".format(transition.get_src().id, transition.get_trg().id)
            t_str += "guard {\n"
            for guard in transition.guard:
                _str = "{}\n".format(obj2fs(guard))
                t_str += _str.replace(">", ">=").replace("<", "<=").replace(">==", ">=").replace("<==", "<=").replace(
                    "**", "^")
            t_str += "}\n"

            # reset
            t_str += "reset {\n"
            for le, ri in transition.reset:
                assert isinstance(le, Variable)
                _str = "{}\' := {}\n".format(le, obj2fs(ri))
                t_str += _str.replace("**", "^").replace("True", "")
            t_str += "}\n"

            t_str += "parallelotope aggregation { }\n"
            trans_str_list.append(t_str)

        trans_str = "jumps {{\n {} \n }}\n".format("\n".join(trans_str_list))

        var_set = get_ha_vars(ha)

        bound_box = ha.get_bound_box()
        initial_modes = set(filter(lambda x: x.is_initial(), ha.get_modes()))
        final_modes = set(filter(lambda x: x.is_final(), ha.get_modes()))

        init_cond_str = ""
        for variable in var_set:
            assert variable in bound_box
            bb = bound_box[variable]
            init_cond_str += "{} in [{}, {}]\n".format(variable, bb.left, bb.right)

        init_child_str = ""
        assert len(initial_modes) == 1
        for start_mode in initial_modes:
            init_child_str += "mode_{} {{".format(start_mode.id)
            init_child_str += init_cond_str
            init_child_str += "}"

        init_str = "init {{\n {}\n}}\n".format(init_child_str)

        unsafe_str = ""
        terminal_modes_str = list()
        for final_mode in final_modes:
            terminal_modes_str.append("mode_{}".format(final_mode.id))

        for m in ha.get_modes():
            real_name = "mode_{}".format(m.id)
            if real_name in terminal_modes_str:
                unsafe_str += "{}{{}}\n".format(real_name)
            else:
                unsafe_str += "{}{{ ff <= 0 }}\n".format(real_name)

        var_str = "state var {}".format(", ".join(map(lambda x: str(x), var_set)))
        assert len(var_set) > 0
        picked = var_set.pop()

        common_section = self.config.get_section("common")
        time_horizon = common_section.get_value("time-horizon")
        bound = common_section.get_value("bound")

        # config
        net_dict = dict()
        net_dict["adaptive steps"] = "{min 0.001, max 0.5}"
        net_dict["time"] = time_horizon
        net_dict["remainder estimation"] = "1e-8"
        net_dict["identity precondition"] = ""
        net_dict["gnuplot octagon"] = "{},{} fixed orders 8".format(picked, picked)
        net_dict["cutoff"] = "1e-13"
        net_dict["precision"] = "53"
        net_dict["no output"] = ""
        net_dict["max jumps"] = bound
        net_dict["print on"] = ""

        conf_str_list = list()
        for k in net_dict:
            conf_str_list.append("{} {}".format(k, net_dict[k]))

        setting_str = "setting {{\n {} \n}}\n".format("\n".join(conf_str_list))

        self._string = "hybrid reachability {{\n {}\n {}\n {}\n {}\n {}\n}}\n unsafe {{\n {} \n }}\n".format(
            var_str,
            setting_str,
            modes_str,
            trans_str,
            init_str,
            unsafe_str)

    def write(self, file_name: str):
        common_section = self.config.get_section("common")
        g_n, b = common_section.get_value("goal"), common_section.get_value("bound")

        fs_n = "{}_{}_b{}_fs.model".format(file_name, g_n, b)
        f = open(fs_n, "w")
        f.write(self._string)
        f.close()
        print("write hybrid automaton to {}".format(fs_n))

    def _reset(self):
        self._string = ""


def preprocessing(ha: HybridAutomaton):
    ff = Real("ff")
    zero, one = RealVal("0.0"), RealVal("1.0")
    g_clk = Real("gClk")

    # add initial conditions for special variables: ff = 1
    ha.add_init(ff == one, g_clk == zero)

    for mode in ha.get_modes():
        mode.add_dynamic((ff, zero))
        mode.add_invariant(ff > zero)

    initials = set()
    for mode in ha.get_modes():
        if mode.is_initial():
            initials.add(mode)
            mode.set_as_non_initial()

    initial_mode = Mode(0)
    initial_mode.set_as_initial()
    initial_mode.add_invariant(g_clk <= zero)

    v_s = get_ha_vars(ha)
    v_s.discard(g_clk)
    for v in v_s:
        initial_mode.add_dynamic((v, zero))

    initial_mode.add_dynamic((g_clk, one))
    ha.add_mode(initial_mode)

    for mode in initials:
        tr = Transition(initial_mode, mode)
        tr.add_guard(g_clk >= zero)
        ha.add_transition(tr)

    remove_equal_jumps(ha)


@singledispatch
def obj2fs(const: Union[Formula, Expr]):
    raise Exception("fail to translate to flowstar object ({})".format(const))


@obj2fs.register(Variable)
def _(const: Variable):
    return const.id


@obj2fs.register(Constant)
def _(const: Constant):
    return const.value


@obj2fs.register(And)
def _(const: And):
    return '\n'.join([obj2fs(c) for c in const.children])


@obj2fs.register(Geq)
def _(const: Geq):
    return obj2fs(const.left - const.right) + " >= 0.0"


@obj2fs.register(Gt)
def _(const: Gt):
    return obj2fs(const.left - const.right) + " >= 0.0"


@obj2fs.register(Leq)
def _(const: Leq):
    return obj2fs(const.left - const.right) + " <= 0.0"


@obj2fs.register(Lt)
def _(const: Geq):
    return obj2fs(const.left - const.right) + " <= 0.0"


@obj2fs.register(Eq)
def _(const: Eq):
    return "{} - {} = 0.0".format(obj2fs(const.left), obj2fs(const.right))


# cannot support this
@obj2fs.register(Neq)
def _(const: Geq):
    c1 = obj2fs(const.left - const.right) + " >= 0.0"
    c2 = obj2fs(const.left - const.right) + " <= 0.0"
    return c1 + "\n" + c2


@obj2fs.register(Add)
def _(const: Add):
    return "(" + obj2fs(const.left) + " + " + obj2fs(const.right) + ")"


@obj2fs.register(Sub)
def _(const: Sub):
    return "(" + obj2fs(const.left) + " - " + obj2fs(const.right) + ")"


@obj2fs.register(Neg)
def _(const: Neg):
    return "(-" + obj2fs(const.child) + ")"


@obj2fs.register(Mul)
def _(const: Mul):
    return "(" + obj2fs(const.left) + " * " + obj2fs(const.right) + ")"


@obj2fs.register(Div)
def _(const: Div):
    return "(" + obj2fs(const.left) + " / " + obj2fs(const.right) + ")"


# maybe not supported
@obj2fs.register(Pow)
def _(const: Pow):
    return "(" + obj2fs(const.left) + " ** " + obj2fs(const.right) + ")"


@obj2fs.register(Forall)
def _(const: Forall):
    return obj2fs(const.const)
