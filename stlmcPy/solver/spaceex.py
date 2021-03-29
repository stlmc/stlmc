from functools import singledispatch
from typing import Dict, List

from spaceex.core import SpaceEx
from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import substitution, reduce_not, get_vars, infix
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.hybrid_automaton.converter import AbstractConverter
from stlmcPy.hybrid_automaton.hybrid_automaton import HybridAutomaton
from stlmcPy.hybrid_automaton.utils import vars_in_ha
from stlmcPy.solver.assignment import Assignment
from stlmcPy.solver.ode_solver import CommonOdeSolver, NaiveStrategyManager, ReductionStrategyManager, \
    UnsatCoreStrategyManager, NormalSolvingStrategy
from stlmcPy.solver.ode_utils import remove_index
from stlmcPy.solver.strategy import unit_split


class SpaceExConverter(AbstractConverter):
    def solve(self):
        spaceex_core_solver = SpaceEx()
        assert len(self.convert_result) == 2
        spaceex_core_solver.run(self.convert_result[0], self.convert_result[1])
        solving_time = spaceex_core_solver.logger.get_duration_time("solving timer")
        if spaceex_core_solver.result:
            return False, solving_time
        else:
            return True, solving_time

    def preprocessing(self, ha: HybridAutomaton):
        pass

    def convert(self, ha: HybridAutomaton, setting: Dict, variable_ordering: List, bound_box: List):
        def _make_conf_dict(_setting: Dict):
            _dict = dict()
            keywords = ["time-horizon", "iter-max", "sampling-time", "rel-err", "abs-err"]
            for keyword in keywords:
                if keyword in _setting:
                    _dict[keyword] = _setting[keyword]
            return _dict

        def _make_init_string(_variable_ordering: List, _bound_box: List):
            _const_set = set()
            for _var_index, _var in enumerate(_variable_ordering):
                _lower = Geq(_var, _bound_box[_var_index][0])
                _upper = Leq(_var, _bound_box[_var_index][1])

                _const_set.add(_lower)
                _const_set.add(_upper)

            _const_str_list = list()
            for _const in _const_set:
                _const_str_list.append(infix(_const))

            return "&".join(_const_str_list)

        print(ha)
        # set variable declaration string
        var_set = vars_in_ha(ha)

        var_str_list = list()
        map_str_list = list()
        for _var in var_set:
            var_str_list.append(
                "\t\t<param name=\"{}\" type=\"{}\" local=\"false\" "
                "d1=\"1\" d2=\"1\" dynamics=\"any\" />\n".format(_var.id, _var.type)
            )

            map_str_list.append(
                "<map key=\"{}\">{}</map>\n".format(_var.id, _var.id)
            )

        mode_str_list = list()
        for mode in ha.modes:
            loc_str_begin = "<location id=\"{}\" name=\"{}__id_{}\" x=\"100\" y=\"100\" " \
                            "width=\"50\" height=\"50\">\n".format(id(mode), mode.name, id(mode))

            # flows
            flow_str_list = list()
            for (var, exp) in mode.dynamics:
                flow_str_list.append("{}\' == {}".format(var, spaceExinfix(exp)))
            flow_str = "<flow>{}</flow>".format("&amp;".join(flow_str_list))

            # invs
            inv_str_list = list()
            for inv in mode.invariant:
                inv_str_list.append(spaceExinfix(inv))
            inv_str = "<invariant>{}</invariant>".format("&amp;".join(inv_str_list))

            loc_str_end = "</location>\n"

            mode_str_list.append(loc_str_begin + inv_str + flow_str + loc_str_end)

        trans_label_str_list = list()
        trans_str_list = list()
        for transition in ha.transitions:
            trans_label_str_list.append(
                "\t\t<param name=\"{}\" type=\"label\" local=\"true\" />".format(transition.name)
            )

            t_str_begin = "<transition source=\"{}\" target=\"{}\">\n".format(id(transition.src),
                                                                              id(transition.trg))
            t_label = "<label>{}</label>\n".format(transition.name)
            t_label_position = "<labelposition x=\"200\" y=\"200\" width=\"20\" height=\"10\"/>\n"

            # guard
            guard_str_list = list()
            for guard in transition.guard:
                guard_str_list.append(spaceExinfix(guard))
            guard_str = "<guard>{}</guard>\n".format("&amp;".join(guard_str_list))

            # reset
            reset_str_list = list()
            for reset in transition.reset:
                reset_str_list.append(spaceExinfixReset(reset))
            reset_str = "<assignment>{}</assignment>\n".format("&amp;".join(reset_str_list))

            t_str_end = "</transition>\n"
            trans_str_list.append(t_str_begin + t_label + guard_str + reset_str + t_label_position + t_str_end)

        # trans_str = ""
        # for i, t in enumerate(ha.trans):
        #     t_str_begin = "<transition source=\"{}\" target=\"{}\">\n".format(mode_map[ha.trans[t].src.name],
        #                                                                       mode_map[ha.trans[t].trg.name])
        #     t_label = "<label>{}</label>\n".format(t)
        #     t_label_position = "<labelposition x=\"{}\" y=\"200\" width=\"{}\" height=\"{}\"/>\n".format(50 * i, 50, 50)
        #     guard_str = ""
        #     if ha.trans[t].guard is not None:
        #         guard_str = "<guard>{}</guard>\n".format(spaceExinfix(ha.trans[t].guard))
        #     reset_str = ""
        #     if ha.trans[t].reset is not None:
        #         reset_str = "<assignment>{}</assignment>\n".format(spaceExinfixReset(ha.trans[t].reset))
        #     t_str_end = "</transition>\n"
        #     trans_str += t_str_begin + t_label + guard_str + reset_str + t_label_position + t_str_end

        hybrid_automaton_component = '''<component id=\"{}\">
        {}{}{}{}
        </component>
        '''.format(ha.name, "\n".join(var_str_list), "\n".join(trans_label_str_list), "\n".join(mode_str_list), "\n".join(trans_str_list))

        # map_str = ""
        # for v_name in vars:
        #     map_str += "<map key=\"{}\">{}</map>\n".format(v_name, v_name)


        # conf_dict = dict()
        # conf_dict["system"] = "\"system\""
        # conf_dict["initially"] = "\"{}\"".format(infix(And(init_children)))
        # conf_dict["scenario"] = "\"supp\""
        # conf_dict["directions"] = "\"uni32\""
        # conf_dict["sampling-time"] = "0.1"
        # conf_dict["time-horizon"] = "100"
        # conf_dict["iter-max"] = "10"
        # conf_dict["output-variables"] = "\"{}\"".format(out_var_str)
        # conf_dict["output-format"] = "\"TXT\""
        # conf_dict["rel-err"] = "1.0e-12"
        # conf_dict["abs-err"] = "1.0e-13"

        system_component = '''<component id=\"system\">
        {}
        <bind component=\"{}\" as=\"{}_system\" x=\"300\" y=\"200\">
        {}
        </bind>
        </component>
        '''.format("\n".join(var_str_list), ha.name, ha.name, "\n".join(map_str_list))

        model_string = '''<?xml version="1.0" encoding="UTF-8"?>
<sspaceex xmlns="http://www-verimag.imag.fr/xml-namespaces/sspaceex" version="0.2" math="SpaceEx"> 
{}
{}
</sspaceex>
        '''.format(hybrid_automaton_component, system_component)

        assert len(variable_ordering) > 1
        init_str = _make_init_string(variable_ordering, bound_box)

        net_dict = _make_conf_dict(setting)
        net_dict["system"] = "\"system\""
        net_dict["initially"] = "\"{}\"".format(init_str)
        net_dict["scenario"] = "\"supp\""
        net_dict["directions"] = "\"uni32\""
        net_dict["output-variables"] = "\"{}, {}\"".format(variable_ordering[0], variable_ordering[0])
        net_dict["output-format"] = "\"TXT\""

        conf_str_list = list()
        for k in net_dict:
            conf_str_list.append("{} = {}".format(k, net_dict[k]))

        conf_string = "\n".join(conf_str_list)

        #
        self.convert_result = [model_string, conf_string]


class SpaceExSolverNaive(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, NaiveStrategyManager())

    def make_assignment(self):
        pass

    def clear(self):
        pass


class SpaceExSolverReduction(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, ReductionStrategyManager())

    def make_assignment(self):
        pass

    def clear(self):
        pass


class SpaceExSolverUnsatCore(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager(), NormalSolvingStrategy(SpaceExConverter()))

    def make_assignment(self):
        pass

    def clear(self):
        pass


class SpaceExAssignment(Assignment):
    def __init__(self, spaceex_counterexample):
        self.spaceex_counterexample = spaceex_counterexample

    def get_assignments(self):
        print(self.spaceex_counterexample)

    def eval(self, const):
        pass


@singledispatch
def spaceExinfix(const: Constraint):
    return str(const)


@spaceExinfix.register(Variable)
def _(const: Variable):
    return const.id


@spaceExinfix.register(And)
def _(const: And):
    return '&amp;'.join([spaceExinfix(c) for c in const.children])


@spaceExinfix.register(Geq)
def _(const: Geq):
    return spaceExinfix(const.left) + " &gt;= " + spaceExinfix(const.right)


@spaceExinfix.register(Gt)
def _(const: Geq):
    return spaceExinfix(const.left) + " &gt; " + spaceExinfix(const.right)


@spaceExinfix.register(Leq)
def _(const: Geq):
    return spaceExinfix(const.left) + " &lt;= " + spaceExinfix(const.right)


@spaceExinfix.register(Lt)
def _(const: Geq):
    return spaceExinfix(const.left) + " &lt; " + spaceExinfix(const.right)


@spaceExinfix.register(Eq)
def _(const: Eq):
    return spaceExinfix(const.left) + " == " + spaceExinfix(const.right)


# cannot support this
@spaceExinfix.register(Neq)
def _(const: Geq):
    return spaceExinfix(const.left) + " &gt;= " + spaceExinfix(const.right) + " &amp; " + spaceExinfix(
        const.left) + " &lt; " + spaceExinfix(
        const.right)


@spaceExinfix.register(Add)
def _(const: Add):
    return "(" + spaceExinfix(const.left) + " + " + spaceExinfix(const.right) + ")"


@spaceExinfix.register(Sub)
def _(const: Sub):
    return "(" + spaceExinfix(const.left) + " - " + spaceExinfix(const.right) + ")"


@spaceExinfix.register(Neg)
def _(const: Neg):
    return "(-" + spaceExinfix(const.child) + ")"


@spaceExinfix.register(Mul)
def _(const: Mul):
    return "(" + spaceExinfix(const.left) + " * " + spaceExinfix(const.right) + ")"


@spaceExinfix.register(Div)
def _(const: Div):
    return "(" + spaceExinfix(const.left) + " / " + spaceExinfix(const.right) + ")"


# maybe not supported
@spaceExinfix.register(Pow)
def _(const: Pow):
    return "(" + spaceExinfix(const.left) + " ** " + spaceExinfix(const.right) + ")"


@spaceExinfix.register(Forall)
def _(const: Forall):
    return spaceExinfix(const.const)


### start


@singledispatch
def spaceExinfixReset(const: Constraint):
    return str(const)


@spaceExinfixReset.register(Variable)
def _(const: Variable):
    return const.id


@spaceExinfixReset.register(And)
def _(const: And):
    return '&amp;'.join([spaceExinfixReset(c) for c in const.children])


@spaceExinfixReset.register(Geq)
def _(const: Geq):
    return spaceExinfixReset(const.left) + " &gt;= " + spaceExinfixReset(const.right)


@spaceExinfixReset.register(Gt)
def _(const: Geq):
    return spaceExinfixReset(const.left) + " &gt; " + spaceExinfixReset(const.right)


@spaceExinfixReset.register(Leq)
def _(const: Geq):
    return spaceExinfixReset(const.left) + " &lt;= " + spaceExinfixReset(const.right)


@spaceExinfixReset.register(Lt)
def _(const: Geq):
    return spaceExinfixReset(const.left) + " &lt; " + spaceExinfixReset(const.right)


@spaceExinfixReset.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Real):
        return "{}\' == {}".format(const.left.id, spaceExinfixReset(const.right))
    elif isinstance(const.left, Int):
        return "{}\' == {}".format(const.left.id, spaceExinfixReset(const.right))
    else:
        raise NotSupportedError()


# cannot support this
@spaceExinfixReset.register(Neq)
def _(const: Geq):
    return spaceExinfixReset(const.left) + " &gt;= " + spaceExinfixReset(const.right) + " &amp; " + spaceExinfixReset(
        const.left) + " &lt; " + spaceExinfixReset(
        const.right)


@spaceExinfixReset.register(Add)
def _(const: Add):
    return "(" + spaceExinfixReset(const.left) + " + " + spaceExinfixReset(const.right) + ")"


@spaceExinfixReset.register(Sub)
def _(const: Sub):
    return "(" + spaceExinfixReset(const.left) + " - " + spaceExinfixReset(const.right) + ")"


@spaceExinfixReset.register(Neg)
def _(const: Neg):
    return "(-" + spaceExinfixReset(const.child) + ")"


@spaceExinfixReset.register(Mul)
def _(const: Mul):
    return "(" + spaceExinfixReset(const.left) + " * " + spaceExinfixReset(const.right) + ")"


@spaceExinfixReset.register(Div)
def _(const: Div):
    return "(" + spaceExinfixReset(const.left) + " / " + spaceExinfixReset(const.right) + ")"


# maybe not supported
@spaceExinfixReset.register(Pow)
def _(const: Pow):
    return "(" + spaceExinfixReset(const.left) + " ** " + spaceExinfixReset(const.right) + ")"


@spaceExinfixReset.register(Forall)
def _(const: Forall):
    return spaceExinfixReset(const.const)
