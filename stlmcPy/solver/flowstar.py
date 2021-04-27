from functools import singledispatch
from typing import *

from sympy import simplify, Equality

from flowstar.core import FlowStar
from stlmcPy.constraints.constraints import *
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.hybrid_automaton.converter import AbstractConverter
from stlmcPy.hybrid_automaton.hybrid_automaton import HybridAutomaton
from stlmcPy.hybrid_automaton.utils import calc_initial_terminal_modes, vars_in_ha
from stlmcPy.solver.assignment import Assignment
from stlmcPy.solver.ode_solver import CommonOdeSolver, NaiveStrategyManager, ReductionStrategyManager, \
    UnsatCoreStrategyManager, MergeSolvingStrategy, NormalSolvingStrategy
from stlmcPy.solver.ode_utils import expr_to_sympy, expr_to_sympy_inequality


class FlowStarConverter(AbstractConverter):
    def preprocessing(self, ha: HybridAutomaton):
        initial_modes, _ = calc_initial_terminal_modes(ha)
        # add unique init mode
        start_mode = ha.new_mode("start")

        for init_mode in initial_modes:
            ha.new_transition("start_2_{}__id_{}".format(init_mode.name, id(init_mode)), start_mode, init_mode)

        ff = Real("ff")
        zero = RealVal("0")

        # ff > 0
        ff_inv = Gt(ff, zero)

        for mode in ha.modes:
            mode.set_dynamic(ff, zero)
            mode.set_invariant(ff_inv)

    def solve(self):
        flowstar_core_solver = FlowStar()
        flowstar_core_solver.run(self.convert_result)
        solving_time = flowstar_core_solver.logger.get_duration_time("solving timer")
        if flowstar_core_solver.result:
            return False, solving_time
        else:
            return True, solving_time

    def convert(self, ha: HybridAutomaton, setting: Dict, lv: List, bound_box: List):
        def _make_conf_dict(_setting: dict, _lv):
            _setting["gnuplot octagon"] = "{}, {}".format(_lv[0], _lv[1])
            # conf_dict = dict()
            # conf_dict["fixed steps"] = "0.01"
            # # conf_dict["initially"] = "\"{}\"".format(infix(And(init_children)))
            # conf_dict["time"] = "1"
            # conf_dict["remainder estimation"] = "1e-2"
            # conf_dict["identity precondition"] = ""
            # conf_dict["gnuplot octagon"] = ""
            # conf_dict["adaptive orders"] = "{ min 4 , max 8 }"
            # conf_dict["cutoff"] = "1e-12"
            # conf_dict["precision"] = "53"
            # conf_dict["no output"] = ""
            # conf_dict["max jumps"] = "10"
            _dict = dict()
            keywords = ["fixed steps", "time", "remainder estimation", "identity precondition",
                        "gnuplot octagon", "adaptive orders", "cutoff", "precision", "no output", "max jumps"]
            for keyword in keywords:
                if keyword in _setting:
                    _dict[keyword] = _setting[keyword]
            return _dict

        self.preprocessing(ha)
        initial_modes, terminal_modes = calc_initial_terminal_modes(ha)

        modes_str_list = list()
        for mode in ha.modes:
            mode_str = "{}__id_{}{{\n".format(mode.name, id(mode))
            mode_str += "poly ode 1\n{"

            for (var, exp) in mode.dynamics:
                mode_str += "{}\' = {}\n".format(var, str(simplify(expr_to_sympy(exp)))).replace("**", "^")
            mode_str += "}\n"

            mode_str += "inv {\n"
            for inv in mode.invariant:
                mode_str += "{}\n".format(expr_to_sympy_inequality(inv)).replace(">", ">=").replace("<",
                                                                                                    "<=").replace(
                    ">==", ">=").replace("<==", "<=").replace("**", "^")
            mode_str += "}\n}"
            modes_str_list.append(mode_str)

        modes_str = "modes {{\n {}\n}}\n".format("\n".join(modes_str_list))

        var_set = vars_in_ha(ha)
        var_str = "state var "
        for i, v in enumerate(var_set):
            if i == len(var_set) - 1:
                var_str += v.id
            else:
                var_str += v.id + ", "

        setting_child_str = ""

        setting_ordering = ["fixed steps", "time", "remainder estimation", "identity precondition", "gnuplot octagon",
                            "adaptive orders", "cutoff", "precision", "no output", "max jumps"]

        flowstar_setting = _make_conf_dict(setting, lv)

        for k in setting_ordering:
            assert k in flowstar_setting
            setting_child_str += "{} {}\n".format(k, flowstar_setting[k])
        setting_str = "setting {{\n {} print on \n}}\n".format(setting_child_str)

        trans_str_list = list()
        for transition in ha.transitions:
            t_str = "{}__id_{} -> {}__id_{}\n".format(transition.src.name,
                                                      id(transition.src),
                                                      transition.trg.name,
                                                      id(transition.trg))

            t_str += "guard {\n"
            for guard in transition.guard:
                simplified_guard = expr_to_sympy_inequality(guard)
                _str = ""
                if isinstance(simplified_guard, Equality):
                    _str = "{} = {}\n".format(simplified_guard.lhs, simplified_guard.rhs)
                else:
                    _str = "{}\n".format(simplified_guard)
                t_str += _str.replace(">", ">=").replace("<", "<=").replace(">==", ">=").replace("<==", "<=").replace("**", "^")
            t_str += "}\n"

            # reset
            t_str += "reset {\n"
            for reset in transition.reset:
                t_str += "{}\n".format(flowStarinfixReset(reset))
            t_str += "}\n"

            t_str += "parallelotope aggregation { }\n"
            trans_str_list.append(t_str)
            #         whole_r_str = flowStarinfixReset(t.reset)
            #         for r_str in whole_r_str.split("&"):
            #             t_str += "{}\n".format(r_str)
            #         t_str += "}\n"
        # for i, t in enumerate(ha.transitions):
        #     t_str = "{}__id_{} -> {}__id_{}\n".format(t.src.name, id(t.src), t.trg.name, id(t.trg))
        #     guard = t.guard
        #     if guard is not None:
        #         t_str += "guard {\n"
        #         if isinstance(guard, And):
        #             for g in guard.children:
        #                 etsi = expr_to_sympy_inequality(g)
        #                 etsi_str = "{}".format(etsi)
        #                 if isinstance(etsi, Equality):
        #                     etsi_str = "{} = {}".format(etsi.lhs, etsi.rhs)
        #                 t_str += "{}\n".format(etsi_str).replace(">", ">=").replace("<",
        #                                                                             "<=").replace(
        #                     ">==", ">=").replace("<==", "<=").replace("**", "^")
        #         else:
        #             etsi = expr_to_sympy_inequality(guard)
        #             etsi_str = "{}".format(etsi)
        #             if isinstance(etsi, Equality):
        #                 etsi_str = "{} = {}".format(etsi.lhs, etsi.rhs)
        #             t_str += "{}\n".format(etsi_str).replace(">", ">=").replace("<",
        #                                                                         "<=").replace(
        #                 ">==", ">=").replace("<==", "<=").replace("**", "^")
        #         # whole_g_str = infix(ha.trans[t].guard)
        #         # for g_str in whole_g_str.split("&"):
        #         #     t_str += "{}\n".format(g_str)
        #         t_str += "}\n"
        #     else:
        #         t_str += "guard {}"
        #
        #     if t.reset is not None:
        #         t_str += "reset {\n"
        #         whole_r_str = flowStarinfixReset(t.reset)
        #         for r_str in whole_r_str.split("&"):
        #             t_str += "{}\n".format(r_str)
        #         t_str += "}\n"
        #     else:
        #         t_str += "reset {}"
        #     t_str += "parallelotope aggregation { }\n"
        #     trans_str_list.append(t_str)

        trans_str = "jumps {{\n {} \n }}\n".format("\n".join(trans_str_list))

        init_child_str = ""
        for start_mode in initial_modes:
            init_child_str += "{}__id_{} {{".format(start_mode.name, id(start_mode))
            for iv, v in enumerate(lv):
                init_child_str += "{} in [{}, {}]\n".format(v, bound_box[iv][0], bound_box[iv][1])
            init_child_str += " ff in [1.0, 1.0]}\n"

        init_str = "init {{\n {}\n}}\n".format(init_child_str)
        # for iv, v in enumerate(self.var_list_ordering):
        #     init_str += "{} in [{}, {}]\n".format(v, self.init_bound[iv][0], self.init_bound[iv][1])
        # init_str += " ff in [2.0, 2.0]}\n}\n"

        unsafe_str = ""

        terminal_modes_str = list()
        for m in terminal_modes:
            terminal_modes_str.append("{}__id_{}".format(m.name, id(m)))

        # print(terminal_modes_str)
        for m in ha.modes:
            real_name = "{}__id_{}".format(m.name, id(m))
            if real_name in terminal_modes_str:
                unsafe_str += "{}{{}}\n".format(real_name)
            else:
                unsafe_str += "{}{{ ff  <= 0 }}\n".format(real_name)

        self.convert_result = "hybrid reachability {{\n {}\n {}\n {}\n {}\n {}\n}}\n unsafe {{\n {} \n }}\n".format(
            var_str,
            setting_str,
            modes_str,
            trans_str,
            init_str,
            unsafe_str)


class FlowStarSolverNaive(CommonOdeSolver):
    def __init__(self):
        assert "merging_strategy" in self.conf_dict
        underlying_solver = NormalSolvingStrategy(flowstar_solver)
        if self.conf_dict["merging_strategy"]:
            underlying_solver = MergeSolvingStrategy(flowstar_merging_solver)
        CommonOdeSolver.__init__(self, NaiveStrategyManager(), underlying_solver)

    def make_assignment(self):
        pass

    def clear(self):
        pass


class FlowStarSolverReduction(CommonOdeSolver):
    def __init__(self):
        assert "merging_strategy" in self.conf_dict
        underlying_solver = NormalSolvingStrategy(flowstar_solver)
        if self.conf_dict["merging_strategy"]:
            underlying_solver = MergeSolvingStrategy(flowstar_merging_solver)
        CommonOdeSolver.__init__(self, ReductionStrategyManager(), underlying_solver)

    def make_assignment(self):
        pass

    def clear(self):
        pass


class FlowStarSolverUnsatCoreMerging(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager(), MergeSolvingStrategy(FlowStarConverter()))

    def clear(self):
        self.strategy_manager.clear()


class FlowStarSolverUnsatCore(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager(), NormalSolvingStrategy(FlowStarConverter()))

    def clear(self):
        self.strategy_manager.clear()


class FlowStarAssignment(Assignment):
    def __init__(self, flowstar_counterexample):
        self.counterexample = flowstar_counterexample

    def get_assignments(self):
        print(self.counterexample)

    def eval(self, const):
        pass


@singledispatch
def flowStarinfixReset(const: Constraint):
    return str(const)


@flowStarinfixReset.register(Variable)
def _(const: Variable):
    return const.id


@flowStarinfixReset.register(And)
def _(const: And):
    return '&'.join([flowStarinfixReset(c) for c in const.children])


@flowStarinfixReset.register(Geq)
def _(const: Geq):
    return flowStarinfixReset(const.left) + " >= " + flowStarinfixReset(const.right)


@flowStarinfixReset.register(Gt)
def _(const: Gt):
    return flowStarinfixReset(const.left) + " >= " + flowStarinfixReset(const.right)


@flowStarinfixReset.register(Leq)
def _(const: Leq):
    return flowStarinfixReset(const.left) + " <= " + flowStarinfixReset(const.right)


@flowStarinfixReset.register(Lt)
def _(const: Geq):
    return flowStarinfixReset(const.left) + " <= " + flowStarinfixReset(const.right)


@flowStarinfixReset.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Real):
        return "{}\' := {}".format(const.left.id, flowStarinfixReset(const.right))
    elif isinstance(const.left, Int):
        return "{}\' := {}".format(const.left.id, flowStarinfixReset(const.right))
    else:
        raise NotSupportedError()


# cannot support this
@flowStarinfixReset.register(Neq)
def _(const: Geq):
    return flowStarinfixReset(const.left) + " >= " + flowStarinfixReset(const.right) + " & " + flowStarinfixReset(
        const.left) + " <= " + flowStarinfixReset(
        const.right)


@flowStarinfixReset.register(Add)
def _(const: Add):
    return "(" + flowStarinfixReset(const.left) + " + " + flowStarinfixReset(const.right) + ")"


@flowStarinfixReset.register(Sub)
def _(const: Sub):
    return "(" + flowStarinfixReset(const.left) + " - " + flowStarinfixReset(const.right) + ")"


@flowStarinfixReset.register(Neg)
def _(const: Neg):
    return "(-" + flowStarinfixReset(const.child) + ")"


@flowStarinfixReset.register(Mul)
def _(const: Mul):
    return "(" + flowStarinfixReset(const.left) + " * " + flowStarinfixReset(const.right) + ")"


@flowStarinfixReset.register(Div)
def _(const: Div):
    return "(" + flowStarinfixReset(const.left) + " / " + flowStarinfixReset(const.right) + ")"


# maybe not supported
@flowStarinfixReset.register(Pow)
def _(const: Pow):
    return "(" + flowStarinfixReset(const.left) + " ** " + flowStarinfixReset(const.right) + ")"


@flowStarinfixReset.register(Forall)
def _(const: Forall):
    return flowStarinfixReset(const.const)
