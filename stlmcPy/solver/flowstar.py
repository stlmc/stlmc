import abc
import copy
from abc import ABC
from functools import singledispatch
from itertools import product

from sympy import symbols, simplify, StrictGreaterThan, GreaterThan, LessThan, StrictLessThan, Symbol, Float, Equality, \
    Unequality
from sympy.core import relational

from flowstar.core import FlowStar
from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import substitution, reduce_not, get_vars, infix, clause
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.hybrid_automaton.abstract_converter import AbstractConverter
from stlmcPy.hybrid_automaton.hybrid_automaton import HybridAutomaton
from stlmcPy.hybrid_automaton.utils import merge, calc_initial_terminal_modes, new_merge
from stlmcPy.solver.abstract_solver import BaseSolver, OdeSolver
from stlmcPy.solver.assignment import Assignment
from stlmcPy.solver.ode_solver import CommonOdeSolver, NaiveStrategyManager, ReductionStrategyManager, \
    UnsatCoreStrategyManager, MergeSolvingStrategy, NormalSolvingStrategy
from stlmcPy.solver.ode_utils import remove_index, expr_to_sympy, get_vars_from_set, expr_to_sympy_inequality, \
    find_index
from stlmcPy.solver.strategy import UnsatCoreBuilder, unit_split
from stlmcPy.solver.z3 import Z3Solver
from stlmcPy.tree.operations import size_of_tree
from stlmcPy.util.logger import Logger
from stlmcPy.util.print import Printer


class FlowStarConverter(AbstractConverter):
    def __init__(self, setting: dict, lv: list, init_bound):
        self.var_set = set()
        self.setting = setting

        self.var_list_ordering = lv
        self.init_bound = init_bound

        self.setting["gnuplot octagon"] = "{}, {}".format(lv[0], lv[1])

    def set_logic(self, logic_name: str):
        pass

    def infix(self, const: Constraint):
        pass

    def infix_reset(self, const: Constraint):
        pass

    def convert(self, ha: HybridAutomaton):
        mode_map = dict()
        # for mode
        vars = dict()
        vars_dyn = dict()

        # for dynamics, key: old variable, value: new variable
        vars_old_new_map = dict()

        modes_str_list = list()

        initial_modes, terminal_modes = calc_initial_terminal_modes(ha)

        # make flag variable for unsafe set
        self.var_set.add(Real("ff"))
        # get all variables and specify their types
        for m in ha.modes:
            put_var = set()
            mode_str = "{}__id_{}{{\n".format(m.name, id(m))
            mode_str += "poly ode 1\n{"
            if m.dynamics is not None:
                for i, v in enumerate(m.dynamics.vars):
                    newv = remove_index(v)
                    vars_old_new_map[v] = newv
                    self.var_set.add(newv)
                    # do we need do check this?
                    if isinstance(m.dynamics.exps[i], RealVal):
                        vars[newv] = "const"
                    else:
                        vars[newv] = "any"

                    e = m.dynamics.exps[i]
                    e_var_set = get_vars(e)
                    subst_dict = dict()
                    for e_var in e_var_set:
                        e_var_wo_index = remove_index(e_var)
                        subst_dict[e_var] = e_var_wo_index
                        self.var_set.add(e_var_wo_index)
                    if newv not in put_var:
                        put_var.add(newv)
                        # vars_dyn[newv] = infix(substitution(e, subst_dict))
                        mode_str += "{}\' = {}\n".format(newv,
                                                         str(simplify(
                                                             expr_to_sympy(substitution(e, subst_dict)))).replace(
                                                             "**", "^"))
            mode_str += "}\n"

            mode_str += "inv {\n"
            if m.invariant is not None:
                inv = m.invariant
                if isinstance(inv, And):
                    for ee in m.invariant.children:
                        # ets = expr_to_sympy(ee)
                        mode_str += "{}\n".format(expr_to_sympy_inequality(ee)).replace(">", ">=").replace("<",
                                                                                                           "<=").replace(
                            ">==", ">=").replace("<==", "<=").replace("**", "^")
                else:
                    mode_str += "{}\n".format(expr_to_sympy_inequality(inv)).replace(">", ">=").replace("<",
                                                                                                        "<=").replace(
                        ">==", ">=").replace("<==", "<=").replace("**", "^")

                # for inv in whole_inv_str.split("&"):
                #     mode_str += "{}\n".format(str(simplify(expr_to_sympy(inv))))
            mode_str += "\nff >= 1\n}\n"
            mode_str += "}"
            modes_str_list.append(mode_str)

        modes_str = "modes {{\n {}\n}}\n".format("\n".join(modes_str_list))

        var_str = "state var "
        for i, v in enumerate(self.var_set):
            if i == len(self.var_set) - 1:
                var_str += v.id
            else:
                var_str += v.id + ", "

        setting_child_str = ""

        setting_ordering = ["fixed steps", "time", "remainder estimation", "identity precondition", "gnuplot octagon",
                            "adaptive orders", "cutoff", "precision", "no output", "max jumps"]

        for k in setting_ordering:
            assert k in self.setting
            setting_child_str += "{} {}\n".format(k, self.setting[k])
        setting_str = "setting {{\n {} print on \n}}\n".format(setting_child_str)

        trans_str_list = list()
        for i, t in enumerate(ha.transitions):
            t_str = "{}__id_{} -> {}__id_{}\n".format(t.src.name, id(t.src), t.trg.name, id(t.trg))
            guard = t.guard
            if guard is not None:
                t_str += "guard {\n"
                if isinstance(guard, And):
                    for g in guard.children:
                        etsi = expr_to_sympy_inequality(g)
                        etsi_str = "".format(etsi)
                        if isinstance(etsi, Equality):
                            etsi_str = "{} = {}".format(etsi.lhs, etsi.rhs)
                        t_str += "{}\n".format(etsi_str).replace(">", ">=").replace("<",
                                                                                    "<=").replace(
                            ">==", ">=").replace("<==", "<=").replace("**", "^")
                else:
                    etsi = expr_to_sympy_inequality(guard)
                    etsi_str = "".format(etsi)
                    if isinstance(etsi, Equality):
                        etsi_str = "{} = {}".format(etsi.lhs, etsi.rhs)
                    t_str += "{}\n".format(etsi_str).replace(">", ">=").replace("<",
                                                                                "<=").replace(
                        ">==", ">=").replace("<==", "<=").replace("**", "^")
                # whole_g_str = infix(ha.trans[t].guard)
                # for g_str in whole_g_str.split("&"):
                #     t_str += "{}\n".format(g_str)
                t_str += "}\n"

            if t.reset is not None:
                t_str += "reset {\n"
                whole_r_str = flowStarinfixReset(t.reset)
                for r_str in whole_r_str.split("&"):
                    t_str += "{}\n".format(r_str)
                t_str += "}\n"
            t_str += "parallelotope aggregation { }\n"
            trans_str_list.append(t_str)

        trans_str = "jumps {{\n {} \n }}\n".format("\n".join(trans_str_list))

        init_child_str = ""
        for start_mode in initial_modes:
            init_child_str += "{}__id_{} {{".format(start_mode.name, id(start_mode))
            for iv, v in enumerate(self.var_list_ordering):
                init_child_str += "{} in [{}, {}]\n".format(v, self.init_bound[iv][0], self.init_bound[iv][1])
            init_child_str += " ff in [2.0, 2.0]}\n"

        init_str = "init {{\n {}\n}}\n".format(init_child_str)
        # for iv, v in enumerate(self.var_list_ordering):
        #     init_str += "{} in [{}, {}]\n".format(v, self.init_bound[iv][0], self.init_bound[iv][1])
        # init_str += " ff in [2.0, 2.0]}\n}\n"

        unsafe_str = ""

        terminal_modes_str = list()
        for m in terminal_modes:
            terminal_modes_str.append(m.name)

        # print(terminal_modes_str)
        for m in ha.modes:
            if m.name in terminal_modes_str:
                unsafe_str += "{}__id_{}".format(m.name, id(m)) + "{}\n"
            else:
                unsafe_str += "{}__id_{}".format(m.name, id(m)) + "{ ff  <= 0 }\n"

        return "hybrid reachability {{\n {}\n {}\n {}\n {}\n {}\n}}\n unsafe {{\n {} \n }}\n".format(var_str,
                                                                                                     setting_str,
                                                                                                     modes_str,
                                                                                                     trans_str,
                                                                                                     init_str,
                                                                                                     unsafe_str)

    @staticmethod
    def make_mode_property(s_integral_i, s_forall_i, i, max_bound, l_v, ha: HybridAutomaton, sigma):
        printer = Printer()
        mode_i = ha.new_mode("mode" + str(i))

        for integral in s_integral_i:
            if integral in sigma:
                dyns = sigma[integral].dynamics
                for j in range(1, i + 1):
                    dyns.vars.append(Real("tau_" + str(j)))
                    dyns.exps.append(RealVal("0"))

                for j in range(i + 1, max_bound + 2):
                    dyns.vars.append(Real("tau_" + str(j)))
                    dyns.exps.append(RealVal("1"))

                mode_i.set_dynamics(dyns)

        phi_forall_children = list()
        for c in s_forall_i:
            new_c = substitution(c, sigma)
            vs = get_vars(new_c)
            new_dict = dict()
            for v in vs:
                new_dict[v] = remove_index(v)
            phi_forall_children.append(reduce_not(substitution(new_c, new_dict)))

        if len(phi_forall_children) > 0:
            mode_i.set_invariant(And(phi_forall_children))
        return mode_i

    @staticmethod
    def make_transition(s_psi_abs_i, i, max_bound, ha: HybridAutomaton, mode_p, mode_n):
        trans_i = ha.new_transition("trans{}".format(i), mode_p, mode_n)
        s_forall_i, s_integral_i, s_0, s_tau_i, s_reset_i, s_guard_i = unit_split(s_psi_abs_i, i)
        # print ("reset {} ".format(s_reset_i))
        # print("guard {} ".format(s_reset_i))
        # print("tau {}".format(s_tau_i))
        guard_i_children = list(s_guard_i)
        tau_i_children = list(s_tau_i)
        total_children = list()

        total_children.extend(guard_i_children)
        total_children.extend(tau_i_children)

        phi_new_guard_children = list()
        for c in total_children:
            vs = get_vars(c)
            new_dict = dict()
            for v in vs:
                new_dict[v] = remove_index(v)
            phi_new_guard_children.append(reduce_not(substitution(c, new_dict)))

        trans_i.set_guard(And(phi_new_guard_children))

        # if "error" in mode_n.name:
        #     mode_n.set_invariant(And(phi_new_guard_children))

        phi_new_reset_children = list()
        for c in s_reset_i:
            vs = get_vars(c)
            new_dict = dict()
            for v in vs:
                new_dict[v] = remove_index(v)
            phi_new_reset_children.append(reduce_not(substitution(c, new_dict)))

        trans_i.set_reset(And(phi_new_reset_children))


def make_flowstar_conf_dict(conf_dict: dict):
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
    flowstar_dict = dict()
    keywords = ["fixed steps", "time", "remainder estimation", "identity precondition",
                "gnuplot octagon", "adaptive orders", "cutoff", "precision", "no output", "max jumps"]
    for keyword in keywords:
        if keyword in conf_dict:
            flowstar_dict[keyword] = conf_dict[keyword]
    return flowstar_dict


def flowstar_run(s_f_list, max_bound, sigma, conf_dict):
    new_s_f_list = list()
    printer = Printer()
    printer.print_debug("\n\ninput s_f_list : \n\n{}".format(s_f_list))
    num_internal = [0 for i in range(max_bound + 1)]

    for s in s_f_list:
        new_s = set()
        for c in s:
            if isinstance(c, Bool):
                if "newTau" in c.id:
                    index = c.id.rfind("_") + 1
                    num_internal[int(c.id[index:])] = num_internal[int(c.id[index:])] + 1
            new_s.add(substitution(c, sigma))
        new_s_f_list.append(new_s)

    sv = get_vars_from_set(new_s_f_list)

    l_v = list()
    for v in sv:
        new_v = remove_index(v)
        if new_v.id not in l_v:
            l_v.append(new_v.id)

    l_v = sorted(l_v)

    s_forall = list()
    s_integral = list()
    s_0 = list()
    s_tau = list()
    s_reset = list()
    s_guard = list()

    for i in range(max_bound + 1):
        s_forall_i, s_integral_i, s_0_i, s_tau_i, s_reset_i, s_guard_i = unit_split(s_f_list[i], i)
        s_forall.append(s_forall_i)
        s_integral.append(s_integral_i)
        s_0.append(s_0_i)
        s_tau.append(s_tau_i)
        s_reset.append(s_reset_i)
        s_guard.append(s_guard_i)

    ha = HybridAutomaton('ha')
    l_mode = list()

    for i in range(max_bound + 1):
        l_mode.append(FlowStarConverter.make_mode_property(s_integral[i], s_forall[i], i, max_bound, l_v, ha, sigma))

    l_mode.append(ha.new_mode("error"))

    for i in range(max_bound + 1):
        FlowStarConverter.make_transition(s_f_list[i], i, max_bound, ha, l_mode[i], l_mode[i + 1])

    forall_set, integral_set, init_set, tau_set, reset_set, guard_set = unit_split(s_f_list[0], max_bound)

    # assumption: all boundaries should be number
    sympy_expr_list = list()

    for cc in init_set:
        # if not isinstance(cc, Lt) or not isinstance(cc, Leq) or \
        #         not isinstance(cc, Gt) or not isinstance(cc, Geq) or \
        #         not isinstance(cc, Eq) or not isinstance(cc, Neq):
        sympy_expr_list.append(simplify(expr_to_sympy(reduce_not(cc))))

    bound_box_list = list()
    for i in range(len(l_v)):
        bound_box_list.append([None, None])

    for t in l_v:
        printer.print_debug("tau setting :\n{}".format(l_v))
        if ("tau" in t) or ("timeStep" in t):
            index = find_index(l_v, Real(t))
            printer.print_debug("{}, index => {}".format(t, index))
            bound_box_list[index][0] = Float(0.0)
            bound_box_list[index][1] = Float(0.0)

    printer.print_debug("\n\ninit constraints :")
    printer.print_debug("* variables : {}".format(l_v))
    for init_elem in init_set:
        printer.print_debug("  * {}".format(init_elem))

    for expr in sympy_expr_list:
        if isinstance(expr, GreaterThan) or isinstance(expr, StrictGreaterThan):
            # left is variable
            if expr.lhs.is_symbol:
                var_id = str(expr.lhs)
                index = find_index(l_v, Real(var_id))
                if bound_box_list[index][0] is None:
                    bound_box_list[index][0] = expr.rhs
                else:
                    if str(simplify(bound_box_list[index][0] <= expr.rhs)) == "True":
                        bound_box_list[index][0] = expr.rhs
            elif expr.rhs.is_symbol:
                var_id = str(expr.rhs)
                index = find_index(l_v, Real(var_id))
                if bound_box_list[index][1] is None:
                    bound_box_list[index][1] = expr.lhs
                else:
                    if str(simplify(bound_box_list[index][1] <= expr.lhs)) == "True":
                        bound_box_list[index][1] = expr.lhs

        elif isinstance(expr, LessThan) or isinstance(expr, StrictLessThan):
            # left is variable
            if expr.lhs.is_symbol:
                var_id = str(expr.lhs)
                index = find_index(l_v, Real(var_id))
                if bound_box_list[index][1] is None:
                    bound_box_list[index][1] = expr.rhs
                else:
                    if str(simplify(bound_box_list[index][1] >= expr.rhs)) == "True":
                        bound_box_list[index][1] = expr.rhs
            elif expr.rhs.is_symbol:
                var_id = str(expr.rhs)
                index = find_index(l_v, Real(var_id))
                if bound_box_list[index][0] is None:
                    bound_box_list[index][0] = expr.lhs
                else:
                    if str(simplify(bound_box_list[index][0] >= expr.lhs)) == "True":
                        bound_box_list[index][0] = expr.lhs
    new_bound_box_list = list()
    for e in bound_box_list:
        printer.print_debug("bound box list test : {}".format(e))
        bound_box_left = -float("inf")
        bound_box_right = float("inf")
        if e[0] is not None:
            bound_box_left = float(e[0])
        if e[1] is not None:
            bound_box_right = float(e[1])
        new_bound_box_list.append([bound_box_left, bound_box_right])

    # add affine variable
    printer.print_debug("* bound : ")
    printer.print_debug(new_bound_box_list)

    # mode = ha.modes['mode0']
    # print(l_v)
    # print(new_bound_box_list)

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
    # conf_dict["output"] = "stlmcflowstar"
    # conf_dict["max jumps"] = "10"

    fs = FlowStarConverter(conf_dict, l_v, new_bound_box_list)
    model_string = fs.convert(ha)
    flowStarRaw = FlowStar()
    flowStarRaw.run(model_string)
    solving_time = flowStarRaw.logger.get_duration_time("solving timer")
    if flowStarRaw.result:
        return False, solving_time
    else:
        return True, solving_time


def flowstar_gen(s_f_list, max_bound, sigma, conf_dict):
    new_s_f_list = list()
    printer = Printer()
    printer.print_debug("\n\ninput s_f_list : \n\n{}".format(s_f_list))
    num_internal = [0 for i in range(max_bound + 1)]

    for s in s_f_list:
        new_s = set()
        for c in s:
            if isinstance(c, Bool):
                if "newTau" in c.id:
                    index = c.id.rfind("_") + 1
                    num_internal[int(c.id[index:])] = num_internal[int(c.id[index:])] + 1
            new_s.add(substitution(c, sigma))
        new_s_f_list.append(new_s)

    sv = get_vars_from_set(new_s_f_list)

    l_v = list()
    for v in sv:
        new_v = remove_index(v)
        if new_v.id not in l_v:
            l_v.append(new_v.id)

    l_v = sorted(l_v)

    s_forall = list()
    s_integral = list()
    s_0 = list()
    s_tau = list()
    s_reset = list()
    s_guard = list()

    for i in range(max_bound + 1):
        s_forall_i, s_integral_i, s_0_i, s_tau_i, s_reset_i, s_guard_i = unit_split(s_f_list[i], i)
        s_forall.append(s_forall_i)
        s_integral.append(s_integral_i)
        s_0.append(s_0_i)
        s_tau.append(s_tau_i)
        s_reset.append(s_reset_i)
        s_guard.append(s_guard_i)

    ha = HybridAutomaton('ha')
    l_mode = list()

    for i in range(max_bound + 1):
        l_mode.append(FlowStarConverter.make_mode_property(s_integral[i], s_forall[i], i, max_bound, l_v, ha, sigma))

    l_mode.append(ha.new_mode("error"))

    for i in range(max_bound + 1):
        FlowStarConverter.make_transition(s_f_list[i], i, max_bound, ha, l_mode[i], l_mode[i + 1])

    forall_set, integral_set, init_set, tau_set, reset_set, guard_set = unit_split(s_f_list[0], max_bound)

    # assumption: all boundaries should be number
    sympy_expr_list = list()

    for cc in init_set:
        # if not isinstance(cc, Lt) or not isinstance(cc, Leq) or \
        #         not isinstance(cc, Gt) or not isinstance(cc, Geq) or \
        #         not isinstance(cc, Eq) or not isinstance(cc, Neq):
        sympy_expr_list.append(simplify(expr_to_sympy(reduce_not(cc))))

    bound_box_list = list()
    for i in range(len(l_v)):
        bound_box_list.append([None, None])

    for t in l_v:
        printer.print_debug("tau setting :\n{}".format(l_v))
        if ("tau" in t) or ("timeStep" in t):
            index = find_index(l_v, Real(t))
            printer.print_debug("{}, index => {}".format(t, index))
            bound_box_list[index][0] = Float(0.0)
            bound_box_list[index][1] = Float(0.0)

    printer.print_debug("\n\ninit constraints :")
    printer.print_debug("* variables : {}".format(l_v))
    for init_elem in init_set:
        printer.print_debug("  * {}".format(init_elem))

    for expr in sympy_expr_list:
        if isinstance(expr, GreaterThan) or isinstance(expr, StrictGreaterThan):
            # left is variable
            if expr.lhs.is_symbol:
                var_id = str(expr.lhs)
                index = find_index(l_v, Real(var_id))
                if bound_box_list[index][0] is None:
                    bound_box_list[index][0] = expr.rhs
                else:
                    if str(simplify(bound_box_list[index][0] <= expr.rhs)) == "True":
                        bound_box_list[index][0] = expr.rhs
            elif expr.rhs.is_symbol:
                var_id = str(expr.rhs)
                index = find_index(l_v, Real(var_id))
                if bound_box_list[index][1] is None:
                    bound_box_list[index][1] = expr.lhs
                else:
                    if str(simplify(bound_box_list[index][1] <= expr.lhs)) == "True":
                        bound_box_list[index][1] = expr.lhs

        elif isinstance(expr, LessThan) or isinstance(expr, StrictLessThan):
            # left is variable
            if expr.lhs.is_symbol:
                var_id = str(expr.lhs)
                index = find_index(l_v, Real(var_id))
                if bound_box_list[index][1] is None:
                    bound_box_list[index][1] = expr.rhs
                else:
                    if str(simplify(bound_box_list[index][1] >= expr.rhs)) == "True":
                        bound_box_list[index][1] = expr.rhs
            elif expr.rhs.is_symbol:
                var_id = str(expr.rhs)
                index = find_index(l_v, Real(var_id))
                if bound_box_list[index][0] is None:
                    bound_box_list[index][0] = expr.lhs
                else:
                    if str(simplify(bound_box_list[index][0] >= expr.lhs)) == "True":
                        bound_box_list[index][0] = expr.lhs
    new_bound_box_list = list()
    for e in bound_box_list:
        printer.print_debug("bound box list test : {}".format(e))
        bound_box_left = -float("inf")
        bound_box_right = float("inf")
        if e[0] is not None:
            bound_box_left = float(e[0])
        if e[1] is not None:
            bound_box_right = float(e[1])
        new_bound_box_list.append([bound_box_left, bound_box_right])

    # add affine variable
    printer.print_debug("* bound : ")
    printer.print_debug(new_bound_box_list)

    # mode = ha.modes['mode0']
    # print(l_v)
    # print(new_bound_box_list)

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
    return ha, conf_dict, l_v, new_bound_box_list


def flowstar_gen_without(formula: Constraint, bound, sigma, ha: HybridAutomaton):
    # def _instantiate_integral_forall (_clause_set: set, _substitution: dict):
    #     new_set = set()
    #     for _clause in _clause_set:
    #         new_set.add(substitution(_clause, _substitution))
    #     return new_set

    clause_of_formula = clause(formula)
    # clause_of_instantiated_formula = _instantiate_integral_forall(clause_of_formula, sigma)
    # instantiated_formula = And(clause_of_instantiated_formula)
    # sv = get_vars(formula)
    #
    # l_v = list()
    # for v in sv:
    #     new_v = remove_index(v)
    #     if new_v.id not in l_v:
    #         l_v.append(new_v.id)
    #
    # l_v = sorted(l_v)

    s_forall_i, s_integral_i, s_0_i, s_tau_i, s_reset_i, s_guard_i = unit_split(clause_of_formula, bound)

    mode_i = ha.new_mode("mode" + str(bound))

    for integral in s_integral_i:
        if integral in sigma:
            dyns = sigma[integral].dynamics
            # for j in range(1, i + 1):
            #     dyns.vars.append(Real("tau_" + str(j)))
            #     dyns.exps.append(RealVal("0"))
            #
            # for j in range(i + 1, max_bound + 2):
            #     dyns.vars.append(Real("tau_" + str(j)))
            #     dyns.exps.append(RealVal("1"))
            mode_i.set_dynamics(dyns)

    phi_forall_children = list()
    for c in s_forall_i:
        new_c = substitution(c, sigma)
        vs = get_vars(new_c)
        new_dict = dict()
        for v in vs:
            new_dict[v] = remove_index(v)
        phi_forall_children.append(reduce_not(substitution(new_c, new_dict)))

    if len(phi_forall_children) > 0:
        mode_i.set_invariant(And(phi_forall_children))
    return mode_i


def flowstar_solver(l: list):
    ha_list = list()
    # for integrity, l_vs are all the same
    latest_l_v = list()
    latest_bound_box_list = list()
    latest_conf_dict = dict()
    if len(l) > 0:
        for i, (ha, conf_dict, l_v, new_bound_box_list) in enumerate(l):
            # if i > 0:
            #    #assert l_v == latest_l_v
            #    #assert new_bound_box_list == latest_bound_box_list
            #    #assert latest_conf_dict == conf_dict
            ha.name = "{}_{}".format(ha.name, i)
            ha_list.append(ha)
            # print(ha)
            latest_l_v = l_v
            latest_bound_box_list = new_bound_box_list
            latest_conf_dict = conf_dict
            # print(ha)
            fs = FlowStarConverter(latest_conf_dict, latest_l_v, latest_bound_box_list)
            model_string = fs.convert(ha)
            flowStarRaw = FlowStar()
            flowStarRaw.run(model_string)
            if flowStarRaw.result:
                return False
        return True

        # nha = merge(*ha_list, chi_optimization=False)
        # fs = FlowStarConverter(latest_conf_dict, latest_l_v, latest_bound_box_list)
        # model_string = fs.convert(nha)
        # flowStarRaw = FlowStar()
        # flowStarRaw.run(model_string)
        # print("# HA: {}, modes: {}, transitions: {}".format(len(l), len(nha.modes), len(nha.transitions)))
        # if flowStarRaw.result:
        #     return False
        # else:
        #     return True
    return True


def flowstar_merging_solver(l: list, is_mini_merging=False):
    # gets representative l_v and list of bound_box_list
    # returns representative bound_box
    def _make_bound_box(_l_v, _bound_box_list):
        new_bound_box = list()
        for i, _ in enumerate(_l_v):
            max_left_value = -float("inf")
            max_right_value = -float("inf")
            for bbl in _bound_box_list:
                if bbl[i][0] > max_left_value:
                    max_left_value = bbl[i][0]
                if bbl[i][1] > max_right_value:
                    max_right_value = bbl[i][1]
            assert max_left_value != -float("inf")
            assert max_right_value != -float("inf")
            new_bound_box.append([max_left_value, max_right_value])
        return new_bound_box

    ha_list = list()
    bound_box_list = list()

    # for integrity, l_vs are all the same
    latest_l_v = list()
    latest_conf_dict = dict()
    if len(l) > 0:
        for i, (ha, conf_dict, l_v, new_bound_box_list) in enumerate(l):
            if i > 0:
                assert l_v == latest_l_v
                assert latest_conf_dict == conf_dict
            ha.name = "{}_{}".format(ha.name, i)
            ha_list.append(ha)
            bound_box_list.append(new_bound_box_list)

            latest_l_v = l_v
            latest_conf_dict = conf_dict

        bound_box = _make_bound_box(latest_l_v, bound_box_list)

        if is_mini_merging:
            print("mini merging ...")
        # nha = merge(*ha_list, chi_optimization=False, syntatic_merging=True)
        nha = new_merge(*ha_list, syntatic_merging=True)
        print("# HA: {}, modes: {}, transitions: {}".format(len(l), len(nha.modes), len(nha.transitions)), flush=True)
        if is_mini_merging:
            return nha, latest_conf_dict, latest_l_v, bound_box
        fs = FlowStarConverter(latest_conf_dict, latest_l_v, bound_box)
        model_string = fs.convert(nha)
        flowstar = FlowStar()
        flowstar.run(model_string)
        solving_time = flowstar.logger.get_duration_time("solving timer")
        if flowstar.result:
            return False, solving_time
        else:
            return True, solving_time
    return True, 0


class FlowStarSolverNaive(CommonOdeSolver):
    def __init__(self):
        assert "merging_strategy" in self.conf_dict
        underlying_solver = NormalSolvingStrategy(flowstar_solver)
        if self.conf_dict["merging_strategy"]:
            underlying_solver = MergeSolvingStrategy(flowstar_merging_solver)
        CommonOdeSolver.__init__(self, NaiveStrategyManager(), underlying_solver)

    def run(self, s_f_list, max_bound, sigma):
        conf_dict = make_flowstar_conf_dict(self.conf_dict)
        result, time = flowstar_run(s_f_list, max_bound, sigma, conf_dict)
        self.set_time("solving timer", time)
        return result

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

    def run(self, s_f_list, max_bound, sigma):
        conf_dict = make_flowstar_conf_dict(self.conf_dict)
        result, time = flowstar_run(s_f_list, max_bound, sigma, conf_dict)
        self.set_time("solving timer", time)
        return result

    def make_assignment(self):
        pass

    def clear(self):
        pass


class FlowStarSolverUnsatCoreMerging(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager(), MergeSolvingStrategy(flowstar_merging_solver))

    def run(self, s_f_list, max_bound, sigma):
        conf_dict = make_flowstar_conf_dict(self.conf_dict)
        return flowstar_gen(s_f_list, max_bound, sigma, conf_dict)

    def make_assignment(self):
        pass

    def clear(self):
        pass


class FlowStarSolverUnsatCore(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager(), NormalSolvingStrategy(flowstar_solver))

    def run(self, s_f_list, max_bound, sigma):
        conf_dict = make_flowstar_conf_dict(self.conf_dict)
        return flowstar_run(s_f_list, max_bound, sigma, conf_dict)

    def make_assignment(self):
        pass

    def clear(self):
        pass


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
