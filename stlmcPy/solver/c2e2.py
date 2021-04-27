import abc
import copy
from abc import ABC
from functools import singledispatch
from itertools import product

from sympy import symbols, simplify, StrictGreaterThan, GreaterThan, LessThan, StrictLessThan, Symbol, Float, Equality, \
    Unequality

from c2e2.core import C2E2
from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import substitution, reduce_not, get_vars
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.hybrid_automaton.converter import AbstractConverter
from stlmcPy.hybrid_automaton.hybrid_automaton import HybridAutomaton
<<<<<<< HEAD
from stlmcPy.hybrid_automaton.utils import calc_initial_terminal_modes
=======
from stlmcPy.hybrid_automaton.utils import calc_initial_terminal_modes, vars_in_ha
>>>>>>> f6721757eff63a8d0e28436a139d95040ccd56a5
from stlmcPy.solver.abstract_solver import BaseSolver, OdeSolver
from stlmcPy.solver.assignment import Assignment
from stlmcPy.solver.strategy import UnsatCoreBuilder, unit_split
from stlmcPy.solver.z3 import Z3Solver
from stlmcPy.tree.operations import size_of_tree
from stlmcPy.util.logger import Logger
from stlmcPy.util.print import Printer
from stlmcPy.solver.ode_solver import CommonOdeSolver, NaiveStrategyManager, ReductionStrategyManager, \
    UnsatCoreStrategyManager, NormalSolvingStrategy
from stlmcPy.solver.ode_utils import remove_index, expr_to_sympy, get_vars_from_set, expr_to_sympy_inequality, \
    find_index
from typing import *


class C2E2Converter(AbstractConverter):
<<<<<<< HEAD
    def __init__(self, inits: str):
        self.inits = inits
        print(inits)
        self.var_set = set()
=======
    def solve(self):
        c2e2_core_solver = C2E2()
        c2e2_core_solver.run(self.convert_result)
        solving_time = c2e2_core_solver.logger.get_duration_time("solving timer")
        if c2e2_core_solver.result:
            return False, solving_time
        else:
            return True, solving_time
>>>>>>> f6721757eff63a8d0e28436a139d95040ccd56a5

    def preprocessing(self, ha: HybridAutomaton):

        ffggee = Real("ffggee")
        zero = RealVal("0")
        one = RealVal("1")

        for mode in ha.modes:
            mode.set_dynamic(ffggee, zero)

        initial_modes, terminal_modes = calc_initial_terminal_modes(ha)

        # ffggee < 0
        non_error_const = Lt(ffggee, zero)
        # ffggee > 0
        error_const = Gt(ffggee, zero)
        # ffggee = 1 : reset
        error_on = Eq(ffggee, one)

        for init_mode in initial_modes:
            init_mode.set_invariant(non_error_const)

            for init_trans in init_mode.outgoing:
                init_trans.set_guard(non_error_const)

        for term_mode in terminal_modes:
            term_mode.set_invariant(error_const)

            for term_trans in term_mode.incoming:
                term_trans.set_reset(error_on)

        for transition in ha.transitions:
            to_be_removed_reset = set()
            for reset in transition.reset:
                assert isinstance(reset, Eq)
                if reset.left == reset.right:
                    to_be_removed_reset.add(reset)
            transition.remove_resets(to_be_removed_reset)

        _, terminal_modes = calc_initial_terminal_modes(ha)
        var_set = vars_in_ha(ha)

        # modes in c2e2 always have dynamics
        for term_mode in terminal_modes:
            for v in var_set:
                term_mode.set_dynamic(v, RealVal("0"))

    def convert(self, ha: HybridAutomaton, setting: Dict, variable_ordering: List, bound_box: List):
        def _make_conf_dict(_setting: dict):
            _dict = dict()
            keywords = ["step", "time", "kvalue"]
            for keyword in keywords:
                if keyword in _setting:
                    _dict[keyword] = _setting[keyword]
            return _dict

        self.preprocessing(ha)
        print("after preprocessing")
        print(ha)
        modes_str_list = list()
<<<<<<< HEAD

        initial_modes, terminal_modes = calc_initial_terminal_modes(ha)

        # get all variables and specify their types
        for m in ha.modes:
            put_var = set()
            # is_initial = False
            # if mode_index == 0:
            #     is_initial = True
            #     start_mode = m
            #
            mode_str = " <mode id=\"{}__id_{}\" initial=\"False\" name=\"{}\">\n".format(m.name, id(m), m.name)
            if m in initial_modes:
                mode_str = " <mode id=\"{}__id_{}\" initial=\"True\" name=\"{}\">\n".format(m.name, id(m), m.name)
            # mode_map[m] = mode_index
            #
            # if "error" in m:
            #     for v in self.var_set:
            #         mode_str += "  <dai equation=\"{}_dot = {}\"/>\n".format(v, 0)

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

                    # vars_dyn[newv] = infix(substitution(e, subst_dict))
                    # print(e)
                    if newv not in put_var:
                        put_var.add(newv)
                        mode_str += "  <dai equation=\"{}_dot = {}\"/>\n".format(newv, simplify(
                            expr_to_sympy(substitution(e, subst_dict))))
                    # mode_str += "  <dai equation=\"{}_out = {}\"/>\n".format(newv, newv)

            if m.invariant is not None:
                inv = m.invariant
                if isinstance(inv, And):
                    for ee in m.invariant.children:
                        # ets = expr_to_sympy(ee)
                        mode_str += "  <invariant equation=\"{}\"/>\n".format(
                            str(simplify(expr_to_sympy_inequality(ee)))
                            .replace(">", "&gt;")
                            .replace(">=", "&gt;=")
                            .replace("<", "&lt;")
                            .replace("<=", "&lt;="))
=======

        initial_modes, terminal_modes = calc_initial_terminal_modes(ha)

        # there should be only one initial mode
        # assert len(initial_modes) == 1

        # get all variables and specify their types
        for mode in ha.modes:
            mode_str = " <mode id=\"{}\" initial=\"False\" name=\"{}\">\n".format(id(mode), mode.name)
            if mode in initial_modes:
                mode_str = " <mode id=\"{}\" initial=\"True\" name=\"{}\">\n".format(id(mode), mode.name)

            for (var, exp) in mode.dynamics:
                mode_str += "  <dai equation=\"{}_dot = {}\"/>\n".format(var, simplify(expr_to_sympy(exp)))

            for inv in mode.invariant:
                simplified_inv = simplify(expr_to_sympy_inequality(inv))
                _str = ""
                if isinstance(simplified_inv, Equality):
                    _str = "{} &lt;= {} &amp;&amp; {} &gt;= {}".format(simplified_inv.lhs, simplified_inv.rhs,
                                                                       simplified_inv.lhs, simplified_inv.rhs)
>>>>>>> f6721757eff63a8d0e28436a139d95040ccd56a5
                else:
                    _str = "{}".format(simplified_inv)
                _mode_str = _str.replace(">", "&gt;").replace(">=", "&gt;=").replace("<", "&lt;").replace("<=", "&lt;=")
                mode_str += "  <invariant equation=\"{}\"/>\n".format(_mode_str)
            mode_str += " </mode>\n"
            modes_str_list.append(mode_str)

        modes_str = "\n".join(modes_str_list)

        var_str_list = list()
        var_set = vars_in_ha(ha)
        for v in var_set:
            var_str_list.append("  <variable name=\"{}\" scope=\"LOCAL_DATA\" type=\"Real\"/>".format(v.id))
        var_str = "\n".join(var_str_list)

        trans_str_list = list()
<<<<<<< HEAD
        for i, t in enumerate(ha.transitions):
            # src_id = mode_map[ha.trans[t].src.name]
            # dst_id = mode_map[ha.trans[t].trg.name]
            t_str = "  <transition destination=\"{}__id_{}\" id=\"{}\" source=\"{}__id_{}\">\n".format(t.trg.name, id(t.trg), i, t.src.name, id(t.src))

            # if "error" in ha.trans[t].trg.name:
            #     is_error_guard = True
            guard = t.guard
            # guard = ha.trans[t].guard
            if guard is not None:
                if isinstance(guard, And):
                    for g in guard.children:
                        ng = str(expr_to_sympy_inequality(g)).replace(">", "&gt;").replace(">=", "&gt;=").replace("<",
                                                                                                                  "&lt;").replace(
                            "<=", "&lt;=")
                        if is_error_guard:
                            error_guard_list.append(ng)
                        t_str += "   <guard equation=\"{}\"/>\n".format(ng)
=======
        for i, transition in enumerate(ha.transitions):
            t_str = "  <transition destination=\"{}\" id=\"{}\" source=\"{}\">\n".format(id(transition.trg), i,
                                                                                         id(transition.src))
            for guard in transition.guard:
                simplified_guard = simplify(expr_to_sympy_inequality(guard))
                _str = ""
                if isinstance(simplified_guard, Equality):
                    _str = "{} &lt;= {} &amp;&amp; {} &gt;= {}".format(simplified_guard.lhs, simplified_guard.rhs,
                                                                       simplified_guard.lhs, simplified_guard.rhs)
>>>>>>> f6721757eff63a8d0e28436a139d95040ccd56a5
                else:
                    _str = "{}".format(simplified_guard)
                g_str = _str.replace(">", "&gt;").replace(">=", "&gt;=").replace("<", "&lt;").replace("<=", "&lt;=")
                t_str += "   <guard equation=\"{}\"/>\n".format(g_str)

            for reset in transition.reset:
                assert isinstance(reset, Eq)
                assert isinstance(reset.left, Variable)

                t_str += "   <action equation=\"{}\"/>\n".format(C2E2infixReset(reset))
            t_str += "  </transition>"
            trans_str_list.append(t_str)
<<<<<<< HEAD
            if t.reset is not None:
                trans_reset = t.reset
                if isinstance(trans_reset, And):
                    if len(trans_reset.children) > 0:
                        for trans_child in trans_reset.children:
                            if isinstance(trans_child, Eq):
                                if isinstance(trans_child.left, Variable) and not isinstance(trans_child.right,
                                                                                             Variable):
                                    trans_str_list.append(
                                        "   <action equation=\"{}\"/>\n".format(C2E2infixReset(trans_child)))
            trans_str_list.append("  </transition>")
        trans_str = "\n".join(trans_str_list)

        error_guard_str = ""
        if len(error_guard_list) == 0:
            pass
        elif len(error_guard_list) == 1:
            error_guard_str = error_guard_list[0]
        else:
            error_guard_str = "&amp;&amp;".join(error_guard_list)

        prop_str = '''<property initialSet = \"{}: {}\" name = \"error_cond\" type = \"0\" unsafeSet = \"{}\">
         <parameters kvalue = \"2000.0\" timehorizon = \"40.0\" timestep = \"0.1\"/>
        </property>
        '''.format(start_mode, self.inits, error_guard_str)

        return (
            "<?xml version='1.0' encoding='utf-8'?>\n<!DOCTYPE hyxml>\n<hyxml type=\"Model\">\n <automaton name=\"{}\">\n{}\n{}\n{}\n </automaton>\n <composition automata=\"{}\"/>\n{}\n</hyxml>".format(
                ha.name, var_str, modes_str, trans_str, ha.name, prop_str))

        # trans_str = "jumps {{\n {} \n }}\n".format("\n".join(trans_str_list))
        #
        # init_str = "init {{\n {}{{".format(start_mode)
        # for iv, v in enumerate(self.var_list_ordering):
        #     init_str += "{} in [{}, {}]\n".format(v, self.init_bound[iv][0], self.init_bound[iv][1])
        # init_str += "}\n}\n"
        #
        # return "hybrid reachability {{\n {}\n {}\n {}\n {}\n {}\n}}\n unsafe {{\n error {{}}\n }}\n".format(var_str, setting_str, modes_str, trans_str, init_str)

    @staticmethod
    def make_mode_property(s_integral_i, s_forall_i, i, max_bound, ha: HybridAutomaton, sigma):
        mode_i = ha.new_mode("mode" + str(i))
        for integral in s_integral_i:
            if integral in sigma:
                dyns = sigma[integral].dynamics
                for j in range(1, i + 1):
                    tau_var = Real("tau_" + str(j))
                    if tau_var not in dyns.vars:
                        dyns.vars.append(tau_var)
                        dyns.exps.append(RealVal("0"))

                for j in range(i + 1, max_bound + 2):
                    tau_var = Real("tau_" + str(j))
                    if tau_var not in dyns.vars:
                        dyns.vars.append(tau_var)
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

        if "error" in mode_n.name:
            mode_n.set_invariant(And(phi_new_guard_children))

        phi_new_reset_children = list()
        for c in s_reset_i:
            vs = get_vars(c)
            new_dict = dict()
            for v in vs:
                new_dict[v] = remove_index(v)
            phi_new_reset_children.append(reduce_not(substitution(c, new_dict)))

        trans_i.set_reset(And(phi_new_reset_children))


def c2e2_run(s_f_list, max_bound, sigma):
    new_s_f_list = list()
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

    # printer = Printer()
    # printer.print_debug("\n\ninput s_f_list : \n\n{}".format(s_f_list))
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
        l_mode.append(C2E2Converter.make_mode_property(s_integral[i], s_forall[i], i, max_bound, ha, sigma))

    l_mode.append(ha.new_mode("error"))

    for i in range(max_bound + 1):
        C2E2Converter.make_transition(s_f_list[i], i, max_bound, ha, l_mode[i], l_mode[i + 1])

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
        # printer.print_debug("tau setting :\n{}".format(l_v))
        if ("tau" in t) or ("timeStep" in t):
            index = find_index(l_v, Real(t))
            # printer.print_debug("{}, index => {}".format(t, index))
            bound_box_list[index][0] = Float(0.0)
            bound_box_list[index][1] = Float(0.0)

    # printer.print_debug("\n\ninit constraints :")
    # printer.print_debug("* variables : {}".format(l_v))
    # for init_elem in init_set:
    #     printer.print_debug("  * {}".format(init_elem))

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
        # printer.print_debug("bound box list test : {}".format(e))
        bound_box_left = -float("inf")
        bound_box_right = float("inf")
        if e[0] is not None:
            bound_box_left = float(e[0])
        if e[1] is not None:
            bound_box_right = float(e[1])
        new_bound_box_list.append([bound_box_left, bound_box_right])

    # printer.print_debug("* bound : ")
    # print(l_v)
    # print(new_bound_box_list)

    init_str_list = list()
    for i, v in enumerate(l_v):
        left = new_bound_box_list[i][0]
        right = new_bound_box_list[i][1]
        # c2e2 only support variables to the left
        if left == right:
            init_str_list.append("{} == {}".format(v, left))
        else:
            # c2e2 only support variables to the left
            init_str_list.append("{} &gt;= {} &amp;&amp; {} &lt;= {}".format(v, left, v, right))

    # print(" & ".join(init_str_list))

    # v_set = set()
    # for ss in s_tau:
    #     for s in ss:
    #         v_set.update(get_vars(s))
    #
    # init_children = list()
    # for c in init_set:
    #     vs = get_vars(c)
    #     new_dict = dict()
    #     for v in vs:
    #         new_dict[v] = remove_index(v)
    #     init_children.append(substitution(c, new_dict))
    #
    # for c in v_set:
    #     init_children.append(Eq(c, RealVal(0)))
    #
    sec = C2E2Converter(" &amp;&amp; ".join(init_str_list))
    c_model = sec.convert(ha)
    c2e2_solver = C2E2()
    result = c2e2_solver.run(c_model)

    # net_v_set = set()
    # for sf in s_f_list:
    #     for c in sf:
    #         vs = get_vars(c)
    #         for v in vs:
    #             net_v_set.add(remove_index(v))
    #
    # print(net_v_set)
    # sp = TestSpaceex()
    # out_var_str = ""
    # for ove_index, ovs in enumerate(sec.var_set):
    #     # if first
    #     if ove_index == 0:
    #         out_var_str = "{}".format(ovs.id)
    #     else:
    #         out_var_str += ", {}".format(ovs.id)
    #
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
    #
    # conf_string = ""
    # for key in conf_dict:
    #     conf_string += "{} = {}\n".format(key, conf_dict[key])
    #
    # sp.run(c_model, conf_string)
    # sp.run(infix(And(init_children)),"x1,x2,tau_1,tau_2",c_model)
    # sp.set_system("system")
    # sp.set_init_set(infix(And(init_children)))
    # sp.set_scenario("supp")
    # sp.set_directions("uni32")
    # sp.set_sample_time("0.01")
    # sp.set_time_horizon("10")
    # sp.set_iter_max("5")
    # sp.set_output_variables("x1,x2,tau_1,tau_2")
    # sp.set_output_format("TXT")
    # sp.set_rel_error("1.0e-12")
    # sp.set_abs_error("1.0e-12")
    #
    # model_string = c_model
    # print(model_string)
    # sp.set_output("outout")
    # sp.set_model(model_string)
    # sp.run()
    # sp.clean()

    # if core.is_counterexample:
    #     self.hylaa_core = core
    #     return False
    # else:
    #     return True

    if result:
        return False
    else:
        return True
=======

        trans_str = "\n".join(trans_str_list)

        # get unique initial mode
        # init_mode = initial_modes.pop()

        init_str_list = list()
        for i, v in enumerate(variable_ordering):
            init_str_list.append("{} &gt;= {} &amp;&amp; {} &lt;= {}".format(v, bound_box[i][0], v, bound_box[i][1]))
        init_str = "&amp;&amp;".join(init_str_list)

        c2e2_setting = _make_conf_dict(setting)

        prop_str = ""
        for i, init_mode in enumerate(initial_modes):
            prop_str += '''<property initialSet = \"{}: {} &amp;&amp; ffggee == -1\" name = \"error_cond_{}\" type = \"0\" unsafeSet = \"ffggee &gt; 0\">
            <parameters kvalue = \"{}\" timehorizon = \"{}\" timestep = \"{}\"/>
            </property>
            '''.format(init_mode.name, init_str, i, c2e2_setting["kvalue"], c2e2_setting["time"], c2e2_setting["step"])

        self.convert_result = "<?xml version='1.0' encoding='utf-8'?>\n<!DOCTYPE hyxml>\n<hyxml type=\"Model\">\n <automaton name=\"{}\">\n{}\n{}\n{}\n </automaton>\n <composition automata=\"{}\"/>\n{}\n</hyxml>".format(
            ha.name, var_str, modes_str, trans_str, ha.name, prop_str)
>>>>>>> f6721757eff63a8d0e28436a139d95040ccd56a5

def c2e2_solver(l: list):
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
            fs = C2E2Converter(latest_conf_dict, latest_l_v, latest_bound_box_list)
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










class C2E2SolverNaive(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, NaiveStrategyManager())

    def run(self, s_f_list, max_bound, sigma):
        return c2e2_run(s_f_list, max_bound, sigma)

    def make_assignment(self):
        pass

    def clear(self):
        pass


class C2E2SolverReduction(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, ReductionStrategyManager())

<<<<<<< HEAD
    def run(self, s_f_list, max_bound, sigma):
        return c2e2_run(s_f_list, max_bound, sigma)

=======
>>>>>>> f6721757eff63a8d0e28436a139d95040ccd56a5
    def make_assignment(self):
        pass

    def clear(self):
        pass


class C2E2SolverUnsatCore(CommonOdeSolver):
    def __init__(self):
<<<<<<< HEAD
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager(), NormalSolvingStrategy(c2e2_solver))

    def run(self, s_f_list, max_bound, sigma):
        return c2e2_run(s_f_list, max_bound, sigma)
=======
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager(), NormalSolvingStrategy(C2E2Converter()))
>>>>>>> f6721757eff63a8d0e28436a139d95040ccd56a5

    def make_assignment(self):
        pass

    def clear(self):
        pass


class C2E2Assignment(Assignment):
    def __init__(self, spaceex_counterexample):
        self.spaceex_counterexample = spaceex_counterexample

    def get_assignments(self):
        print(self.spaceex_counterexample)

    def eval(self, const):
        pass


@singledispatch
def C2E2infix(const: Constraint):
    return str(const)


@C2E2infix.register(Variable)
def _(const: Variable):
    return const.id


@C2E2infix.register(And)
def _(const: And):
    return '&amp;&amp;'.join([C2E2infix(c) for c in const.children])


@C2E2infix.register(Geq)
def _(const: Geq):
    return C2E2infix(const.left) + " &gt;= " + C2E2infix(const.right)


@C2E2infix.register(Gt)
def _(const: Geq):
    return C2E2infix(const.left) + " &gt; " + C2E2infix(const.right)


@C2E2infix.register(Leq)
def _(const: Geq):
    return C2E2infix(const.left) + " &lt;= " + C2E2infix(const.right)


@C2E2infix.register(Lt)
def _(const: Geq):
    return C2E2infix(const.left) + " &lt; " + C2E2infix(const.right)


@C2E2infix.register(Eq)
def _(const: Eq):
    return C2E2infix(const.left) + " == " + C2E2infix(const.right)


# cannot support this
@C2E2infix.register(Neq)
def _(const: Geq):
    return C2E2infix(const.left) + " &gt;= " + C2E2infix(const.right) + " &amp;&amp; " + C2E2infix(
        const.left) + " &lt; " + C2E2infix(
        const.right)


@C2E2infix.register(Add)
def _(const: Add):
    return "(" + C2E2infix(const.left) + " + " + C2E2infix(const.right) + ")"


@C2E2infix.register(Sub)
def _(const: Sub):
    return "(" + C2E2infix(const.left) + " - " + C2E2infix(const.right) + ")"


@C2E2infix.register(Neg)
def _(const: Neg):
    return "(-" + C2E2infix(const.child) + ")"


@C2E2infix.register(Mul)
def _(const: Mul):
    return "(" + C2E2infix(const.left) + " * " + C2E2infix(const.right) + ")"


@C2E2infix.register(Div)
def _(const: Div):
    return "(" + C2E2infix(const.left) + " / " + C2E2infix(const.right) + ")"


# maybe not supported
@C2E2infix.register(Pow)
def _(const: Pow):
    return "(" + C2E2infix(const.left) + " ** " + C2E2infix(const.right) + ")"


@C2E2infix.register(Forall)
def _(const: Forall):
    return C2E2infix(const.const)


### start


@singledispatch
def C2E2infixReset(const: Constraint):
    return str(const)


@C2E2infixReset.register(Variable)
def _(const: Variable):
    return const.id


@C2E2infixReset.register(And)
def _(const: And):
    return '&amp;&amp;'.join([C2E2infixReset(c) for c in const.children])


@C2E2infixReset.register(Geq)
def _(const: Geq):
    return C2E2infixReset(const.left) + " &gt;= " + C2E2infixReset(const.right)


@C2E2infixReset.register(Gt)
def _(const: Geq):
    return C2E2infixReset(const.left) + " &gt; " + C2E2infixReset(const.right)


@C2E2infixReset.register(Leq)
def _(const: Geq):
    return C2E2infixReset(const.left) + " &lt;= " + C2E2infixReset(const.right)


@C2E2infixReset.register(Lt)
def _(const: Geq):
    return C2E2infixReset(const.left) + " &lt; " + C2E2infixReset(const.right)


@C2E2infixReset.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Real):
        r_str = C2E2infixReset(const.right)
        if const.left.id == r_str:
            return ""
        return "{} = {}".format(const.left.id, r_str)
    elif isinstance(const.left, Int):
        r_str = C2E2infixReset(const.right)
        if const.left.id == r_str:
            return ""
        return "{} = {}".format(const.left.id, r_str)
    else:
        raise NotSupportedError()


# cannot support this
@C2E2infixReset.register(Neq)
def _(const: Geq):
    return C2E2infixReset(const.left) + " &gt;= " + C2E2infixReset(const.right) + " &amp;&amp; " + C2E2infixReset(
        const.left) + " &lt; " + C2E2infixReset(
        const.right)


@C2E2infixReset.register(Add)
def _(const: Add):
    return "(" + C2E2infixReset(const.left) + " + " + C2E2infixReset(const.right) + ")"


@C2E2infixReset.register(Sub)
def _(const: Sub):
    return "(" + C2E2infixReset(const.left) + " - " + C2E2infixReset(const.right) + ")"


@C2E2infixReset.register(Neg)
def _(const: Neg):
    return "(-" + C2E2infixReset(const.child) + ")"


@C2E2infixReset.register(Mul)
def _(const: Mul):
    return "(" + C2E2infixReset(const.left) + " * " + C2E2infixReset(const.right) + ")"


@C2E2infixReset.register(Div)
def _(const: Div):
    return "(" + C2E2infixReset(const.left) + " / " + C2E2infixReset(const.right) + ")"


# maybe not supported
@C2E2infixReset.register(Pow)
def _(const: Pow):
    return "(" + C2E2infixReset(const.left) + " ** " + C2E2infixReset(const.right) + ")"


@C2E2infixReset.register(Forall)
def _(const: Forall):
    return C2E2infixReset(const.const)

# start
