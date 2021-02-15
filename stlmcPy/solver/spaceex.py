import abc
import copy
from abc import ABC
from functools import singledispatch
from itertools import product

from sympy import symbols, simplify, StrictGreaterThan, GreaterThan, LessThan, StrictLessThan, Symbol, Float, Equality, \
    Unequality
from sympy.core import relational

from spaceex.core import Spaceex, TestSpaceex
from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import substitution, reduce_not, get_vars, infix
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.hybrid_automaton.abstract_converter import AbstractConverter
from stlmcPy.hybrid_automaton.hybrid_automaton import HybridAutomaton
from stlmcPy.solver.abstract_solver import BaseSolver, OdeSolver
from stlmcPy.solver.assignment import Assignment
from stlmcPy.solver.ode_solver import CommonOdeSolver, NaiveStrategyManager, ReductionStrategyManager, \
    UnsatCoreStrategyManager
from stlmcPy.solver.ode_utils import remove_index
from stlmcPy.solver.strategy import UnsatCoreBuilder, unit_split
from stlmcPy.solver.z3 import Z3Solver
from stlmcPy.tree.operations import size_of_tree
from stlmcPy.util.logger import Logger
from stlmcPy.util.print import Printer


class SpaceExConverter(AbstractConverter):
    def __init__(self):
        self.var_set = set()

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

        # get all variables and specify their types
        for m in ha.modes:
            if ha.modes[m].dynamics is not None:
                for i, v in enumerate(ha.modes[m].dynamics.vars):
                    newv = remove_index(v)
                    vars_old_new_map[v] = newv
                    self.var_set.add(newv)
                    # do we need do check this?
                    if isinstance(ha.modes[m].dynamics.exps[i], RealVal):
                        vars[newv] = "const"
                    else:
                        vars[newv] = "any"
                    vars_dyn[newv] = spaceExinfix(ha.modes[m].dynamics.exps[i])

        var_str = ""
        for v in vars:
            var_str += "\t\t<param name=\"{}\" type=\"{}\" local=\"false\" d1=\"1\" d2=\"1\" dynamics=\"any\" />\n".format(
                v.id, v.type)

        var_str_with_label = var_str
        for t in ha.trans:
            var_str_with_label += "\t\t<param name=\"{}\" type=\"label\" local=\"true\" />\n".format(t)

        mode_str = ""

        for i, m in enumerate(ha.modes):
            mode_map[m] = i
            loc_str_begin = "<location id=\"{}\" name=\"{}\" x=\"{}\" y=\"100\" width=\"50\" height=\"50\">\n".format(i,
                                                                                                                      m,
                                                                                                                      50 * i)
            inv_str = ""
            if ha.modes[m].invariant is not None:
                inv_str = "<invariant>{}</invariant>\n".format(spaceExinfix(ha.modes[m].invariant))
            f_s = list()
            flow_str = ""
            if ha.modes[m].dynamics is not None:
                for j, v in enumerate(ha.modes[m].dynamics.vars):
                    e = ha.modes[m].dynamics.exps[j]
                    e_var_set = get_vars(e)
                    subst_dict = dict()
                    for e_var in e_var_set:
                        e_var_wo_index = remove_index(e_var)
                        subst_dict[e_var] = e_var_wo_index
                        self.var_set.add(e_var_wo_index)

                    f_s.append("{}\' == {}".format(vars_old_new_map[v].id, spaceExinfix(substitution(e, subst_dict))))
                flow_str = "<flow>{}</flow>\n".format("&amp;".join(f_s))
            loc_str_end = "</location>\n"
            mode_str += loc_str_begin + inv_str + flow_str + loc_str_end

        trans_str = ""
        for i, t in enumerate(ha.trans):
            t_str_begin = "<transition source=\"{}\" target=\"{}\">\n".format(mode_map[ha.trans[t].src.name],
                                                                              mode_map[ha.trans[t].trg.name])
            t_label = "<label>{}</label>\n".format(t)
            t_label_position = "<labelposition x=\"{}\" y=\"200\" width=\"{}\" height=\"{}\"/>\n".format(50 * i, 50, 50)
            guard_str = ""
            if ha.trans[t].guard is not None:
                guard_str = "<guard>{}</guard>\n".format(spaceExinfix(ha.trans[t].guard))
            reset_str = ""
            if ha.trans[t].reset is not None:
                reset_str = "<assignment>{}</assignment>\n".format(spaceExinfixReset(ha.trans[t].reset))
            t_str_end = "</transition>\n"
            trans_str += t_str_begin + t_label + guard_str + reset_str + t_label_position + t_str_end

        hybrid_automaton_component = '''<component id=\"{}\">
        {}{}{}
        </component>
        '''.format(ha.name, var_str_with_label, mode_str, trans_str)

        map_str = ""
        for v_name in vars:
            map_str += "<map key=\"{}\">{}</map>\n".format(v_name, v_name)
            # if vars[v_name] == "any":
            #     map_str += "<map key=\"{}\">{}</map>\n".format(v_name, v_name)
            # elif vars[v_name] == "const":
            #     map_str += "<map key=\"{}\">{}</map>\n".format(v_name, vars_dyn[v_name])

        system_component = '''<component id=\"system\">
        {}
        <bind component=\"{}\" as=\"{}_system\" x=\"300\" y=\"200\">
        {}
        </bind>
        </component>
        '''.format(var_str, ha.name, ha.name, map_str)

        return '''<?xml version="1.0" encoding="UTF-8"?>
<sspaceex xmlns="http://www-verimag.imag.fr/xml-namespaces/sspaceex" version="0.2" math="SpaceEx"> 
{}
{}
</sspaceex>
        '''.format(hybrid_automaton_component, system_component)

    def make_mode_property(s_integral_i, s_forall_i, i, max_bound, ha: HybridAutomaton, sigma):
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


def space_ex_run(s_f_list, max_bound, sigma, tau_guard_list):
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
        l_mode.append(SpaceExConverter.make_mode_property(s_integral[i], s_forall[i], i, max_bound, ha, sigma))

    l_mode.append(ha.new_mode("error"))

    for i in range(max_bound + 1):
        SpaceExConverter.make_transition(s_f_list[i], i, max_bound, ha, l_mode[i], l_mode[i + 1])

    forall_set, integral_set, init_set, tau_set, reset_set, guard_set = unit_split(s_f_list[0], max_bound)

    v_set = set()
    for ss in s_tau:
        for s in ss:
            v_set.update(get_vars(s))
    sec = SpaceExConverter()
    c_model = sec.convert(ha)

    init_children = list()
    for c in init_set:
        vs = get_vars(c)
        new_dict = dict()
        for v in vs:
            new_dict[v] = remove_index(v)
        init_children.append(substitution(c, new_dict))

    for c in v_set:
        init_children.append(Eq(c, RealVal(0)))
    # print(infix(And(init_children)))

    # net_v_set = set()
    # for sf in s_f_list:
    #     for c in sf:
    #         vs = get_vars(c)
    #         for v in vs:
    #             net_v_set.add(remove_index(v))
    #
    # print(net_v_set)
    sp = TestSpaceex()
    out_var_str = ""
    for ove_index, ovs in enumerate(sec.var_set):
        # if first
        if ove_index == 0:
            out_var_str = "{}".format(ovs.id)
        else:
            out_var_str += ", {}".format(ovs.id)

    conf_dict = dict()
    conf_dict["system"] = "\"system\""
    conf_dict["initially"] = "\"{}\"".format(infix(And(init_children)))
    conf_dict["scenario"] = "\"supp\""
    conf_dict["directions"] = "\"uni32\""
    conf_dict["sampling-time"] = "0.1"
    conf_dict["time-horizon"] = "100"
    conf_dict["iter-max"] = "10"
    conf_dict["output-variables"] = "\"{}\"".format(out_var_str)
    conf_dict["output-format"] = "\"TXT\""
    conf_dict["rel-err"] = "1.0e-12"
    conf_dict["abs-err"] = "1.0e-13"

    conf_string = ""
    for key in conf_dict:
        conf_string += "{} = {}\n".format(key, conf_dict[key])

    sp.run(c_model, conf_string)
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

    if sp.result:
        return False
    else:
        return True


class SpaceExSolverNaive(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, NaiveStrategyManager())

    def run(self, s_f_list, max_bound, sigma, tau_guard_list):
        return space_ex_run(s_f_list, max_bound, sigma, tau_guard_list)

    def make_assignment(self):
        pass

    def clear(self):
        pass


class SpaceExSolverReduction(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, ReductionStrategyManager())

    def run(self, s_f_list, max_bound, sigma, tau_guard_list):
        return space_ex_run(s_f_list, max_bound, sigma, tau_guard_list)

    def make_assignment(self):
        pass

    def clear(self):
        pass


class SpaceExSolverUnsatCore(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager())

    def run(self, s_f_list, max_bound, sigma, tau_guard_list):
        return space_ex_run(s_f_list, max_bound, sigma, tau_guard_list)

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
