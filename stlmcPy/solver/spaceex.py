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
from stlmcPy.solver.strategy import UnsatCoreBuilder, unit_split
from stlmcPy.solver.z3 import Z3Solver
from stlmcPy.tree.operations import size_of_tree
from stlmcPy.util.logger import Logger
from stlmcPy.util.print import Printer



class SpaceExConverter(AbstractConverter):
    def __init__(self):
        self.var_set = set()

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


# builder class for hylaa
class SpaceExStrategy:

    @abc.abstractmethod
    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict):
        pass

    def get_max_literal(self, alpha, assignment, max_bound, c, optimize, z3_boolean_consts, boolean_sub_dict):
        c_sat = set()
        c_unsat = set()
        total = dict()

        assign_const = list()

        for b in boolean_sub_dict:
            if not isinstance(b, Bool):
                if assignment.eval(b):
                    assign_const.append(boolean_sub_dict[b])
                else:
                    if not "newTau" in boolean_sub_dict[b].id:
                        assign_const.append(Not(boolean_sub_dict[b]))

        boolean_variables = list()
        for a in alpha:
            if isinstance(a, Bool):
                boolean_variables.append(a.id)

        for c_elem in c:
            vs = get_vars(c_elem)
            flag = True

            for c_vs in vs:
                if c_vs.id in boolean_variables or "newPropDecl" in c_vs.id or "chi" in c_vs.id or "invAtomicID" in c_vs.id or "newIntegral" in c_vs.id:
                    flag = False
                    if c_vs not in alpha:
                        pass
                    elif str(alpha[c_vs]) == "True":
                        total[c_vs] = alpha[c_vs]
                        c_sat.add(c_vs)
                    elif str(alpha[c_vs]) == "False":
                        total[c_vs] = alpha[c_vs]
                        c_unsat.add(Not(c_vs))
                    else:
                        flag = True
                        # raise NotSupportedError("Forall variable assignments problem")
                    break

            if flag:
                if assignment.eval(c_elem):
                    total[c_elem] = BoolVal("True")
                    c_sat.add(c_elem)
                else:
                    total[c_elem] = BoolVal("False")
                    c_unsat.add(Not(c_elem))

        alpha_delta = total

        max_literal_set_list = list()
        total_set = c_sat.union(c_unsat)

        for i in range(max_bound + 1):
            # max_literal_start = timer()
            max_literal_set, alpha_delta = self.get_max_literal_aux(i, c_sat.union(c_unsat), alpha_delta, optimize,
                                                                    z3_boolean_consts, boolean_sub_dict, assign_const)
            # max_literal_end = timer()
            # print("For bound : " + str(i) + " solving time is " + str(max_literal_end - max_literal_start))

            max_literal_set_list.append(max_literal_set)
        return max_literal_set_list, alpha_delta

    def get_max_literal_aux(self, i, c_sat, alpha_delta: dict, optimize, z3_boolean_consts, boolean_sub_dict,
                            assign_const):
        forall_set, integral_set, init_set, tau_set, reset_set, guard_set = unit_split(c_sat, i)
        reset_pool = make_reset_pool(reset_set)

        diff = set()

        for c in alpha_delta:
            if c in integral_set:
                for v in get_vars(c):
                    diff.add(v)
            elif c in reset_set:
                diff.add(c)
        for c in diff:
            del alpha_delta[c]

        for integral in integral_set:
            append_boolean_const = list()
            for v in get_vars(integral):
                alpha_delta[v] = BoolVal("True")
            for reset in reset_pool:
                for r in reset:
                    alpha_delta[r] = BoolVal("True")
                for b in boolean_sub_dict:
                    if isinstance(b, Bool):
                        if b not in alpha_delta:
                            pass
                        elif str(alpha_delta[b]) == "True":
                            append_boolean_const.append(b)
                        else:
                            append_boolean_const.append(Not(b))

                last_boolean_const = assign_const + append_boolean_const

                max_literal_set, alpha_delta = self.solve_strategy_aux(alpha_delta, i, z3_boolean_consts,
                                                                       last_boolean_const, boolean_sub_dict)

                if max_literal_set is not None and alpha_delta is not None:
                    if not optimize:
                        s_diff = set()
                        for se in max_literal_set:
                            if isinstance(se, Bool):
                                if "newTau" in se.id:
                                    s_diff.add(se)
                        max_literal_set = max_literal_set.difference(s_diff)

                    return max_literal_set, alpha_delta

    @abc.abstractmethod
    def solve_strategy_aux(self, alpha_delta, bound, z3_boolean_consts, boolean_const_model, boolean_sub_dict):
        pass


def make_tau_guard(tau_dict, max_bound):
    result = list()
    for i in range(max_bound):
        sub = dict()
        for k in tau_dict:
            if "newTau" in k.id:
                if k.id[-1] == str(i):
                    or_literals = set()
                    for e in tau_dict[k].children:
                        or_literals.add(e)
                    sub[k] = or_literals
        result.append(sub)
    return result


def make_boolean_abstract(abstracted_consts):
    index = 0
    new_id = "new_boolean_var_"
    clause_list = clause(abstracted_consts)
    sub_dict = dict()
    original_bool = list()

    solver = Z3Solver()
    solver.set_logic("lra")

    for c in clause_list:
        if not isinstance(c, Bool):
            sub_dict[c] = Bool(new_id + str(index))
            index += 1
        else:
            original_bool.append(c)

    boolean_abstracted = solver.substitution(abstracted_consts, sub_dict)

    for o in original_bool:
        sub_dict[o] = o
    return boolean_abstracted, sub_dict


class SpaceExSolver(OdeSolver, SpaceExStrategy, ABC):
    def __init__(self):
        BaseSolver.__init__(self)
        self.hylaa_core = None
        self.time_optimize = False

    def solve(self, all_consts=None, info_dict=None, mapping_info=None):
        assert self.logger is not None
        if info_dict is None:
            info_dict = dict()
        if mapping_info is None:
            mapping_info = dict()

        logger = self.logger

        tau_info = dict()
        for k in mapping_info:
            if "newTau" in k.id:
                tau_info[k] = mapping_info[k]

        printer = Printer()
        # pre-processing
        # boolean_start = timer()
        # heuristic: removing mapping constraint part.
        trans_all_consts = list()
        trans_all_consts.append(all_consts.children[0])
        if not SpaceExSolver().time_optimize:
            bef = all_consts.children[1]
            tau_condition_sub = substitution(all_consts.children[1].children[-1], tau_info)
            aft = all_consts.children[1].children[0:-1]
            aft.append(tau_condition_sub)
            trans_all_consts.append(And(aft))
        else:
            trans_all_consts.append(all_consts.children[1])

        abstracted_consts = And(trans_all_consts)
        first_abst_size = size_of_tree(abstracted_consts)

        # get stlmc type constraints and transform
        z3_boolean_consts, boolean_sub_dict = make_boolean_abstract(abstracted_consts)
        # boolean_end = timer()

        max_bound = get_bound(mapping_info)
        tau_guard_list = make_tau_guard(mapping_info, max_bound)

        hylaa_result = True
        counter_consts = None

        cur_index = 0
        solver = Z3Solver()
        solver.append_logger(logger)
        solver.add(abstracted_consts)
        while hylaa_result:
            # logging
            logger.add_info("loop", cur_index)

            abst_size = size_of_tree(abstracted_consts)
            logger.add_info("constraint size", abst_size)

            printer.print_verbose("loop : {}, size of constraints : {}".format(cur_index, abst_size))
            #
            logger.start_timer("loop timer")
            logger.start_timer("smt solving timer")

            cur_index += 1
            if counter_consts is not None:
                children_list = list()
                for chi in abstracted_consts.children:
                    children_list.append(chi)
                children_list.append(Or(counter_consts))
                abstracted_consts = And(children_list)
                solver.add(Or(counter_consts))

            # 2. Perform process #2 from note
            result, size = solver.solve()

            logger.stop_timer("smt solving timer")
            logger.add_info("smt solving time", logger.get_duration_time("smt solving timer"))

            if result:
                printer.print_normal_dark("Smt solver level result!")
                logger.write_to_csv()
                print("The number of loop : " + str(cur_index))
                # self.add_log_info("SMT solver level result!")
                return True, 0
            assignment = solver.make_assignment()
            alpha = assignment.get_assignments()

            for mp in mapping_info:
                if isinstance(mapping_info[mp], Or):
                    mapping_info[mp] = mapping_info[mp].children[0]

            net_dict = info_dict.copy()
            net_dict.update(mapping_info)
            new_alpha = gen_net_assignment(alpha, net_dict)
            new_abstracted_consts = abstracted_consts
            c = clause(new_abstracted_consts)

            logger.start_timer("max literal timer")
            max_literal_set_list, alpha_delta = self.perform_strategy(alpha, assignment, max_bound,
                                                                      new_abstracted_consts,
                                                                      c, SpaceExSolver().time_optimize,
                                                                      z3_boolean_consts,
                                                                      boolean_sub_dict)
            logger.stop_timer("max literal timer")
            logger.add_info("preparing max literal set", logger.get_duration_time("max literal timer"))

            remove_mode_clauses = list()
            for clause_bound in max_literal_set_list:
                s_diff = set()
                for elem in clause_bound:
                    if isinstance(elem, Bool):
                        if "reach_goal" in elem.id:
                            s_diff.add(elem)
                    if isinstance(elem, Neq):
                        s_diff.add(elem)
                    vs = get_vars(elem)
                    if len(vs) == 0:
                        s_diff.add(elem)
                    for v in vs:
                        if v in new_alpha:
                            s_diff.add(elem)
                clause_bound = clause_bound.difference(s_diff)
                remove_mode_clauses.append(clause_bound)

            max_literal_set_list = remove_mode_clauses

            counter_consts_set = set()
            max_bound = -1
            for s in max_literal_set_list:
                for c in s:
                    if isinstance(c, Bool):
                        if "newIntegral" in c.id:
                            index = int(c.id.rfind("_")) + 1
                            bound = int(c.id[index:])
                            if bound > max_bound:
                                max_bound = bound
                    if str(alpha_delta[c]) == "True":
                        counter_consts_set.add(Not(c))
                    else:
                        counter_consts_set.add(c)

            counter_consts = list(counter_consts_set)

            try:
                logger.start_timer("hylaa timer")
                hylaa_result = self.run(max_literal_set_list, max_bound, mapping_info,
                                        tau_guard_list)
                # hylaa_result = True
                logger.stop_timer("hylaa timer")
                logger.add_info("hylaa time", logger.get_duration_time("hylaa timer"))

                logger.stop_timer("loop timer")
                logger.add_info("loop total", logger.get_duration_time("loop timer"))
                logger.write_to_csv()
                logger.reset_timer_without("goal timer")

            except RuntimeError as re:
                # negate the error state
                hylaa_result = True

                import sys
                import traceback
                exc_type, exc_value, exc_traceback = sys.exc_info()
                traceback.print_tb(exc_traceback, file=sys.stdout)
                printer.print_normal_dark("retry because of {}".format(re))
                logger.write_to_csv()
                logger.reset_timer_without("goal timer")

        # get overviewed file name
        output_file_name = logger.get_output_file_name()
        bound_index = output_file_name.rfind("_")
        overview_file_name = output_file_name[:bound_index]

        logger.add_info("bound", max_bound)
        logger.add_info("loop", cur_index)
        logger.add_info("constraint size", first_abst_size)
        logger.write_to_csv(file_name=overview_file_name, cols=["bound", "loop", "constraint size"])

        # TODO: replace -1 to formula size
        return hylaa_result, -1

    def run(self, s_f_list, max_bound, sigma, tau_guard_list):
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
            l_mode.append(make_mode_property(s_integral[i], s_forall[i], i, max_bound, ha, sigma))

        l_mode.append(ha.new_mode("error"))

        for i in range(max_bound + 1):
            make_transition(s_f_list[i], i, max_bound, ha, l_mode[i], l_mode[i + 1])

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

    def make_assignment(self):
        pass

    def clear(self):
        pass


class SpaceExSolverNaive(SpaceExSolver):
    def __init__(self, optimize=""):
        super(SpaceExSolver, self).__init__()

    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict):
        return self.get_max_literal(alpha, assignment, max_bound, c, optimize, z3_boolean_consts, boolean_sub_dict)

    def solve_strategy_aux(self, alpha_delta, bound, z3_boolean_consts, boolean_const_model, boolean_sub_dict):
        # solve_start = timer()
        solver = Z3Solver()
        dummy_logger = Logger()
        solver.append_logger(dummy_logger)

        solver.add(And(boolean_const_model))
        result = solver.solve()

        if not result[0]:
            assignment = solver.make_assignment()

            simplified_result = assignment.z3eval(z3_boolean_consts)

            # make_sub_dict_time = timer()

            s_abs_set = set()
            # solve_end = timer()

            if str(simplified_result) == "True":
                for c in alpha_delta:
                    b_forall, b_integral, b_zero, b_tau, b_reset, b_guard = unit_split({c}, bound)
                    if (len(b_forall) == 1 or len(b_integral) == 1 or len(b_zero) == 1 or
                            len(b_tau) == 1 or len(b_reset) == 1 or len(b_guard) == 1):
                        if str(alpha_delta[c]) == 'True' and not isinstance(c, Neq):
                            s_abs_set.add(c)

                return s_abs_set, alpha_delta

        return None, alpha_delta


class SpaceExSolverReduction(SpaceExSolver):
    def __init__(self):
        super(SpaceExSolver, self).__init__()

    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict):
        return self.get_max_literal(alpha, assignment, max_bound, c, optimize, z3_boolean_consts, boolean_sub_dict)

    def solve_strategy_aux(self, alpha_delta, bound, z3_boolean_consts, boolean_const_model, boolean_sub_dict):
        solver = Z3Solver()
        solver.set_logic('lra')
        solver.add(And(boolean_const_model))
        if not solver.solve()[0]:
            assignment = solver.make_assignment()

            simplified_result = assignment.z3eval(z3_boolean_consts)

            s_abs_set = set()

            if str(simplified_result) == "True":
                for c in alpha_delta:
                    b_forall, b_integral, b_zero, b_tau, b_reset, b_guard = unit_split({c}, bound)
                    if (len(b_forall) == 1 or len(b_integral) == 1 or len(b_zero) == 1 or
                            len(b_tau) == 1 or len(b_reset) == 1 or len(b_guard) == 1):
                        if str(alpha_delta[c]) == 'True' and not isinstance(c, Neq):
                            s_abs_set.add(c)

                return self.delta_debugging(s_abs_set, z3_boolean_consts, boolean_sub_dict), alpha_delta

        return None, alpha_delta

    def delta_debugging_aux(self, c_max: set, z3_boolean_consts, boolean_sub_dict):
        if len(c_max) == 0:
            return set()
        alpha = dict()
        boolean_const_model = list()
        for c in c_max:
            alpha[c] = BoolVal("True")
            boolean_const_model.append(boolean_sub_dict[c])

        for c in c_max:
            new_alpha = alpha.copy()
            revise_boolean_const = copy.deepcopy(boolean_const_model)
            new_alpha[c] = BoolVal("False")
            revise_boolean_const.remove(boolean_sub_dict[c])
            revise_boolean_const.append(Not(boolean_sub_dict[c]))
            solver = Z3Solver()
            solver.set_logic('lra')
            solver.add(And(revise_boolean_const))
            if not solver.solve()[0]:
                assignment = solver.make_assignment()

                simplified_result = assignment.z3eval(z3_boolean_consts)

                if str(simplified_result) == "True":
                    return self.delta_debugging_aux(c_max.difference({c}), z3_boolean_consts)

        return c_max

    def delta_debugging(self, c_max, z3_boolean_consts, boolean_sub_dict):
        s = self.delta_debugging_aux(c_max, z3_boolean_consts, boolean_sub_dict)
        return s


class SpaceExSolverUnsatCore(SpaceExSolver):
    def __init__(self):
        super(SpaceExSolver, self).__init__()
        self.builder = UnsatCoreBuilder()

    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict):
        info_dict = dict()
        info_dict["alpha"] = alpha
        info_dict["assignment"] = assignment
        info_dict["max_bound"] = max_bound
        info_dict["new_abstracted_consts"] = new_abstracted_consts
        info_dict["c"] = c
        info_dict["optimize"] = optimize
        info_dict["reduction_flag"] = self.get_optimize_flag("formula")

        self.builder.prepare(info_dict)
        return self.builder.perform()


class SpaceExAssignment(Assignment):
    def __init__(self, spaceex_counterexample):
        self.spaceex_counterexample = spaceex_counterexample

    def get_assignments(self):
        print(self.spaceex_counterexample)

    def eval(self, const):
        pass


def make_reset_pool(s_i_reset):
    s_i_pool = list()
    s_v = set()
    for c in s_i_reset:
        s_v = s_v.union(get_vars(c.left))

    s_i_r = s_i_reset
    s_diff = set()

    for v in s_v:
        s_l = set()
        for c in s_i_r:
            if c.left.id == v.id:
                s_l.add(c)
                s_diff.add(c)
        s_i_r = s_i_r.difference(s_diff)
        s_i_pool.append(s_l)

    tuple_to_set = list(product(*s_i_pool))
    s_i_pool = list()
    for i in tuple_to_set:
        chi = [element for tupl in i for element in (tupl if isinstance(tupl, tuple) else (tupl,))]
        s_i_pool.append(set(chi))

    return s_i_pool


@singledispatch
def get_string(const: Constraint):
    return {const}


@get_string.register(Variable)
def _(const: Variable):
    start_index = int(const.id.find("_"))
    return {const.id[:start_index]}


def revert_by_sigma(clauses: set, sigma: dict):
    revert_s = set()
    for c in clauses:
        if c in sigma:
            revert_s.add(sigma[c])
        else:
            revert_s.add(c)
    return revert_s


@singledispatch
def remove_index(c: Constraint) -> Variable:
    raise NotSupportedError("input should be variable type : " + str(c))


@remove_index.register(Variable)
def _(v: Variable) -> Variable:
    if "tau" not in v.id and "_" in v.id:
        start_index = v.id.find("_")
        var_id = v.id[:start_index]
        return Real(var_id)
    return v


def get_vars_from_set(set_of_list: list):
    result_set = set()
    for s in set_of_list:
        for c in s:
            result_set = result_set.union(get_vars(c))

    s_diff = set()
    for s in result_set:
        if isinstance(s, Integral):
            s_diff.add(s)
    result_set = result_set.difference(s_diff)
    return result_set


def find_index(input_list: list, v: Variable):
    index = 0
    for e in input_list:
        if e == remove_index(v).id:
            return index
        index += 1
    raise NotFoundElementError(v, "index not found")


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


def z3_bool_to_const_bool(z3list):
    return [Bool(str(b)) for b in z3list]


def get_bound(mapping_info: dict):
    max_bound = -1
    for key in mapping_info:
        # for forall
        if isinstance(key, Bool):
            if "newIntegral" in key.id:
                index = int(key.id.rfind("_")) + 1
                bound = int(key.id[index:])
                if max_bound < bound:
                    max_bound = bound
    return max_bound


def gen_sigma(s: set, op: str):
    sigma = dict()
    index = 0
    for c in s:
        v = Bool("new#" + str(index) + op)
        sigma[v] = c
        index += 1
    return sigma


def gen_net_assignment(mapping: dict, range_dict: dict):
    new_dict = dict()
    for var in mapping:
        search_index = var.id.find("_")
        search_id = var.id[:search_index]
        if not (Bool(var.id) in range_dict or Real(search_id) in range_dict or Real(
                var.id) in range_dict or "tau" in var.id):
            new_dict[var] = mapping[var]
    return new_dict


@singledispatch
def gen_fresh_new_var_map_aux(const: Constraint, id_str=None):
    raise NotSupportedError("cannot create mapping for integral and forall : " + str(const) + ", " + str(id_str))


@gen_fresh_new_var_map_aux.register(Integral)
def _(const: Integral):
    new_map = dict()
    new_map_without_and = dict()
    end_var_str = const.end_vector[0].id
    start_index = end_var_str.find('_')
    bound_str = end_var_str[start_index + 1:-2]
    new_id = "newIntegral_" + str(const.current_mode_number) + "_" + bound_str
    new_map[const] = Bool(new_id)
    new_map_without_and[const] = Bool(new_id)
    return new_map, new_map_without_and


@gen_fresh_new_var_map_aux.register(Forall)
def _(const: Forall):
    new_map = dict()
    new_map_without_and = dict()
    end_var_str = const.integral.end_vector[0].id
    start_index = end_var_str.find('_')
    bound_str = end_var_str[start_index + 1:-2]
    new_id = "newForall#" + str(id(const)) + "_" + str(const.current_mode_number) + "_" + bound_str
    new_map[const] = And([Bool(new_id), const.const])
    new_map_without_and[const] = Bool(new_id)
    return new_map, new_map_without_and


@gen_fresh_new_var_map_aux.register(Eq)
def _(const: Eq):
    new_map = dict()
    new_map_without_and = dict()
    flag = False
    # const_key is Forall object, const_value is boolean variable id
    if isinstance(const.left, Forall) or isinstance(const.right, Forall):
        flag = True
    if isinstance(const.left, Forall):
        const_key = const.left
        const_value = const.right
    else:
        const_key = const.right
        const_value = const.left

    if flag:
        new_map[const] = BoolVal("True")
    new_map_without_and[const_key] = const_value
    return new_map, new_map_without_and


def gen_fresh_new_var_map(if_set: set):
    new_map = dict()
    new_map_without_and = dict()
    for elem in if_set:
        m, nm = gen_fresh_new_var_map_aux(elem)
        new_map.update(m)
        new_map_without_and.update(nm)
    return new_map, new_map_without_and


def divide_dict(info_dict: dict):
    mode_dict = dict()
    else_dict = dict()
    for key in info_dict:
        if isinstance(key, str):
            mode_dict[key] = info_dict[key]
        else:
            else_dict[key] = info_dict[key]
    return mode_dict, else_dict


@singledispatch
def clause(const: Constraint):
    return {const}


@clause.register(Not)
def _(const: Not):
    return clause(const.child)


@clause.register(And)
def _(const: And):
    result = set()
    for c in list(const.children):
        result = result.union(clause(c))
    return result


@clause.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Formula):
        return clause(const.left).union(clause(const.right))
    return {const}


@clause.register(Or)
def _(const: Or):
    result = set()
    for c in list(const.children):
        result = result.union(clause(c))
    return result


@clause.register(Not)
def _(const: Not):
    result = set()
    return result.union(clause(const.child))


@clause.register(Implies)
def _(const):
    result = set()
    result = result.union(clause(const.left))
    result = result.union(clause(const.right))
    return result


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
