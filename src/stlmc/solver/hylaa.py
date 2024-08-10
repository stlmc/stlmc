import abc
import copy
from abc import ABC
from functools import singledispatch
from itertools import product

from sympy import symbols, simplify, StrictGreaterThan, GreaterThan, LessThan, StrictLessThan, Symbol, Float, Equality, \
    Unequality
from sympy.core import relational

# from hylaa import symbolic, lputil
# from hylaa.core import Core
#
# from hylaa.settings import HylaaSettings
# from hylaa.stateset import StateSet
# from hylaa.stlmc_core import HylaaRawSolver, HylaaConverter
from ..constraints.constraints import *
from ..constraints.operations import substitution, reduce_not, get_vars, infix
from ..exception.exception import NotSupportedError
from ..hybrid_automaton.hybrid_automaton import HybridAutomaton
from ..solver.abstract_solver import BaseSolver, OdeSolver
from ..solver.assignment import Assignment
from ..solver.strategy import UnsatCoreBuilder, unit_split
from ..solver.z3 import Z3Solver
from ..tree.operations import size_of_tree
from ..util.logger import Logger
from ..util.print import Printer
from ..exception.exception import *
from ..hybrid_automaton.hybrid_automaton import HybridAutomaton as StlMCHybridAutomaton
from ..hybrid_automaton.converter import AbstractConverter


class HylaaConverter(AbstractConverter):
    def __init__(self, l_v):
        self.var_set = set()
        # self.ha = HybridAutomaton('ha')
        # self.sigma = sigma
        self.l_v = l_v
        # self.max_bound = max_bound
        # self.s_integrals = s_integrals
        # self.s_foralls = s_foralls

    def _find_index(self, input_list: list, v: Variable):
        index = 0
        for e in input_list:
            if e == remove_index(v).id:
                return index
            index += 1
        raise NotFoundElementError(v, "index not found")

    #
    # def make_transition(self, s_psi_abs_i, i, mode_p, mode_n):
    #     trans_i = self.ha.new_transition(mode_p, mode_n)
    #     s_forall_i, s_integral_i, s_0, s_tau_i, s_reset_i, s_guard_i = unit_split(s_psi_abs_i, i)
    #
    #     # printer = Printer()
    #     guard_i_children = list(s_guard_i)
    #     tau_i_children = list(s_tau_i)
    #     total_children = list()
    #
    #     total_children.extend(guard_i_children)
    #     total_children.extend(tau_i_children)
    #
    #     phi_reset_children = list()
    #     for c in total_children:
    #         vs = get_vars(c)
    #         new_dict = dict()
    #         for v in vs:
    #             new_dict[v] = remove_index(v)
    #         phi_reset_children.append(reduce_not(substitution(c, new_dict)))
    #
    #     # printer.print_debug("\n\ntransition : {}".format(trans_i))
    #     # printer.print_debug("* variables : {}".format(l_v))
    #     # printer.print_debug("* guard condition : ")
    #     # for g_cond in infix(And(phi_reset_children)).split('&'):
    #     #     printer.print_debug("  * {}".format(g_cond))
    #
    #     m_guard, m_guard_rhs = symbolic.make_condition(self.l_v, infix(And(phi_reset_children)).split('&'), {},
    #                                                    has_affine_variable=True)
    #     trans_i.set_guard(m_guard, m_guard_rhs)
    #
    #     remove_var_dict = dict()
    #     for c in s_reset_i:
    #         vs = get_vars(c)
    #         for v in vs:
    #             remove_var_dict[v] = remove_index(v)
    #
    #     l_r = self.l_v.copy()
    #     for r in s_reset_i:
    #         k = self._find_index(self.l_v, r.left)
    #         l_r[k] = infix(substitution(r.right, remove_var_dict))
    #
    #     if "tau" in self.l_v:
    #         for j in range(1, self.max_bound + 1):
    #             k_t_j = self._find_index(self.l_v, Real("tau_" + str(j)))
    #             l_r[k_t_j] = "tau_" + str(j)
    #
    #     # printer.print_debug("* reset condition : {}".format(l_r))
    #
    #     reset_mat = symbolic.make_reset_mat(self.l_v, l_r, {}, has_affine_variable=True)
    #     trans_i.set_reset(reset_mat)

    def convert(self, ha: StlMCHybridAutomaton):
        hylaa_ha = HybridAutomaton(ha.name)
        new_mode_dict = dict()
        for m in ha.modes:
            new_mode = hylaa_ha.new_mode(m)
            new_mode_dict[ha.modes[m]] = new_mode
            l_integral = self.l_v.copy()

            if ha.modes[m].dynamics is not None:
                for j, v in enumerate(ha.modes[m].dynamics.vars):
                    e = ha.modes[m].dynamics.exps[j]
                    try:
                        k = self._find_index(self.l_v, v)
                        vs = get_vars(e)
                        new_dict = dict()
                        for v_elem in vs:
                            new_dict[v_elem] = remove_index(v_elem)
                        l_integral[k] = infix(substitution(e, new_dict))
                    except NotFoundElementError as ne:
                        print(ne)
                        raise NotSupportedError("element should be found!")

            m_integral = symbolic.make_dynamics_mat(self.l_v, l_integral, {}, has_affine_variable=True)
            # printer.print_debug("\n\n* variables : {} \n* integrals : {}".format(l_v, l_integral))
            new_mode.set_dynamics(m_integral)

            if ha.modes[m].invariant is not None:
                inv = ha.modes[m].invariant
                if isinstance(inv, And) and len(inv.children) > 0:
                    m_forall, m_forall_rhs = symbolic.make_condition(self.l_v, infix(inv).split('&'), {},
                                                                     has_affine_variable=True)
                    new_mode.set_invariant(m_forall, m_forall_rhs)
                else:
                    m_forall, m_forall_rhs = symbolic.make_condition(self.l_v, infix(inv), {},
                                                                     has_affine_variable=True)
                    new_mode.set_invariant(m_forall, m_forall_rhs)

        # transition
        for i, t in enumerate(ha.trans):
            print("{} , {} -> {}".format(t, new_mode_dict[ha.trans[t].src].name, new_mode_dict[ha.trans[t].trg].name))

            new_trans = hylaa_ha.new_transition(new_mode_dict[ha.trans[t].src], new_mode_dict[ha.trans[t].trg])
            if ha.trans[t].guard is not None:
                m_guard, m_guard_rhs = symbolic.make_condition(self.l_v, infix(ha.trans[t].guard).split('&'), {},
                                                               has_affine_variable=True)
                new_trans.set_guard(m_guard, m_guard_rhs)

            if ha.trans[t].reset is not None:
                reset = ha.trans[t].reset
                l_r = self.l_v.copy()
                if isinstance(reset, And) and len(reset.children) > 0:
                    for r in reset.children:
                        if isinstance(r, Eq) and isinstance(r.left, Variable):
                            try:
                                k = self._find_index(self.l_v, r.left)
                                l_r[k] = infix(r.right)
                            except NotFoundElementError as ne:
                                print(ne)
                                raise NotSupportedError("element should be found!")

                reset_mat = symbolic.make_reset_mat(self.l_v, l_r, {}, has_affine_variable=True)
                new_trans.set_reset(reset_mat)
        return hylaa_ha


class HylaaRawSolver:
    def __init__(self):
        self.result = None

    def run(self, ha: HybridAutomaton, new_bound_box_list):
        mode = ha.modes['mode0']
        init_lpi = lputil.from_box(new_bound_box_list, mode)
        init_list = [StateSet(init_lpi, mode)]
        settings = HylaaSettings(0.1, 100)
        # settings.stop_on_aggregated_error = False
        settings.aggstrat.deaggregate = True  # use deaggregationboolean_abstract_dict
        # settings.stdout = HylaaSettings.STDOUT_VERBOSE
        core = Core(ha, settings)
        ce = core.run(init_list)

        self.result = core.is_counterexample


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


# builder class for hylaa
class HylaaStrategy:

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


class HylaaSolver(OdeSolver, HylaaStrategy, ABC):
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
        if not HylaaSolver().time_optimize:
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
                                                                      c, HylaaSolver().time_optimize, z3_boolean_consts,
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

            '''
            is_reach = False
            min_bound = 1000000
            cur_min_bound = 1000000
            print("new_alpha")
            print(new_alpha)
            print(max_literal_set_list)

            remove_mode_clauses = list()
            for clause_bound in max_literal_set_list:
                s_diff = set()
                for elem in clause_bound:
                    if isinstance(elem, Bool):
                        if "reach_goal_" in elem.id:
                            is_reach = True
                            s_diff.add(elem)
                            index = elem.id.rfind("_")
                            cur_min_bound = int(elem.id[index+1:])
                            if cur_min_bound < min_bound:
                                min_bound = cur_min_bound
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

            remove_reach_clauses = list()

            if is_reach:
                remove_reach_clauses = list()
                for clause_bound in max_literal_set_list:
                    s_diff = set()
                    for elem in clause_bound:
                        print("elem : " + str(elem) +", " + str(get_max_bound(elem)))

                        if get_max_bound(elem) > min_bound:
                            s_diff.add(elem)
                    clause_bound = clause_bound.difference(s_diff)
                    print("cur min bound : " + str(min_bound))
                    print(s_diff)
                    remove_reach_clauses.append(clause_bound)
                max_literal_set_list = remove_reach_clauses
                max_bound = min_bound
                print("result")
                print(max_literal_set_list)
            '''

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
            l_mode.append(make_mode_property(s_integral[i], s_forall[i], i, max_bound, l_v, ha, sigma))

        l_mode.append(ha.new_mode("error"))

        for i in range(max_bound + 1):
            make_transition(s_f_list[i], i, max_bound, l_v, ha, l_mode[i], l_mode[i + 1])

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
            if ("tau" in t) or (HylaaSolver().time_optimize and "timeStep" in t):
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
        new_bound_box_list.append([1.0, 1.0])
        printer.print_debug("* bound : ")
        printer.print_debug(new_bound_box_list)

        hc = HylaaConverter(l_v)
        new_ha = hc.convert(ha)

        hrs = HylaaRawSolver()
        hrs.run(new_ha, new_bound_box_list)
        # self.add_log_info(str(ce.counterexample))
        if hrs.result:
            # self.hylaa_core = core
            return False
        else:
            return True

    def make_assignment(self):
        if self.hylaa_core is not None:
            return HylaaAssignment(self.hylaa_core.get_counterexample())
        return HylaaAssignment(None)

    def clear(self):
        pass


class HylaaSolverNaive(HylaaSolver):
    def __init__(self, optimize=""):
        super(HylaaSolver, self).__init__()

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


class HylaaSolverReduction(HylaaSolver):
    def __init__(self):
        super(HylaaSolver, self).__init__()

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


class HylaaSolverUnsatCore(HylaaSolver):
    def __init__(self):
        super(HylaaSolver, self).__init__()
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


class HylaaAssignment(Assignment):
    def __init__(self, hylaa_counterexample):
        self.hylaa_counterexample = hylaa_counterexample

    def get_assignments(self):
        print(self.hylaa_counterexample)

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
def sympy_var(expr: relational):
    raise NotSupportedError("cannot make box : " + str(expr))


@sympy_var.register(Symbol)
def _(expr: Symbol):
    return expr


@singledispatch
def sympy_value(expr: relational):
    raise NotSupportedError("cannot make box : " + str(expr))


@sympy_value.register(Float)
def sympy_value(expr: Float):
    return expr


@singledispatch
def expr_to_sympy(const: Constraint):
    raise NotSupportedError("cannot make it canonical : " + str(const))


@expr_to_sympy.register(Variable)
def _(const: Variable):
    return symbols(const.id)


@expr_to_sympy.register(Constant)
def _(const: Constant):
    return float(const.value)


@expr_to_sympy.register(Add)
def _(const: Add):
    return expr_to_sympy(const.left) + expr_to_sympy(const.right)


@expr_to_sympy.register(Sub)
def _(const: Sub):
    return expr_to_sympy(const.left) - expr_to_sympy(const.right)


@expr_to_sympy.register(Mul)
def _(const: Mul):
    return expr_to_sympy(const.left) * expr_to_sympy(const.right)


@expr_to_sympy.register(Div)
def _(const: Div):
    return expr_to_sympy(const.left) / expr_to_sympy(const.right)


@expr_to_sympy.register(Pow)
def _(const: Pow):
    return expr_to_sympy(const.left) ** expr_to_sympy(const.right)


@expr_to_sympy.register(Gt)
def _(const: Gt):
    return StrictGreaterThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Geq)
def _(const: Geq):
    return GreaterThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Lt)
def _(const: Lt):
    return StrictLessThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Leq)
def _(const: Leq):
    return LessThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Eq)
def _(const: Eq):
    return Equality(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Neq)
def _(const: Neq):
    return Unequality(expr_to_sympy(const.left), expr_to_sympy(const.right))


@singledispatch
def remove_index(c: Constraint) -> Variable:
    raise NotSupportedError("input should be variable type : " + str(c))


@remove_index.register(Variable)
def _(v: Variable) -> Variable:
    if "tau" not in v.id:
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
    # mode_i = ha.new_mode("mode" + str(i))
    # l_integral = l_v.copy()
    #
    # for integral in s_integral_i:
    #     index = 0
    #     for exp in sigma[integral].dynamics.exps:
    #         try:
    #             k = find_index(l_v, sigma[integral].dynamics.vars[index])
    #             l_integral[k] = infix(exp)
    #             index += 1
    #         except NotFoundElementError as ne:
    #             print(ne)
    #             raise NotSupportedError("element should be found!")
    #
    # for j in range(1, i + 1):
    #     k_j = find_index(l_v, Real("tau_" + str(j)))
    #     l_integral[k_j] = "0"
    #
    # for j in range(i + 1, max_bound + 2):
    #     k_j = find_index(l_v, Real("tau_" + str(j)))
    #     l_integral[k_j] = "1"
    #
    # if optimize:
    #     l_integral[-1] = "1"
    #
    # printer.print_debug("\n\nmode : {}".format(mode_i.name))
    # m_integral = symbolic.make_dynamics_mat(l_v, l_integral, {}, has_affine_variable=True)
    # printer.print_debug("\n\n* variables : {} \n* integrals : {}".format(l_v, l_integral))
    # mode_i.set_dynamics(m_integral)
    #
    # phi_forall_children = list()
    # for c in s_forall_i:
    #     new_c = substitution(c, sigma)
    #     vs = get_vars(new_c)
    #     new_dict = dict()
    #     for v in vs:
    #         new_dict[v] = remove_index(v)
    #     phi_forall_children.append(reduce_not(substitution(new_c, new_dict)))
    # printer.print_debug("* invariants : {}".format(infix(And(phi_forall_children))))
    #
    # if len(phi_forall_children) > 0:
    #     m_forall, m_forall_rhs = symbolic.make_condition(l_v, infix(And(phi_forall_children)).split('&'), {},
    #                                                      has_affine_variable=True)
    #     mode_i.set_invariant(m_forall, m_forall_rhs)
    #
    # return mode_i


def make_transition(s_psi_abs_i, i, max_bound, l_v, ha: HybridAutomaton, mode_p, mode_n):
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
    # trans_i = ha.new_transition(mode_p, mode_n)
    # s_forall_i, s_integral_i, s_0, s_tau_i, s_reset_i, s_guard_i = unit_split(s_psi_abs_i, i)
    #
    # printer = Printer()
    # guard_i_children = list(s_guard_i)
    # tau_i_children = list(s_tau_i)
    # total_children = list()
    #
    # total_children.extend(guard_i_children)
    # total_children.extend(tau_i_children)
    #
    # phi_reset_children = list()
    # for c in total_children:
    #     vs = get_vars(c)
    #     new_dict = dict()
    #     for v in vs:
    #         new_dict[v] = remove_index(v)
    #     phi_reset_children.append(reduce_not(substitution(c, new_dict)))
    #
    # printer.print_debug("\n\ntransition : {}".format(trans_i))
    # printer.print_debug("* variables : {}".format(l_v))
    # printer.print_debug("* guard condition : ")
    # for g_cond in infix(And(phi_reset_children)).split('&'):
    #     printer.print_debug("  * {}".format(g_cond))
    #
    # m_guard, m_guard_rhs = symbolic.make_condition(l_v, infix(And(phi_reset_children)).split('&'), {},
    #                                                has_affine_variable=True)
    # trans_i.set_guard(m_guard, m_guard_rhs)
    #
    # remove_var_dict = dict()
    # for c in s_reset_i:
    #     vs = get_vars(c)
    #     for v in vs:
    #         remove_var_dict[v] = remove_index(v)
    #
    # l_r = l_v.copy()
    # for r in s_reset_i:
    #     k = find_index(l_v, r.left)
    #     l_r[k] = infix(substitution(r.right, remove_var_dict))
    #
    # if "tau" in l_v:
    #     for j in range(1, max_bound + 1):
    #         k_t_j = find_index(l_v, Real("tau_" + str(j)))
    #         l_r[k_t_j] = "tau_" + str(j)
    #
    # printer.print_debug("* reset condition : {}".format(l_r))
    #
    # reset_mat = symbolic.make_reset_mat(l_v, l_r, {}, has_affine_variable=True)
    # trans_i.set_reset(reset_mat)


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


# def unit_split(given_set: set, i: int):
#     forall_set = set()
#     integral_set = set()
#     tau_set = set()
#     guard_set = set()
#     reset_set = set()
#     init_set = set()
#
#     s_diff = set()
#
#     for c in given_set:
#         if isinstance(c, Not):
#             s_diff.add(c)
#
#     given_set = given_set.difference(s_diff)
#
#     for c in given_set:
#         var_set = get_vars(c)
#         if len(var_set) == 1:
#             for var in var_set:
#                 start_index = int(var.id.find("_"))
#                 if var.id[start_index:] == "_0_0" and "newTau" not in var.id and "newIntegral" not in var.id and "invAtomicID" not in var.id:
#                     init_set.add(c)
#                     s_diff.add(c)
#                     break
#
#     given_set = given_set.difference(s_diff)
#     s_diff = set()
#
#     for c in given_set:
#         var_set = get_vars(c)
#         for var in var_set:
#             start_index = int(var.id.find("#"))
#             s_index = int(var.id.find("_"))
#             e_index = int(var.id.rfind("_"))
#             bound_index = int(var.id.rfind("_"))
#             if not (s_index == -1) and ((s_index == e_index and "tau" not in var.id)
#                                         or ("invAtomicID" in var.id) or ("newPropDecl" in var.id)):
#                 bound = int(var.id[bound_index + 1:])
#                 if i == bound:
#                     forall_set.add(c)
#                     s_diff.add(c)
#                     break
#             elif var.id[:start_index] == "newIntegral":
#                 bound = int(var.id[bound_index + 1:])
#                 if i == bound:
#                     integral_set.add(c)
#                     s_diff.add(c)
#                     break
#
#     given_set = given_set.difference(s_diff)
#     s_diff = set()
#
#     for c in given_set:
#         var_set = get_vars(c)
#         max_bound = -1
#         for var in var_set:
#             start_index = int(var.id.find("_"))
#             if var.id[:start_index] == "tau":
#                 bound = int(var.id[start_index + 1:])
#                 if max_bound < bound:
#                     max_bound = bound
#         if (max_bound == 0 and i == 0) or (max_bound != -1 and max_bound == i + 1):
#             tau_set.add(c)
#             s_diff.add(c)
#         elif isinstance(c, Bool):
#             if "newTau#" in c.id and int(c.id[-1]) == i:
#                 tau_set.add(c)
#                 s_diff.add(c)
#
#     given_set = given_set.difference(s_diff)
#     s_diff = set()
#
#     for c in given_set:
#         if isinstance(c, Eq):
#             if isinstance(c.left, Variable):
#                 start_index = int(c.left.id.find("_"))
#                 end_index = int(c.left.id.rfind("_"))
#                 if start_index < end_index:
#                     bound = int(c.left.id[start_index + 1:end_index])
#                     if c.left.id[end_index + 1:] == "0" and bound == i + 1:
#                         reset_set.add(c)
#                         s_diff.add(c)
#
#     given_set = given_set.difference(s_diff)
#     s_diff = set()
#
#     for c in given_set:
#         var_set = get_vars(c)
#         flag = True
#         for var in var_set:
#             start_index = int(var.id.find("_"))
#             s_index = int(var.id.find("_"))
#             e_index = int(var.id.rfind("_"))
#             end_index = int(var.id.rfind("_"))
#             if not (s_index == e_index or "newIntegral" in var.id or "invAtomicID" in var.id
#                     or "newPropDecl" in var.id or "newTau" in var.id):
#                 bound = int(var.id[start_index + 1:end_index])
#                 last_str = var.id[-1]
#                 if not ((bound == i and last_str == "t") or (bound == i + 1 and last_str == "0")):
#                     flag = False
#                 if isinstance(c.left, Real):
#                     if c.left.id[e_index + 1:] == "0":
#                         flag = False
#                         break
#             else:
#                 flag = False
#         if flag:
#             guard_set.add(c)
#             s_diff.add(c)
#
#     return forall_set, integral_set, init_set, tau_set, reset_set, guard_set


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
