from functools import singledispatch
from typing import *

from .enumerate import *
from .static_learning import StaticLearner
from ..constraints.constraints import *
from ..constraints.operations import *
from ..objects.algorithm import Algorithm
from ..objects.configuration import Configuration
from ..objects.goal import Goal, ReachGoal
from ..objects.model import Model
from ..solver.abstract_solver import SMTSolver
from ..util.logger import Logger
from ..util.print import Printer


class SmtAlgorithm(Algorithm):
    def __init__(self):
        self.debug_name = ""

    def set_debug(self, msg: str):
        self.debug_name = msg

    def run(self, model: Model, goal: Goal, goal_prop_dict: Dict, config: Configuration,
            solver: SMTSolver, logger: Logger, printer: Printer):
        common_section = config.get_section("common")
        bound = common_section.get_value("bound")
        time_bound = common_section.get_value("time-bound")
        delta_str = common_section.get_value("threshold")
        is_only_loop = common_section.get_value("only-loop")
        underlying_solver = common_section.get_value("solver")

        total_time = 0.0
        total_size = 0
        final_result = "Unknown"
        finished_bound = bound
        delta = float(delta_str)

        goal_f = substitution(goal.get_formula(), goal_prop_dict)

        is_reach = isinstance(goal, ReachGoal)
        if is_reach:
            model.gen_reach_condition()
        else:
            model.gen_stl_condition()

        static_learner = StaticLearner(model, goal_f)
        if is_only_loop == "false":
            static_learner.generate_learned_clause(bound, delta)

        for b in range(1, int(bound) + 1):
            if is_only_loop == "true":
                if b < int(bound):
                    continue
            # start logging
            logger.reset_timer()

            model_const = model.make_consts(b)
            logger.start_timer("goal timer")
            if is_reach:
                k_step_goal = goal.k_step_consts(b, float(time_bound), delta, model, goal_prop_dict)
                time_order_const = reach_time_ordering(2 * b + 2, float(time_bound))
                stl_const = And([k_step_goal, time_order_const])
            else:
                stl_const = k_size_stl_formula(model, goal, goal_prop_dict, b, delta, float(time_bound))

            boolean_abstract = dict()
            boolean_abstract.update(model.boolean_abstract)
            boolean_abstract_consts = make_boolean_abstract_consts(boolean_abstract)
            logger.stop_timer("goal timer")
            goal_time = logger.get_duration_time("goal timer")

            if is_only_loop == "false":
                clause_in_consts = clause(And([model_const, stl_const, boolean_abstract_consts]))
                contradiction_const = static_learner.get_contradiction_upto(b, clause_in_consts)
            else:
                contradiction_const = BoolVal("True")

            if model.is_gen_reach_condition():
                total_consts = And([model_const, contradiction_const, stl_const])
                total_size = size_of_tree(total_consts)
                reduction_dict = dict()
                for mac in boolean_abstract_consts.children:
                    assert isinstance(mac, Eq)
                    reduction_dict[mac.left] = mac.right
                total_consts = substitution(total_consts, reduction_dict)
            else:
                total_consts = And([model_const, contradiction_const, stl_const, boolean_abstract_consts])
                total_size = size_of_tree(total_consts)

            solver.set_time_bound(time_bound)
            result, _ = solver.solve(total_consts, model.range_dict, boolean_abstract)

            final_result = result

            smt_time = logger.get_duration_time("solving timer")
            total_time += smt_time + goal_time

            printer.print_verbose("(bound {})".format(b))
            printer.print_verbose("  result : {}".format(result))
            printer.print_verbose("  running time : {:.5f} seconds".format(smt_time + goal_time))

            printer.print_debug("(bound {})".format(b))
            printer.print_debug("  result : {}".format(result))
            printer.print_debug("  running time : {:.5f} seconds".format(smt_time + goal_time))

            finished_bound = b
            # stop when find false
            if result == "False":
                # for reach case, we should translate the result in the opposite way
                if is_reach:
                    return "True", total_time, finished_bound, None
                assn = solver.make_assignment()
                printer.print_verbose("size : {}".format(total_size))
                return "False", total_time, finished_bound, assn.get_assignments()

            model.clear()
            goal.clear()
            solver.clear()
        printer.print_verbose("size : {}".format(total_size))
        # for reach case, we should translate the result in the opposite way
        # for now, do not make any assignment for reach case
        if is_reach:
            return "False", total_time, finished_bound, None
        return final_result, total_time, finished_bound, None


def k_size_stl_formula(model: Model, goal: Goal, goal_prop_dict, bound: int, delta: float, tau_max):
    raw_stl_formula = substitution(goal.get_formula(), goal_prop_dict)
    neg_formula = reduce_not(Not(raw_stl_formula))
    reduced_formula = remove_binary(neg_formula)
    stl_formula = relaxing(reduced_formula, delta)

    sub_formulas = calc_sub_formulas(stl_formula)

    initial_stl_f = chi(1, 1, stl_formula)
    total_stl_children = [initial_stl_f]
    total_time_children = list()

    final_f_k = None

    # depth = 2 * (bound + 1)
    max_depth = 2 * (bound + 1)
    for d in range(1, max_depth + 1):
        stl_f_d, time_f_d, final_f_d = k_depth_stl_consts(sub_formulas, d, tau_max)

        total_stl_children.append(stl_f_d)
        total_time_children.append(time_f_d)
        final_f_k = final_f_d

    assert final_f_k is not None
    time_order_const = time_ordering(max_depth, tau_max)

    path_const_children = list()
    path_const_children.extend(total_stl_children)
    path_const_children.extend(total_time_children)
    path_const_children.append(time_order_const)

    path_const = And(path_const_children)

    bools = get_bools(path_const)
    p_bools = {b.id for b in bools}
    extra_prop_path, extra_time_path = assn2path(p_bools, sub_formulas, tau_max)

    # p_chi = (or currentMode = ... (forall ...) ...)
    extra_prop_path_const = path2const(extra_prop_path, model)
    extra_time_path_const = time_path2const(extra_time_path)

    total_const_children = list()
    total_const_children.extend(path_const_children)
    total_const_children.extend([final_f_k, extra_prop_path_const])

    return And(total_const_children)


@singledispatch
def clause(const: Constraint):
    return set()


@clause.register(Lt)
def _(const: Lt):
    return {const}


@clause.register(Leq)
def _(const: Leq):
    return {const}


@clause.register(Gt)
def _(const: Gt):
    return {const}


@clause.register(Geq)
def _(const: Geq):
    return {const}


@clause.register(Eq)
def _(const: Eq):
    return {const}


@clause.register(Neq)
def _(const: Neq):
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


@clause.register(Forall)
def _(const):
    return clause(const.const)


@clause.register(Integral)
def _(const):
    return set()


@singledispatch
def get_bools(formula: Formula) -> Set[Bool]:
    return set()


@get_bools.register(Bool)
def _(formula: Bool) -> Set[Bool]:
    return {formula}


@get_bools.register(UnaryFormula)
def _(const: UnaryFormula):
    is_non_leaf = isinstance(const, NonLeaf)
    if is_non_leaf:
        return get_bools(const.child)
    else:
        return set()


@get_bools.register(BinaryFormula)
def _(const: BinaryFormula):
    is_non_leaf = isinstance(const, NonLeaf)
    if is_non_leaf:
        result = set()
        result.update(get_bools(const.left))
        result.update(get_bools(const.right))
        return result
    else:
        if isinstance(const, Eq):
            result = set()
            result.update(get_bools(const.left))
            result.update(get_bools(const.right))
            return result
        return set()


@get_bools.register(MultinaryFormula)
def _(const: MultinaryFormula):
    is_non_leaf = isinstance(const, NonLeaf)
    if is_non_leaf:
        result = set()
        for c in const.children:
            result.update(get_bools(c))
        return result
    else:
        return set()
