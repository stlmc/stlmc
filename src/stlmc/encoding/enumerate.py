import concurrent.futures
import time
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, ProcessPoolExecutor
from functools import reduce
from typing import *

from ..objects.algorithm import *
# from .algorithm import ParallelAlgRunner
from ..objects.algorithm import *
from ..objects.configuration import Configuration
from ..objects.goal import Goal, ReachGoal
from ..objects.model import Model
from ..solver.dreal import dRealSolver, DrealAssignment
from ..solver.z3 import *
from ..util.logger import Logger
from ..util.print import Printer


class EnumerateAlgorithm(Algorithm):
    def __init__(self):
        self.scenario_solver = z3.SolverFor("QF_LRA")
        self.minimize_solver = z3.SolverFor("QF_LRA")
        self.minimize_solver.set(":core.minimize", True)

        self.clause_set: Set[Formula] = set()
        self.run_queue = set()
        self.runner = None
        self.debug_name = ""
        self.loop_mode = False

    def clear(self):
        self.scenario_solver = z3.SolverFor("QF_LRA")
        self.minimize_solver = z3.SolverFor("QF_LRA")
        self.minimize_solver.set(":core.minimize", True)
        self.clause_set.clear()

    def set_debug(self, msg: str):
        self.debug_name = msg

    def run(self, model: Model, goal: Goal, goal_prop_dict: Dict, config: Configuration,
            solver: SMTSolver, logger: Logger, printer: Printer):
        total_time = 0.0
        total_size = 0
        common_section = config.get_section("common")
        bound = common_section.get_value("bound")
        time_bound = common_section.get_value("time-bound")
        delta = common_section.get_value("threshold")
        loop = "false"

        parallel = common_section.get_value("parallel")

        if self.runner is None:
            if parallel == "true":
                self.runner = ParallelAlgRunner(25)
            else:
                self.runner = NormalRunner()

        assert self.runner is not None

        self.clear()

        self.loop_mode = True if loop == "on" else False

        model.boolean_abstract.clear()

        final_result = "Unknown"
        finished_bound = bound

        # depth = int(bound) * 2
        tau_max = float(time_bound)

        is_reach = isinstance(goal, ReachGoal)
        if is_reach:
            model.gen_reach_condition()
        else:
            model.gen_stl_condition()

        if not is_reach:
            raw_stl_formula = substitution(goal.get_formula(), goal_prop_dict)
            neg_formula = reduce_not(Not(raw_stl_formula))
            reduced_formula = remove_binary(neg_formula)
            stl_formula = relaxing(reduced_formula, float(delta))

            sub_formulas = calc_sub_formulas(stl_formula)

            initial_stl_f = chi(1, 1, stl_formula)
        else:
            initial_stl_f = BoolVal("True")
            sub_formulas = set()

        initial_model_f, initial_track_const = model.init_consts()

        self.scenario_solver.add(z3Obj(initial_stl_f))
        self.scenario_solver.add(z3Obj(initial_model_f))
        self.scenario_solver.add(z3Obj(initial_track_const))
        self.minimize_solver.add(
            z3Obj(Not(And([initial_model_f, initial_stl_f, initial_track_const, Bool("unsat@0")]))))
        self.minimize_solver.push()
        self.minimize_solver.add(z3Obj(Bool("unsat@0")))

        self.clause_set.update(clause(And([initial_model_f, initial_stl_f, initial_track_const])))

        # stl
        stl_consts = []
        stl_time_consts = []

        # model
        model_consts = []
        model_track_consts = []

        # bound is the number of jumps
        # starts from 0
        # [ 0 ... bound ]
        for b in range(0, int(bound) + 1):

            # generate model consts
            model_f_k, track_f_k = model.k_step_consts(b)
            model_f_k_final, track_f_k_final = model.k_step_consts(b, is_final=True)
            model_consts.append(model_f_k)
            model_track_consts.append(track_f_k)

            if not is_reach:
                stl_f_k_children = list()
                stl_f_k_time_children = list()
                final_f_k = None

                # corresponding stl depth
                # b -> 2 * b + 1 and 2 * b + 2
                for d in range(2 * b + 1, 2 * b + 3):
                    # print("bound: {}, depth: [ {} ]".format(b, d))
                    stl_f_d, time_f_d, final_f_d = k_depth_stl_consts(sub_formulas, d, tau_max)

                    stl_f_k_children.append(stl_f_d)
                    stl_f_k_time_children.append(time_f_d)
                    final_f_k = final_f_d

                time_order_const = time_ordering(2 * b + 2, tau_max)

                assert final_f_k is not None
                stl_f_k = And(stl_f_k_children)
                time_f_k = And(stl_f_k_time_children)

                stl_consts.append(stl_f_k)
                stl_time_consts.append(time_f_k)
            else:
                stl_f_k = BoolVal("True")
                time_f_k = BoolVal("True")
                stl_consts.append(BoolVal("True"))
                stl_time_consts.append(BoolVal("True"))
                time_order_const = reach_time_ordering(2 * b + 2, tau_max)
                final_f_k = goal.k_step_consts(b, float(time_bound), delta, model, goal_prop_dict)
            result, result_model, scenario_time = self.scenario_check(model, b, tau_max, sub_formulas,
                                                                      model_consts, stl_consts, stl_time_consts,
                                                                      model_f_k_final, final_f_k, time_order_const,
                                                                      solver)

            finished_bound = b
            total_size = acc_size(model_consts)
            total_size += acc_size(stl_consts)
            total_size += acc_size(stl_time_consts)
            total_size += acc_size(model_track_consts)
            total_size += size_of_tree(stl_f_k)
            total_size += size_of_tree(time_f_k)
            total_size += size_of_tree(time_order_const)
            total_size += size_of_tree(final_f_k)
            total_time += scenario_time
            # found counter example
            if result:
                printer.print_verbose("total loop : {}".format(self.runner.number))
                printer.print_verbose("size : {}".format(total_size))
                return "False", total_time, finished_bound, result_model.get_assignments()

            if not self.loop_mode:
                runner_result, runner_model = self.runner.wait_and_check_sat()
                if runner_result:
                    printer.print_verbose("total loop : {}".format(self.runner.number))
                    printer.print_verbose("size : {}".format(total_size))
                    return "False", self.runner.time, finished_bound, runner_model.get_assignments()
        printer.print_verbose("total loop : {}".format(self.runner.number))
        printer.print_verbose("size : {}".format(total_size))
        return "True", total_time, finished_bound, None

    # accumulated
    def scenario_check(self, model: Model, bound: int, tau_max, sub_formulas: Set[Formula],
                       acc_model: List[Formula], acc_stl: List[Formula], acc_stl_time: List[Formula],
                       model_f_k_final: Formula, stl_final: Formula, stl_time_order: Formula,
                       smt_solver: SMTSolver, is_generalized=True):
        total_time = 0.0
        print("bound: {}".format(bound))

        k_model_f = acc_model[bound]
        k_stl_f = acc_stl[bound]
        k_stl_time_f = acc_stl_time[bound]

        cur_minimize_var = Bool("unsat@{}".format(bound))
        next_minimize_var = Bool("unsat@{}".format(bound + 1))

        current_minimize_info = Eq(cur_minimize_var, And([model_f_k_final, k_stl_f, k_stl_time_f,
                                                          stl_time_order, next_minimize_var]))

        self.minimize_solver.pop()
        self.minimize_solver.push()
        self.minimize_solver.add(z3Obj(current_minimize_info))
        self.minimize_solver.add(z3Obj(next_minimize_var))

        # n_symbolic_path: final, n_symbolic_path_next: non-final
        n_symbolic_path = And([model_f_k_final, k_stl_f, k_stl_time_f, stl_time_order])
        n_symbolic_path_next = And([k_model_f, k_stl_f, k_stl_time_f])

        self.clause_set.update(clause(n_symbolic_path_next))
        self.clause_set.update(clause(n_symbolic_path))

        contra_v_const, contra_e_const = contradiction_gen(self.clause_set, sub_formulas)
        contra_v_inv = contradiction_gen_inv(model.boolean_abstract)

        self.scenario_solver.push()
        self.scenario_solver.add(z3Obj(n_symbolic_path))
        self.scenario_solver.add(z3Obj(stl_final))
        self.scenario_solver.add(z3Obj(contra_v_const))
        self.scenario_solver.add(z3Obj(contra_e_const))
        self.scenario_solver.add(z3Obj(contra_v_inv))

        true = BoolVal("True")
        false = BoolVal("False")
        counter = 0
        while True:
            scenario_s = time.time()
            result = self.scenario_solver.check()
            scenario_e = time.time()
            total_time += scenario_e - scenario_s
            # sat, find counterexample
            if result.r == z3.Z3_L_TRUE:
                m = self.scenario_solver.model()
                assn = Z3Assignment(m)
                assn_dict = assn.get_assignments()

                # pop final and time ordering constraints
                if is_generalized:
                    self.minimize_solver.push()

                    real_set = set()
                    neg_dict: Dict[str, Eq] = dict()
                    for v in assn_dict:
                        valuation = assn_dict[v]
                        if isinstance(v, Bool) and isinstance(valuation, BoolVal):
                            track_id = "p@{}".format(v.id)
                            if valuation == true:
                                neg_dict[track_id] = Eq(v, false)
                                self.minimize_solver.assert_and_track(z3Obj(Eq(v, true)), track_id)
                            else:
                                self.minimize_solver.add(z3Obj(Eq(v, false)))
                        else:
                            assert isinstance(v, Real) or isinstance(v, Int)
                            real_set.add(v)

                    real_dict = dict()
                    for c in self.clause_set:
                        c_vars = get_vars(c)
                        if c_vars.intersection(real_set):
                            track_id = "p@real_{}".format(id(c))
                            if m.eval(z3Obj(c)):
                                real_dict[track_id] = c
                                self.minimize_solver.assert_and_track(z3Obj(Eq(c, true)), track_id)
                            else:
                                self.minimize_solver.add(z3Obj(Eq(c, false)))

                    minimize_s = time.time()
                    self.minimize_solver.check()
                    minimize_e = time.time()
                    total_time += minimize_e - minimize_s

                    unsat_cores = self.minimize_solver.unsat_core()

                    # remove tracking infos
                    self.minimize_solver.pop()
                    picked_unsat_cores = {str(unsat_core) for unsat_core in unsat_cores}
                    p_reals = picked_unsat_cores.difference(set(neg_dict.keys()))
                    p_bools = picked_unsat_cores.difference(p_reals)

                    # pick time and propositions
                    # remove intermediate goals
                    p_bools = pick_time_and_props(p_bools, sub_formulas)
                    path_bool_consts = {Bool(p_bool.replace("p@", "")) for p_bool in p_bools}
                    path_real_consts = list(map(lambda p: real_dict[p],
                                                filter(lambda p: p in real_dict, [p_real for p_real in p_reals])))

                    path_const_children = list()
                    path_const_children.extend(path_bool_consts)
                    path_const_children.extend(path_real_consts)

                    path_const = And(path_const_children)

                    model_abstract_const = And([Eq(v, model.boolean_abstract[v]) for v in model.boolean_abstract])
                    extra_prop_path, extra_time_path = assn2path(p_bools, sub_formulas, tau_max)
                    # p_chi = (or currentMode = ... (forall ...) ...)
                    extra_prop_path_const = path2const(extra_prop_path, model)
                    extra_time_path_const = time_path2const(extra_time_path)

                    # to avoid omitting range consts due to unsat core
                    range_consts = list(map(lambda t: t[0], [model.make_range_consts(d) for d in range(0, bound + 1)]))
                    range_const = And(range_consts)

                    # total_const = And([path_const, stl_acc_time, range_const, model_abstract_const])
                    if model.is_gen_reach_condition():
                        total_const = And([path_const, extra_prop_path_const, stl_final,
                                           extra_time_path_const, range_const])

                        reduction_dict = dict()
                        for mac in model_abstract_const.children:
                            assert isinstance(mac, Eq)
                            reduction_dict[mac.left] = mac.right
                        total_const = substitution(total_const, reduction_dict)
                    else:
                        total_const = And([path_const, extra_prop_path_const, stl_final,
                                           extra_time_path_const, range_const,
                                           model_abstract_const])

                    if not self.loop_mode:
                        self.runner.set_debug(self.debug_name)
                        self.runner.run(smt_solver, total_const)
                        runner_result, runner_model = self.runner.check_sat()
                        if runner_result:
                            return True, runner_model, self.runner.time

                    generalized_symbolic_path = Not(path_const)
                    self.scenario_solver.add(z3Obj(generalized_symbolic_path))
                    counter += 1

                else:
                    # w/o generalize
                    # TODO:
                    concrete_symbolic_path = Or([neg_dict[track_id] for track_id in neg_dict])
                    self.scenario_solver.add(z3Obj(concrete_symbolic_path))
            if result.r == z3.Z3_L_FALSE:
                break

        self.scenario_solver.pop()
        self.scenario_solver.add(z3Obj(n_symbolic_path_next))
        self.minimize_solver.pop()
        self.minimize_solver.add(z3Obj(Eq(cur_minimize_var, And([k_model_f, k_stl_f, k_stl_time_f,
                                                                 next_minimize_var]))))
        self.minimize_solver.push()
        self.minimize_solver.add(z3Obj(next_minimize_var))

        print("# bound: {}, {}".format(bound, counter))
        return False, None, self.runner.time


def k_depth_stl_consts(sub_formulas: Set[Formula], depth: int, tau_max: float) -> Tuple[Formula, Formula, Formula]:
    left_time = is_left_time(sub_formulas)
    right_time = is_right_time(sub_formulas)

    # calculate time condition
    sup_i = symbolic_sup(depth)
    inf_i_next = symbolic_inf(depth + 1) if depth % 2 == 1 else symbolic_sup(depth + 1)

    # depth odd : closed interval (point []), depth even : open interval ()

    t_l_i = Bool("T^{}_l".format(depth))
    t_r_i = Bool("T^{}_r".format(depth))

    left_time_intersect = sup_i < RealVal(str(tau_max)) if depth % 2 == 1 else sup_i <= RealVal(str(tau_max))
    right_time_intersect = inf_i_next >= RealVal(str(tau_max))

    time_const_left = Eq(t_l_i, left_time_intersect)
    time_const_right = Eq(t_r_i, right_time_intersect)

    time_consts = set()
    if left_time:
        time_consts.add(time_const_left)
    if right_time:
        time_consts.add(time_const_right)

    goal_consts = set()
    for f in sub_formulas:
        is_globally = isinstance(f, GloballyFormula)
        is_finally = isinstance(f, FinallyFormula)
        if is_proposition(f):
            continue

        if is_finally or is_globally:
            goal_consts.update({symbolic_goal(f, i, depth, tau_max) for i in range(1, depth + 1)})

            if is_globally:
                time_consts.update(globally_time_const(depth, f))

            if is_finally:
                time_consts.update(finally_time_const(depth, f))

        else:
            goal_consts.add(symbolic_goal(f, depth, depth, tau_max))

    goal_const = And(list(goal_consts))
    time_const = And(list(time_consts))
    final_const = And([final(f, depth) for f in sub_formulas])

    return goal_const, time_const, final_const


def calc_sub_formulas(formula: Formula) -> Set[Formula]:
    sub_formulas = sub_formula(formula)
    new_formulas: Set[GloballyFormula] = set()

    for f in sub_formulas:
        if isinstance(f, FinallyFormula):
            local_time = Interval(True, RealVal("0.0"), False, f.local_time.left)
            new_formulas.add(GloballyFormula(local_time, f.global_time, f.child))
    return sub_formulas.union(new_formulas)


def is_left_time(sub_formulas: Set[Formula]):
    for f in sub_formulas:
        if isinstance(f, UntilFormula) or isinstance(f, FinallyFormula):
            return True
    return False


def is_right_time(sub_formulas: Set[Formula]):
    for f in sub_formulas:
        if isinstance(f, ReleaseFormula) or isinstance(f, GloballyFormula):
            return True
    return False


def chi(i: int, k: int, f: Formula):
    return Bool("chi^{{{},{}}}_{}".format(i, k, hash(f)))


def t1(i: int, k: int, f: Formula):
    return Bool("T1^{{{},{}}}_{}".format(i, k, hash(f)))


def t2(i: int, k: int, f: Formula):
    return Bool("T2^{{{},{}}}_{}".format(i, k, hash(f)))


def t3(i: int, k: int, f: Formula):
    return Bool("T3^{{{},{}}}_{}".format(i, k, hash(f)))


# sup(J_i)
def symbolic_sup(index: int) -> Real:
    # odd : [ \tau_{(i - 1) / 2}, \tau_{(i - 1) / 2} ]
    # even : ( \tau_{i / 2 - 1}, \tau_{i / 2} )
    tau_index = index / 2
    if index % 2 == 1:
        tau_index = (index - 1) / 2
    return Real("tau_{}".format(int(tau_index)))


# inf(J_i)
def symbolic_inf(index: int) -> Real:
    # odd : [ \tau_{(i - 1) / 2}, \tau_{(i - 1) / 2} ]
    # even : ( \tau_{i / 2 - 1}, \tau_{i / 2} )
    tau_index = index / 2 - 1
    if index % 2 == 1:
        tau_index = (index - 1) / 2
    return Real("tau_{}".format(int(tau_index)))


# final const
def final(f: Formula, depth: int):
    # chi^{{i, depth + 1}}_{f} = false
    # i \in [ 1 ... depth + 1 ]
    return And([Eq(chi(i, depth + 1, f), BoolVal("False")) for i in range(1, depth + 2)])


def symbolic_goal(f: Formula, i: int, d: int, tau_max):
    # if isinstance(f, Bool):
    #     assert i == d
    #     return None

    if isinstance(f, And):
        assert i == d
        # assert len(f.children) == 2
        left = chi(i, d, f)
        right = And([chi(i, i, child) for child in f.children])
        return Eq(left, right)

    if isinstance(f, Or):
        assert i == d
        # assert len(f.children) == 2
        left = chi(i, d, f)
        right = Or([chi(i, i, child) for child in f.children])
        return Eq(left, right)

    if isinstance(f, UntilFormula):
        assert i == d
        left = chi(i, i, f)
        right = Or([And([chi(i, i, f.left), chi(i, i, f.right), Bool("T^{}_l".format(i))]),
                    And([chi(i, i, f.left), chi(i + 1, i + 1, f)])])
        return Eq(left, right)

    if isinstance(f, ReleaseFormula):
        assert i == d
        left = chi(i, i, f)
        right = Or([chi(i, i, f.left),
                    And([chi(i, i, f.right), Bool("T^{}_r".format(i))]),
                    And([chi(i, i, f.right), chi(i + 1, i + 1, f)])])
        return Eq(left, right)

    if isinstance(f, GloballyFormula):
        left = chi(i, d, f)
        right = Or([And([t1(i, d, f), chi(i, d + 1, f)]), t2(i, d, f),
                    And([chi(d, d, f.child), chi(i, d + 1, f)]),
                    And([t1(i, d, f), Bool("T^{}_r".format(d))]),
                    And([t2(i, d, f), Bool("T^{}_r".format(d))]),
                    And([chi(d, d, f.child), Bool("T^{}_r".format(d))])])
        return Eq(left, right)

    if isinstance(f, FinallyFormula):
        new_interval = Interval(True, RealVal("0.0"), False, f.local_time.left)
        left = chi(i, d, f)
        right = Or([And([t3(i, d, f), chi(d, d, f.child),
                         chi(i, d, GloballyFormula(new_interval, f.global_time, f.child)),
                         Bool("T^{}_l".format(d))]),
                    chi(i, d + 1, f)])
        return Eq(left, right)

    raise NotSupportedError("cannot find related rule")


def globally_time_const(depth: int, f: Formula) -> Set[Formula]:
    assert isinstance(f, GloballyFormula)

    consts = set()

    sup_k = symbolic_sup(depth)
    inf_k = symbolic_inf(depth)

    sup_formula = f.local_time.right
    inf_formula = f.local_time.left
    J = f.local_time

    # 1 ... depth
    for i in range(1, depth + 1):
        sup_i = symbolic_sup(i)
        inf_i = symbolic_inf(i)

        t_1 = t1(i, depth, f)
        t_2 = t2(i, depth, f)

        add_left_close = True if depth % 2 == 1 and J.left_end else False
        add_right_close = True if depth % 2 == 1 and J.right_end else False

        left_jk_locate = Lt(sup_k, Add(inf_i, inf_formula)) if depth % 2 == 1 and add_left_close else Leq(sup_k,
                                                                                                          Add(inf_i,
                                                                                                              inf_formula))
        right_jk_locate = Gt(inf_k, Add(sup_i, sup_formula)) if depth % 2 == 1 and add_right_close else Geq(inf_k,
                                                                                                            Add(sup_i,
                                                                                                                sup_formula))

        const1 = Eq(t_1, left_jk_locate)
        const2 = Eq(t_2, right_jk_locate)

        consts.add(const1)
        consts.add(const2)
    return consts


def finally_time_const(depth: int, f: Formula) -> Set[Formula]:
    assert isinstance(f, FinallyFormula)

    consts = set()
    inf_k = symbolic_inf(depth)
    # 1 ... depth

    kl_interval = True if depth % 2 == 1 and f.local_time.right_end else False

    for i in range(1, depth + 1):
        inf_i = symbolic_inf(i)

        sup_formula = f.local_time.right
        t_3 = t3(i, depth, f)

        time_cond = Lt(Sub(inf_k, sup_formula), inf_i) if (not kl_interval) and i % 2 == 1 else Leq(
            Sub(inf_k, sup_formula), inf_i)

        const = Eq(t_3, time_cond)
        consts.add(const)
    return consts


def time_ordering(n: int, tau_max: float) -> And:
    # n: even
    # 0 = \tau_0 < \tau_1 < ... < \tau_{i / 2} = \tau_max
    time_order: Set[Constraint] = set()
    time_order.add(Eq(RealVal("0"), Real("tau_0")))
    time_order.add(Eq(symbolic_sup(n), RealVal(str(tau_max))))

    for i in range(1, n, 2):
        time_order.add(symbolic_sup(i) < symbolic_sup(i + 1))

    return And(list(time_order))


def reach_time_ordering(n: int, tau_max: float) -> And:
    # n: even
    # 0 = \tau_0 < \tau_1 < ... < \tau_{i / 2} <= \tau_max
    time_order: Set[Constraint] = set()
    time_order.add(Eq(RealVal("0"), Real("tau_0")))
    time_order.add(Leq(symbolic_sup(n), RealVal(str(tau_max))))

    for i in range(1, n, 2):
        time_order.add(symbolic_sup(i) < symbolic_sup(i + 1))

    return And(list(time_order))


def sub_formula(formula: Formula) -> Set[Formula]:
    assert isinstance(formula, Formula)
    set_of_formulas = set()
    count = 0

    # first children
    root = (count, formula)

    waiting_queue = set()
    waiting_queue.add(root)
    set_of_formulas.add(formula)

    while len(waiting_queue) > 0:
        count = count + 1
        _, f = waiting_queue.pop()

        if is_proposition(f):
            set_of_formulas.add(f)
        elif isinstance(f, UnaryFormula):
            set_of_formulas.add(f)
            waiting_queue.add((count, f.child))
        elif isinstance(f, BinaryFormula):
            set_of_formulas.add(f)
            waiting_queue.add((count, f.left))
            waiting_queue.add((count, f.right))
        elif isinstance(f, MultinaryFormula):
            set_of_formulas.add(f)
            for child in f.children:
                waiting_queue.add((count, child))
        else:
            continue
    return set_of_formulas


def is_proposition(formula: Formula):
    if isinstance(formula, Bool):
        return True
    else:
        if not isinstance(formula, Variable) and isinstance(formula, Leaf):
            return True
    return False


def bound_dict(picked_bools: List[Bool], sub_formulas: Set[Formula], model_boolean_abst: Dict) -> Tuple[
    Set[Bool], Dict[int, Set[Formula]], Dict[int, Set[Formula]]
]:
    path_const_children = set()
    # key: depth
    prop_dict: Dict[int, Set[Formula]] = dict()
    # key: bound
    inv_dict: Dict[int, Set[Formula]] = dict()

    time_type1_prefix = ["T1", "T2", "T3"]
    time_type2_prefix = "T"
    integral_prefix = "newIntegral"
    invariant_prefix = "invAtomicID"

    for picked_bool in picked_bools:
        is_chi = "chi" in picked_bool.id
        # check if v_info is applied to unsat_core id
        # unsat_core contains at least one of prefix in v_prefixes
        is_time_type1 = reduce(lambda b, acc: acc or b, [prefix in picked_bool.id for prefix in time_type1_prefix],
                               False)
        if is_chi or is_time_type1:
            formula, f_i, f_k = v_type1_info(picked_bool.id, sub_formulas)
            is_formula_prop = is_proposition(formula)

            # if path has an index f_k
            if is_formula_prop:
                if is_time_type1:
                    path_const_children.add(picked_bool)
                else:
                    if f_k in prop_dict:
                        prop_dict[f_k].add(formula)
                    else:
                        prop_dict[f_k] = {formula}

        is_time_type2 = time_type2_prefix in picked_bool.id and not is_time_type1
        if is_time_type2:
            # if path has an index f_k
            path_const_children.add(picked_bool)

        is_integral = integral_prefix in picked_bool.id
        if is_integral:
            path_const_children.add(picked_bool)

        is_invariant = invariant_prefix in picked_bool.id
        if is_invariant:
            assert picked_bool in model_boolean_abst
            invariant = model_boolean_abst[picked_bool]

            assert isinstance(invariant, Forall)
            module_index, bound = inv_index_info(picked_bool.id)
            if bound in inv_dict:
                inv_dict[bound].add(invariant.const)
            else:
                inv_dict[bound] = {invariant.const}

    # inv_dict key is bound
    # time_dict key is depth
    return path_const_children, prop_dict, inv_dict


def extra_path_dict(prop_dict: Dict[int, Set[Formula]],
                    inv_dict: Dict[int, Set[Formula]]) -> Dict[int, Set[Formula]]:
    # key: depth
    path_dict: Dict[int, Set[Formula]] = dict()
    for depth in prop_dict:
        bound = depth2bound(depth)
        prop_consts = prop_dict[depth]
        is_vertex = depth % 2 == 0

        renamed_consts = set(map(lambda f: rename(f, bound, is_vertex)[0], prop_consts))
        if bound in path_dict:
            path_dict[bound].update(renamed_consts)
        else:
            path_dict[bound] = renamed_consts

    for bound in inv_dict:
        depth = 2 * (bound + 1)
        if depth in path_dict:
            path_dict[depth].update(inv_dict[bound])
        else:
            path_dict[depth] = inv_dict[bound]

    return path_dict


def extra_path_formula(path_dict: Dict[int, Set[Formula]], module_index_dict: Dict[int, int], model: Model):
    path_const_children = list()
    # depth / 2 = bound
    for depth in path_dict:
        path_formula_at_depth = And(list(path_dict[depth]))
        bound = depth2bound(depth)
        is_vertex = depth % 2 == 0
        if is_vertex:
            module_index = module_index_dict[bound]
            assert module_index < len(model.modules)
            integral = model.boolean_abstract[Bool("newIntegral_{}_{}".format(module_index, bound))]
            # renamed_integral = rename_integral(integral, bound, is_vertex)
            forall = Forall(module_index, symbolic_sup(depth), symbolic_inf(depth),
                            path_formula_at_depth, integral)
            path_const_children.append(forall)
        else:
            path_const_children.append(path_formula_at_depth)
    return And(path_const_children)


def pick_current_module_dict(real_clause_set: Set[Formula]) -> Dict[int, int]:
    cur_mode_prefix = "currentMode_"
    cur_module_dict: Dict[int, int] = dict()
    for real_clause in real_clause_set:
        if isinstance(real_clause, Eq):
            if isinstance(real_clause.left, Real) and isinstance(real_clause.right, RealVal):
                real_id = real_clause.left.id
                if cur_mode_prefix in real_id:
                    bound = int(real_id.split("_")[1])
                    module_index = int(real_clause.right.value)

                    assert bound not in cur_module_dict
                    cur_module_dict[bound] = module_index
    return cur_module_dict


def pick_time_and_props(unsat_cores: Set[str], sub_formulas: Set[Formula]) -> Set[str]:
    picked_set: Set[str] = set()

    time_type1_prefix = ["T1", "T2", "T3"]
    time_type2_prefix = "T"
    model_type = ["invAtomicID", "newIntegral"]

    for unsat_core in unsat_cores:
        is_chi = "chi" in unsat_core
        # check if v_info is applied to unsat_core id
        # unsat_core contains at least one of prefix in v_prefixes
        is_time_type1 = reduce(lambda b, acc: acc or b, [prefix in unsat_core for prefix in time_type1_prefix], False)
        if is_chi or is_time_type1:
            formula, f_i, f_k = v_type1_info(unsat_core, sub_formulas)
            is_formula_prop = is_proposition(formula)

            # if path has an index f_k
            if is_formula_prop:
                picked_set.add(unsat_core)

        is_time_type2 = time_type2_prefix in unsat_core and not is_time_type1
        if is_time_type2:
            # if path has an index f_k
            picked_set.add(unsat_core)

        is_model_type = reduce(lambda b, acc: acc or b, [prefix in unsat_core for prefix in model_type], False)
        if is_model_type:
            picked_set.add(unsat_core)

    return picked_set


def assn2path(unsat_cores: Set[str], sub_formulas: Set[Formula], tau_max: float) -> Tuple[
    Dict[Tuple[int, Bool], Formula],
    Dict[Tuple[int, Bool], Formula]
]:
    path_dict: Dict[Tuple[int, Bool], Formula] = dict()
    time_dict: Dict[Tuple[int, Bool], Formula] = dict()

    time_type1_prefix = ["T1", "T2", "T3"]
    time_type2_prefix = "T"

    for unsat_core in unsat_cores:
        is_chi = "chi" in unsat_core
        # check if v_info is applied to unsat_core id
        # unsat_core contains at least one of prefix in v_prefixes
        is_time_type1 = reduce(lambda b, acc: acc or b, [prefix in unsat_core for prefix in time_type1_prefix], False)
        if is_chi or is_time_type1:
            formula, f_i, f_k = v_type1_info(unsat_core, sub_formulas)
            is_formula_prop = is_proposition(formula)

            pair = (f_k, Bool(unsat_core))
            assert pair not in path_dict
            # if path has an index f_k
            if is_formula_prop:
                if is_chi:
                    path_dict[pair] = formula
                if is_time_type1:
                    time_dict[pair] = formula

        is_time_type2 = time_type2_prefix in unsat_core and not is_time_type1
        if is_time_type2:
            formula, f_i = v_type2_info(unsat_core, tau_max)
            pair = (f_i, Bool(unsat_core))
            assert is_proposition(formula) and pair not in path_dict

            # if path has an index f_k
            time_dict[pair] = formula

    return path_dict, time_dict


def is_mode_variable(b: Bool, model: Model):
    if b.id in model.mode_var_dict:
        return True
    return False


def path2const(path: Dict[Tuple[int, Bool], Formula], model: Model):
    path_const_children = list()
    # depth / 2 = bound
    for (depth, v) in path:
        bound = int((depth - 1) / 2)
        is_vertex = depth % 2 == 0
        formula = path[(depth, v)]
        renamed_const, rename_dict = rename(formula, bound, is_vertex)
        if is_vertex:
            #  if mode variable, do not add
            if is_mode_variable(v, model):
                renamed_e_const, _ = rename(formula, bound, False)
                path_const_children.append(Eq(Bool(v.id.replace("p@", "")), renamed_e_const))
                continue

            chi_prop_children = list()
            for module_index, module in enumerate(model.modules):
                integrals = module["flow"]
                # renamed_integrals = substitution(integrals, rename_dict)
                forall = Forall(module_index, symbolic_sup(depth), symbolic_inf(depth),
                                renamed_const,
                                model.boolean_abstract[Bool("newIntegral_{}_{}".format(module_index, bound))])
                matching = Eq(Real("currentMode_{}".format(bound)), RealVal(str(module_index)))
                chi_prop_children.append(And([matching, renamed_const, forall]))
            path_const_children.append(Eq(Bool(v.id.replace("p@", "")), Or(chi_prop_children)))
        else:
            renamed_e_const, _ = rename(formula, bound, False)
            path_const_children.append(Eq(Bool(v.id.replace("p@", "")), renamed_e_const))
    return And(path_const_children)


def time_path2const(path: Dict[Tuple[int, Bool], Formula]):
    path_const_children = list()
    # depth / 2 = bound
    for (depth, v) in path:
        bound = int((depth - 1) / 2)
        is_vertex = depth % 2 == 0
        formula = path[(depth, v)]
        renamed_const, _ = rename(formula, bound, is_vertex)

        if is_vertex:
            path_const_children.append(Eq(Bool(v.id.replace("p@", "")), renamed_const))
        else:
            renamed_e_const, _ = rename(formula, bound, False)
            path_const_children.append(Eq(Bool(v.id.replace("p@", "")), renamed_e_const))
    return And(path_const_children)


def v_type_model_info(v_id: str):
    module_id = v_id.split("@")[1]
    bound_str = v_id.split("@")[2]

    assert "m_" in module_id and "const_" in bound_str

    module_index = module_id.split("_")[1]
    bound = bound_str.split("_")[1]
    return int(module_index), int(bound)


def v_type1_info(v_id: str, sub_formulas: Set[Formula]) -> Tuple[Formula, int, int]:
    is_chi = "chi" in v_id
    is_t1 = "T1" in v_id
    is_t2 = "T2" in v_id
    is_t3 = "T3" in v_id

    if is_chi:
        return type1_info(v_id, sub_formulas)

    # T1, T2, T3
    f, f_i, f_k = type1_info(v_id, sub_formulas)

    assert isinstance(f, GloballyFormula) or isinstance(f, FinallyFormula)
    sup_formula = f.local_time.right
    inf_formula = f.local_time.left

    sup_k = symbolic_sup(f_k)
    inf_k = symbolic_inf(f_k)

    sup_i = symbolic_sup(f_i)
    inf_i = symbolic_inf(f_i)

    if is_t1:
        return Leq(sup_k, Add(inf_i, inf_formula)), f_i, f_k

    if is_t2:
        return Leq(Add(sup_i, sup_formula), inf_k), f_i, f_k

    if is_t3:
        return Leq(Sub(inf_k, sup_formula), inf_i), f_i, f_k

    raise NotSupportedError("unknown time type")


def v_type2_info(v_id: str, tau_max: float) -> Tuple[Formula, int]:
    return type2_info(v_id, tau_max)


# type1: v_id^{i, k}_{hash}
def type1_info(v_id: str, sub_formulas: Set[Formula]) -> Tuple[Formula, int, int]:
    hash_id = int(v_id.split("_")[1])
    i, k = type1_index_info(v_id)

    for f in sub_formulas:
        if hash(f) == hash_id:
            return f, i, k

    raise NotSupportedError("cannot find corresponding formula")


# type2: v_id^{i}_{l} or v_id^{i}_{r}
def type2_info(v_id: str, tau_max) -> Tuple[Formula, int]:
    left_or_right = v_id.split("_")[1]
    is_left = left_or_right == "l"
    is_right = left_or_right == "r"

    i = type2_index_info(v_id)

    if is_left:
        return symbolic_sup(i) <= RealVal(str(tau_max)), i

    if is_right:
        return Eq(symbolic_sup(i), RealVal(str(tau_max))), i

    raise NotSupportedError("cannot find corresponding formula")


def type1_index_info(v_id: str) -> Tuple[int, int]:
    # {i, k}
    ik_encoded_str = v_id.split("_")[0].split("^")[1][1:-1]
    ik = ik_encoded_str.split(",")

    assert len(ik) == 2
    i = int(ik[0])
    k = int(ik[1])
    return i, k


def type2_index_info(v_id: str):
    # {i}
    return int(v_id.split("_")[0].split("^")[1])


def inv_index_info(v_id: str):
    # bound
    bound = int(v_id.split("_")[2])
    module_index = int(v_id.split("_")[1][0])
    return module_index, bound


def rename(f: Formula, bound: int, is_vertex=True):
    variables = get_vars(f)
    rename_dict = dict()
    for v in variables:
        if isinstance(v, Bool):
            indexed_v = Bool("{}_{}".format(v.id, bound))
            rename_dict[v] = indexed_v
        if isinstance(v, Real) and "tau_" not in v.id:
            if is_vertex:
                indexed_v = Real("{}_{}_0".format(v.id, bound))
            else:
                if bound > 0:
                    indexed_v = Real("{}_{}_t".format(v.id, bound - 1))
                else:
                    indexed_v = Real("{}_{}_0".format(v.id, bound))
            rename_dict[v] = indexed_v
    return substitution(f, rename_dict), rename_dict


def depth2bound(depth: int):
    return int((depth - 1) / 2)


# vertex, edge
def contradiction_gen(clause_set, sub_formulas):
    const_edge_children = list()
    const_vertex_children = list()
    for c in clause_set:
        if isinstance(c, Bool):
            is_chi = "chi" in c.id
            if is_chi:
                formula, f_i, f_k = v_type1_info(c.id, sub_formulas)
                is_formula_prop = is_proposition(formula)
                is_edge = f_k % 2 == 1
                is_vertex = f_k % 2 == 0

                bound = depth2bound(f_k)

                # if path has an index f_k
                if is_formula_prop and is_edge:
                    renamed_f, _ = rename(formula, bound, is_vertex=False)
                    const_edge_children.append(Eq(c, renamed_f))

                if is_formula_prop and is_vertex:
                    renamed_f_v, _ = rename(formula, bound, is_vertex=True)
                    renamed_f_e, _ = rename(formula, bound + 1, is_vertex=False)
                    const_vertex_children.append(Eq(c, And([renamed_f_v, renamed_f_e])))
    return And(const_vertex_children), And(const_edge_children)


def contradiction_gen_inv(boolean_dict):
    inv_eq = list()
    for b in boolean_dict:
        is_inv = "invAtomicID" in b.id
        if is_inv:
            forall = boolean_dict[b]
            assert isinstance(forall, Forall)
            inv_eq.append(Eq(b, forall.const))
    return And(inv_eq)


def acc_size(acc: List[Formula]):
    return size_of_tree(And(acc))
