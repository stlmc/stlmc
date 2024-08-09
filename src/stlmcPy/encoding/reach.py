import time
from abc import abstractmethod
from typing import Dict, Set, List, Tuple

from .static_learning import StaticLearner
from ..constraints.constraints import *
from ..constraints.operations import substitution, make_new_dynamics, get_vars, make_dictionary_for_invariant, clause
from ..objects.algorithm import Algorithm
from ..objects.configuration import Configuration
from ..objects.goal import Goal
from ..objects.model import Model, StlMC
from ..solver.abstract_solver import SMTSolver
from ..solver.new_dreal import newDRealSolver
from ..util.logger import Logger
from ..util.print import Printer


class ReachAlgorithm(Algorithm):
    def run(self, model: Model, goal: Goal, prop_dict: Dict, config: Configuration,
            solver: SMTSolver, logger: Logger, printer: Printer):
        common_section = config.get_section("common")
        bound = int(common_section.get_value("bound"))
        time_bound = float(common_section.get_value("time-bound"))
        delta = float(common_section.get_value("threshold"))
        # only_loop = common_section.get_value("only-loop")

        solving_time = 0.0

        r_g = goal.k_step_consts(bound, time_bound, -1, model, prop_dict)
        ic, _ = model.init_consts()
        assert isinstance(model, StlMC)

        # dreal related
        copied_model = copy_model(model)
        apply_dreal(copied_model, bound, time_bound)
        # g_c = global_clock(bound, time_bound)

        # for future
        # static_learner = StaticLearner(model, goal.get_formula())
        # static_learner.generate_learned_clause(bound, delta)
        # contradiction_const = static_learner.get_contradiction_upto(bound, clause(goal.get_formula()))
        # print(contradiction_const)

        paths = find_feasible(copied_model, bound + 1)
        print("total path: {}".format(len(paths)))
        for i, (pc, pd) in enumerate(paths):
            if isinstance(solver, newDRealSolver):
                solver.set_stl_model(copied_model)

            f = translate(pc, pd, True)
            # add gl_clock
            # r, s = solver.solve(And([ic, f, r_g, g_c]))
            r, s = solver.solve(And([ic, f, r_g]))
            st = solver.get_time("solving timer")
            solver.reset_time("solving timer")

            solving_time += st

            # found counterexample
            if r == "False":
                assn = solver.make_assignment()
                print("solving {}".format(solving_time))
                # printer.print_verbose("size : {}".format(total_size))
                # return "False", solving_time, bound, assn.get_assignments()
                return "True", solving_time, bound, None
        print("solving {}".format(solving_time))
        # return "True", solving_time, bound, None
        return "False", solving_time, bound, None

    def set_debug(self, msg: str):
        pass


# mode, 0, t, reset
SubDict = Tuple[Dict, Dict, Dict, Dict]


def make_indexed_variable_dict(model: StlMC, bound: int):
    assert isinstance(model, StlMC)
    mode_v_d = dict()
    d0, dt = dict(), dict()
    dr = dict()

    next_str = model.next_str
    op_dict = dict({'bool': Bool, 'int': Int, 'real': Real})

    for mode_var_id in model.mode_var_dict:
        mode_var = model.mode_var_dict[mode_var_id]
        next_var = op_dict[mode_var.type]("{}{}".format(mode_var_id, next_str))

        # add bounded info
        mode_v_d[mode_var] = op_dict[mode_var.type]("{}_{}".format(mode_var_id, bound))
        dr[next_var] = op_dict[mode_var.type]("{}_{}".format(mode_var_id, bound + 1))

    for range_var in model.range_dict:
        next_var = Real("{}{}".format(range_var, next_str))

        # add bounded info
        d0[range_var] = Real("{}_{}_0".format(range_var.id, bound))
        dt[range_var] = Real("{}_{}_t".format(range_var.id, bound))
        dr[next_var] = Real("{}_{}_0".format(range_var.id, bound + 1))
    return mode_v_d, d0, dt, dr


def find_feasible(model: StlMC, bound: int):
    feasible_paths: List[(Formula, Dict)] = list()
    all_combination = make_pool(model, bound)

    # key: (mode index, bound), value: (encoding, jump, abstraction dict, jp abstraction dict)
    memoize: Dict[Tuple[int, int], Tuple[List[Formula], Or, Dict, Dict]] = dict()
    subst_memoize: Dict[int, SubDict] = dict()

    counter = 0
    cache_c = 0
    memoize_c = 0
    s = time.time()
    for path in all_combination:
        # print("path: {}".format(path))
        path_const: List[Formula] = list()
        path_dict: Dict = dict()
        for b, mode_index in enumerate(path):
            counter += 1
            # print("  processing mode#{}".format(mode_index))
            if b not in subst_memoize:
                substitute_dict = make_indexed_variable_dict(model, b)
                subst_memoize[b] = substitute_dict
            else:
                cache_c += 1
                substitute_dict = subst_memoize[b]

            if (mode_index, b) not in memoize:
                c, jc, d, jp_d = make_consts(model, mode_index, b, substitute_dict)
                memoize[(mode_index, b)] = (c, jc, d, jp_d)
            else:
                memoize_c += 1
                c, jc, d, jp_d = memoize[(mode_index, b)]
            path_const.extend(c)
            path_dict.update(d)

            if b < bound - 1:
                path_const.append(jc)
                path_dict.update(jp_d)

        # print("  const: {}".format(path_const))
        feasible_paths.append((path_const, path_dict))

    e = time.time()
    print("memoize : {}%".format(cache_c / counter * 100))
    print("substitution caching : {}%".format(cache_c / counter * 100))
    print("time: {}".format(e - s))
    return feasible_paths


def make_pool(model: StlMC, bound: int):
    def concat(li, le):
        c_li = li.copy()
        c_li.append(le)
        return c_li

    from itertools import product
    # module_index = [index for index in range(len(model.modules))]

    assert model.init is not None
    m_jp_d = feasible_jumps(model)

    pool = list()
    waiting_queue = [[model.init_mode]]
    while len(waiting_queue) > 0:
        p = waiting_queue.pop(0)

        if len(p) > bound - 1:
            pool.append(p)
            continue

        m = p[-1]
        assert m in m_jp_d
        waiting_queue.extend([concat(p, e) for e in m_jp_d[m]])

    return pool


def feasible_jumps(model: StlMC):
    m_jp_d = dict()
    for mode_index, mode in enumerate(model.modules):
        m_jp_d[mode_index] = list(mode["jp_d"].values())
    return m_jp_d


def make_consts(model: StlMC, mode_index, b: int, substitution_dict: SubDict):
    track_dict = dict()
    mode_v_d, d0, dt, dr = substitution_dict
    mode_v, mode_track = make_mode_consts(model, mode_index, b, mode_v_d)
    flow_v, flow_track = make_flow_consts(model, mode_index, b, d0, dt)
    inv_v, inv_track = make_inv_consts(model, mode_index, b, d0, dt)
    jp_or, jp_track = make_jump_consts(model, mode_index, b, dt, dr, mode_v_d)
    # rv, rc_track = make_range_consts(model, d0, dt)
    rc = make_range_consts(model, d0, dt)

    track_dict.update(mode_track)
    track_dict.update(flow_track)
    track_dict.update(inv_track)

    return [mode_v, flow_v, inv_v], jp_or, track_dict, jp_track


def make_mode_consts(model: StlMC, mode_index, b: int, substitution_dict: Dict):
    track_dict = dict()
    mode_const = model.modules[mode_index]["mode"]
    mode_cons_bound = substitution(mode_const, substitution_dict)

    # m_{ module index }@
    track_v = Bool("mode@m{}#b{}".format(mode_index, b))
    visualize = Eq(Real("$m_{}".format(b)), RealVal(str(mode_index)))
    mode_const = And([mode_cons_bound, visualize])

    track_dict[track_v] = mode_const
    return track_v, track_dict


def make_flow_consts(model: StlMC, mode_index, b: int, d0: Dict, dt: Dict):
    mode = model.modules[mode_index]
    dynamics = mode["flow"]

    track_dict = dict()

    start_vector = list()
    end_vector = list()

    for index, _ in enumerate(dynamics.exps):
        dyn_v = dynamics.vars[index]
        start_vector.append(d0[dyn_v])
        end_vector.append(dt[dyn_v])
    new_dynamics = make_new_dynamics(dynamics, b, model.mode_var_dict, model.range_dict, model.const_dict)

    integral = Integral(mode_index, end_vector, start_vector, new_dynamics)
    bool_flow = Bool("flow@m{}#b{}".format(mode_index, b))
    track_dict[bool_flow] = integral
    return bool_flow, track_dict


def make_inv_consts(model: StlMC, mode_index, b: int, d0: Dict, dt: Dict):
    track_dict = dict()

    inv_c = model.modules[mode_index]["inv"]
    assert isinstance(inv_c, And)
    inv_s = substitution(inv_c, d0)
    inv_e = substitution(inv_c, dt)

    track_v = Bool("inv@m{}#b{}".format(mode_index, b))
    forall_c = Forall(mode_index, Real("tau_{}".format(b + 1)), Real("tau_{}".format(b)), inv_e, None)
    cm_c = Eq(Real("$m_{}".format(b)), RealVal(str(mode_index)))
    track_dict[track_v] = And([inv_s, inv_e, cm_c, forall_c])

    return track_v, track_dict


def make_jump_consts(model: StlMC, mode_index, b: int, dt: Dict, dr: Dict, mode_v_d: Dict):
    track_dict = dict()
    jumps = model.modules[mode_index]["jump"]

    jump_consts = list()
    for j_index, j_pre in enumerate(jumps):
        track_v = Bool("jp{}@m{}#b{}".format(j_index + 1, mode_index, b))

        # first replace next
        rn = substitution(jumps[j_pre], dr)
        # replace rest, should handle mode and continuous variables at the same time
        fj = substitution(substitution(rn, dt), mode_v_d)
        track_dict[track_v] = And([substitution(j_pre, dt), fj])
        jump_consts.append(track_v)

    return Or(jump_consts), track_dict


def make_range_consts(model: StlMC, d0: Dict, dt: Dict):
    r_consts = list()
    # track_dict = dict()
    # track_v = Bool("rv")
    for rv in model.range_dict:
        ic = model.aux_make_range_const(d0[rv], model.range_dict[rv])
        ec = model.aux_make_range_const(dt[rv], model.range_dict[rv])
        r_consts.extend(ic)
        r_consts.extend(ec)
    # track_dict[track_v] = And(r_consts)
    # return track_v, track_dict
    return And(r_consts)


def make_dict_consts(abstraction: Dict):
    if len(abstraction) > 0:
        return And([Eq(c, abstraction[c]) for c in abstraction])
    return BoolVal("True")


def translate(consts: List[Formula], abstraction: Dict, is_dreal=False):
    if is_dreal:
        return substitution(And(consts), abstraction)
    else:
        consts.append(make_dict_consts(abstraction))
        return And(consts)


def global_clock(bound: int, tb: float):
    time_order: List[Constraint] = list()
    zero = RealVal("0")
    g_m = RealVal("{}".format(tb))

    g0 = [Real("g@clock_{}_0".format(b)) for b in range(bound + 1)]
    gt = [Real("g@clock_{}_t".format(b)) for b in range(bound + 1)]

    time_order.append(Eq(zero, g0[0]))

    for b in range(bound + 1):
        time_order.append(g0[b] <= gt[b])
    time_order.append(gt[bound] <= g_m)

    for b in range(bound + 1):
        if b < len(g0) - 1:
            time_order.append(Eq(gt[b], g0[b + 1]))
    return And(time_order)


def copy_model(model: StlMC):
    modules = list()
    for m in model.modules:
        md = dict()
        md["mode"], md["inv"] = m["mode"], m["inv"]
        md["jump"], md["jp_d"] = m["jump"], m["jp_d"]

        flow = m["flow"]
        if isinstance(flow, Ode):
            md["flow"] = Ode(flow.vars.copy(), flow.exps.copy())
        else:
            md["flow"] = Function(flow.vars.copy(), flow.exps.copy())
        modules.append(md)

    return StlMC(model.mode_var_dict.copy(), model.range_dict.copy(),
                 model.const_dict.copy(), model.prop_dict.copy(),
                 modules, model.init, model.init_mode)


def apply_dreal(model: StlMC, bound: int, tb: float):
    # # add gl_clock
    # g_clk = Real("g@clock")
    # model.range_dict[g_clk] = (True, 0.0, tb, True)
    #
    # one = RealVal("1")
    # for mode in model.modules:
    #     flow = mode["flow"]
    #
    #     assert isinstance(mode["flow"], Ode)
    #     vs, es = flow.vars.copy(), flow.exps.copy()
    #     vs.append(g_clk)
    #     es.append(one)
    #     mode["flow"] = Ode(vs, es)

    v_n = "$m"
    model.mode_var_dict[v_n] = Int(v_n)
