from itertools import combinations
from typing import Tuple, Optional, List, Set

import z3

from stlmcPy.constraints.constraints import Constraint, And, Forall, BoolVal, Dynamics, Real, RealVal, Bool, Variable, \
    Eq, Neq, Or
from stlmcPy.constraints.operations import get_vars, clause, substitution, reduce_not, update_dynamics_with_replacement
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.hybrid_automaton.hybrid_automaton import HybridAutomaton, BaseMode, AggregatedMode, Transition, Mode
from stlmcPy.solver.ode_utils import remove_index
from stlmcPy.solver.strategy import unit_split
from stlmcPy.solver.z3 import z3Obj
from stlmcPy.util.logger import Logger


def calc_initial_terminal_modes(ha: HybridAutomaton):
    assert (ha is not None)
    _initial_modes = set()
    _terminal_modes = set()
    for m in ha.modes:
        if len(m.incoming) == 0:
            if len(m.outgoing) == 0:
                pass
            else:
                _initial_modes.add(m)
        else:
            if len(m.outgoing) == 0:
                _terminal_modes.add(m)

    return _initial_modes, _terminal_modes


# Definition:
#   modes with no incoming edges is initial mode
#   modes with no outgoing edges is terminal mode
#   if modes has no incoming and outgoing edges at the same time,
#   this mode is ignored.
# Assumption:
#   Given hybrid automaton is tree not graph.
def indexing(ha: HybridAutomaton):
    assert (ha is not None)
    initial_modes, terminal_modes = calc_initial_terminal_modes(ha)

    # print(initial_modes)
    # print(terminal_modes)
    assert (len(terminal_modes) == 1)

    indexing_dict = dict()
    waiting_queue = terminal_modes
    index = 1
    new_waiting_queue = list()
    while len(waiting_queue) > 0:
        m = waiting_queue.pop()
        if index not in indexing_dict:
            indexing_dict[index] = set()
        indexing_dict[index].add(m)

        for trans in m.incoming:
            new_waiting_queue.append(trans.src)

        if len(waiting_queue) == 0:
            index += 1
            for elem in new_waiting_queue:
                waiting_queue.add(elem)
            new_waiting_queue.clear()
    return indexing_dict


# p subsumes q, p >= q
def subsumption(p: Constraint, q: Constraint):
    """
    check if p subsumes q.

    :param p: any constraint
    :param q: any constraint
    :return: true if p subsumes q else false
    """
    if isinstance(p, And):
        if len(p.children) == 0:
            p = None

    if isinstance(q, And):
        if len(q.children) == 0:
            q = None

    if q is None:
        if p is None:
            return True
        return False
    if p is None:
        return True

    var_set = get_vars(p)
    var_set = var_set.union(get_vars(q))

    var_list = list()
    for v in var_set:
        var_list.append(z3Obj(v))

    left = z3Obj(q)
    right = z3Obj(p)

    f = z3.ForAll(var_list, z3.Implies(left, right))
    s = z3.Solver()
    s.add(f)
    # print(s.sexpr())
    str_result = str(s.check())
    # print(str_result)
    if str_result == "sat":
        return True
    else:
        return False


def merge_mode(m1: BaseMode, m2: BaseMode, ha: HybridAutomaton) -> Tuple[
    Optional[AggregatedMode], bool]:
    def _remove_forall_from_invariant(c: Constraint):
        if c is None:
            return c
        # invariants are assumed to be None or And
        if isinstance(c, And):
            new_children = list()
            for child in c.children:
                if isinstance(child, Forall):
                    new_children.append(child.const)
                else:
                    new_children.append(child)
            return new_children
        else:
            return [c]

    # def _invariant_eq(c: And, c1: And):
    #     assert isinstance(c, And) and isinstance(c1, And)
    #     eq_queue = c.children.copy()
    #     for c in eq_queue:
    #         assert isinstance(c, Forall)
    #         for c1 in c1.children:
    #             assert isinstance(c1, Forall)
    #             if c.current_mode_number == c1.current_mode_number:
    #                 if str(c.const) == str(c1.const):
    #                     eq_queue.pop(c)
    #     return len(eq_queue) == 0

    if m1.dynamics == m2.dynamics:
        m1_inv_without_forall = _remove_forall_from_invariant(m1.invariant)
        m2_inv_without_forall = _remove_forall_from_invariant(m2.invariant)

        # invariants to be checked subsumption relation
        m1_inv = None
        m2_inv = None
        if m1_inv_without_forall is not None:
            m1_inv = And(m1_inv_without_forall)

        if m2_inv_without_forall is not None:
            m2_inv = And(m2_inv_without_forall)

        ha2_subsume_ha1 = subsumption(m2_inv, m1_inv)
        ha1_subsume_ha2 = subsumption(m1_inv, m2_inv)
        if not ha2_subsume_ha1 and not ha1_subsume_ha2:
            # print("cannot merge {} and {}".format(m1.name, m2.name))
            return None, False

        is_inv_same = False
        if ha2_subsume_ha1 and ha1_subsume_ha2:
            is_inv_same = True

        new_agg_mode = AggregatedMode("{}_{}".format(m1.name, m2.name), set(), ha)
        new_agg_mode.add(m1)
        new_agg_mode.add(m2)
        new_agg_mode.set_dynamics(m1.dynamics)

        new_out_going = set()
        new_out_going = new_out_going.union(m1.outgoing)
        new_out_going = new_out_going.union(m2.outgoing)

        if ha2_subsume_ha1:
            new_agg_mode.set_invariant(m2.invariant)
        else:
            # ha1_subsume_ha2
            new_agg_mode.set_invariant(m1.invariant)

        for out_going_trans in new_out_going:
            g = out_going_trans.guard
            # flatten guard constraint if it is And
            if isinstance(g, And):
                children = g.children.copy()
                if ha1_subsume_ha2 and m1.invariant is not None and out_going_trans.belongs_to() is m1.belongs_to():
                    children.extend(m1_inv_without_forall)
                elif m2.invariant is not None and out_going_trans.belongs_to() is m2.belongs_to():
                    children.extend(m2_inv_without_forall)
                out_going_trans.set_guard(And(children))
            else:
                if ha1_subsume_ha2 and m1.invariant is not None and out_going_trans.belongs_to() is m1.belongs_to():
                    new_children = m1_inv_without_forall
                    new_children.extend(g)
                    out_going_trans.set_guard(And(new_children))
                elif m2.invariant is not None and out_going_trans.belongs_to() is m2.belongs_to():
                    new_children = m2_inv_without_forall
                    new_children.extend(g)
                    out_going_trans.set_guard(And(new_children))

        new_agg_mode.incoming = new_agg_mode.incoming.union(m1.incoming)
        new_agg_mode.incoming = new_agg_mode.incoming.union(m2.incoming)

        new_agg_mode.outgoing = new_agg_mode.outgoing.union(new_out_going)
        return new_agg_mode, True
    else:
        return None, False


def merge_transition(trans1: Transition, trans2: Transition):
    # if trans1.belongs_to() != trans2.belongs_to():
    #     return False
    if id(trans1.src) == id(trans2.src) and id(trans1.trg) == id(trans2.trg):
        tg1_subsumes_tg2 = subsumption(trans1.guard, trans2.guard)
        tg2_subsumes_tg1 = subsumption(trans2.guard, trans1.guard)

        tr1_subsumes_tr2 = subsumption(trans1.reset, trans2.reset)
        tr2_subsumes_tr1 = subsumption(trans2.reset, trans1.reset)

        if tg1_subsumes_tg2 and tg2_subsumes_tg1:
            if tr1_subsumes_tr2 and tr2_subsumes_tr1:
                return True
    return False


def merge(*hybrid_automata, **option):
    """
    Merge given hybrid automata. In order to merged, two hybrid automaton must have the common
    terminal nodes. See a test case with the different length.

    :param hybrid_automata: Any hybrid automata
    :param option: chi_optimization True to enable chi optimization else false
    :return: A new merged hybrid automata
    """
    option_keyword = "chi_optimization"
    is_optimize = False
    if option_keyword in option.keys():
        if isinstance(option[option_keyword], bool):
            is_optimize = option[option_keyword]

    def _get_terminal_nodes(ha: HybridAutomaton) -> List[BaseMode]:
        assert (ha is not None)
        terminal_modes = list()
        for _m in ha.modes:
            if len(_m.incoming) == 0:
                pass
            else:
                if len(_m.outgoing) == 0:
                    terminal_modes.append(_m)
        return terminal_modes

    def _categorize(_set):
        _category_dict = dict()
        for _m in _set:
            dyn_str = str(_m.dynamics)
            if dyn_str not in _category_dict:
                _category_dict[dyn_str] = set()
            _category_dict[dyn_str].add(_m)
        return _category_dict

    def _check_chi_valuation(chi_valuation_dict1: dict, chi_valuation_dict2: dict, is_on=False):
        if not is_on:
            return True
        if len(chi_valuation_dict1) > 0 and len(chi_valuation_dict2) > 0:
            for chi_1 in chi_valuation_dict1:
                for chi_2 in chi_valuation_dict2:
                    if chi_1 == chi_2:
                        if chi_valuation_dict1[chi_1] != chi_valuation_dict2[chi_2]:
                            return False
        return True

    all_merged_modes = set()
    all_merged_trans = set()
    waiting_queue = set()
    further_remove_mode_queue = set()
    merged_ha_name = "new_agg_mode"
    for hybrid_automaton in hybrid_automata:
        merged_ha_name = "{}__{}".format(merged_ha_name, hybrid_automaton.name)
        for terminal_node in _get_terminal_nodes(hybrid_automaton):
            waiting_queue.add(terminal_node)

    merged_ha = HybridAutomaton(merged_ha_name)

    categories = _categorize(waiting_queue)
    # print("this is waiting queue {}".format(waiting_queue))
    is_reset_waiting_queue = False
    logger = Logger()
    logger.start_timer("mode merging")
    merging_counter = 0
    while len(waiting_queue) > 0:
        merging_counter += 1
        print("mode merging ... {}".format(merging_counter))
        if is_reset_waiting_queue:
            updated_waiting_queue = set()
            # print(waiting_queue)
            for m in waiting_queue:
                all_merged_modes.add(m)
                for trans in m.incoming:
                    updated_waiting_queue.add(trans.src)
                    trans.trg = m
                for trans in m.outgoing:
                    trans.src = m
                    all_merged_trans.add(trans)
            if is_optimize:
                for mode_to_be_removed in further_remove_mode_queue:
                    waiting_queue.remove(mode_to_be_removed)
                further_remove_mode_queue.clear()

            waiting_queue.clear()
            waiting_queue = updated_waiting_queue
            is_reset_waiting_queue = False

        categories = _categorize(waiting_queue)
        # print(waiting_queue)
        is_update = False
        for c in categories:
            # print("normal => {}".format(categories))
            possibilities = list(combinations(categories[c], 2))
            if len(possibilities) == 0:
                is_reset_waiting_queue = True
                break

            for (m1, m2) in possibilities:
                # print("is optimize {}".format(is_optimize))
                is_same_valuation = _check_chi_valuation(m1.chi_valuation, m2.chi_valuation, is_optimize)
                # print("{}, {} : and {}, {} => {}".format(m1.belongs_to().name, m1.name, m2.belongs_to().name, m2.name,
                #                                          is_same_valuation, m1 is m2))
                if is_same_valuation:
                    # print("valuation")
                    merged_mode, is_merged = merge_mode(m1, m2, merged_ha)
                    if is_merged:
                        # print("merged! to {}".format(merged_mode))
                        # print("({} <><> {}) are merged to {}".format(m1, m2, merged_mode))
                        waiting_queue.remove(m1)
                        waiting_queue.remove(m2)
                        waiting_queue.add(merged_mode)
                        # categories = _categorize(waiting_queue)
                        # print(categories)
                        is_update = True
                        break
                else:
                    # if m1 and m2 have the same dynamics but not the valuations
                    # put them in the removing queue
                    further_remove_mode_queue.add(m1)
                    further_remove_mode_queue.add(m2)

            if is_update:
                break

        # remove modes in the removing queue
        if is_optimize:
            if len(further_remove_mode_queue) > 0:
                is_reset_waiting_queue = True

        if is_update is False:
            is_reset_waiting_queue = True
    logger.stop_timer("mode merging")
    print("mode merging time : {}".format(logger.get_duration_time("mode merging")))

    def _update_mode_name(_mode: BaseMode):
        _mode_belongs_to = _mode.belongs_to().name
        if _mode_belongs_to == merged_ha_name:
            _mode.name = "{}_{}".format(_mode_belongs_to, _mode.name)
        else:
            _mode.name = "{}_{}_{}".format(merged_ha_name, _mode_belongs_to, _mode.name)
        merged_ha.modes.add(_mode)

    def _update_trans_name(_trans: Transition):
        _trans_belongs_to = _trans.belongs_to().name
        if _trans_belongs_to == merged_ha_name:
            _trans.name = "{}_{}".format(_trans_belongs_to, _trans.name)
        else:
            _trans.name = "{}_{}_{}".format(merged_ha_name, _trans_belongs_to, _trans.name)
        merged_ha.transitions.add(trans)

    # print(all_merged_modes)
    for m in all_merged_modes:
        _update_mode_name(m)

    reduced_merged_trans = all_merged_trans.copy()
    # reduce transition

    logger.start_timer("transition merging")
    merging_counter = 0
    while True:
        merging_counter += 1
        print("transition merging ... {}".format(merging_counter))
        reduced_merged_trans_before = reduced_merged_trans.copy()
        possible_transitions = list(combinations(reduced_merged_trans, 2))
        for (trans1, trans2) in possible_transitions:
            # print("=======>>")
            # print(trans1)
            # print(trans2)
            if merge_transition(trans1, trans2):
                # print("=======>>")
                # print("{}_id_{} => ( {} ) {}_id_{}".format(trans1.src.name, id(trans1.src), trans1, trans1.trg, id(trans1.trg)))
                # print("{}_id_{} => ( {} ) {}_id_{}".format(trans2.src.name, id(trans2.src), trans2, trans2.trg, id(trans2.trg)))
                reduced_merged_trans.remove(trans1)
                break
        if reduced_merged_trans_before.issubset(reduced_merged_trans) and \
                reduced_merged_trans_before.issuperset(reduced_merged_trans):
            break
    logger.stop_timer("transition merging")
    print("transition merging time : {}".format(logger.get_duration_time("transition merging")))
    for trans in reduced_merged_trans:
        _update_trans_name(trans)

    # print("\n\n\n Merged!")
    # print(merged_ha)
    return merged_ha


def make_mode_from_formula(formula: Constraint, bound, max_bound, sigma):
    clause_of_formula = clause(formula)
    # print(formula)
    s_forall_i, s_integral_i, s_0_i, s_tau_i, s_reset_i, s_guard_i = unit_split(clause_of_formula, bound)

    mode_i = Mode("mode{}".format(bound), None)

    for integral in s_integral_i:
        if integral in sigma:
            dyns = sigma[integral].dynamics
            for j in range(1, bound + 1):
                tau = Real("tau_" + str(j))
                update_dynamics_with_replacement(dyns, tau, RealVal("0"))

            for j in range(bound + 1, max_bound + 2):
                tau = Real("tau_" + str(j))
                update_dynamics_with_replacement(dyns, tau, RealVal("1"))
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


def add_mode(ha: HybridAutomaton, depth: int, mode: BaseMode):
    assert ha is not None

    def _set_ha(_mode: BaseMode):
        _mode.ha = ha
        for _m in _mode.incoming:
            _m.ha = ha

        for _m in _mode.outgoing:
            _m.ha = ha

    def _get_modes_at_depth(_start_modes: set):
        queue = _start_modes
        _depth = 0
        while len(queue) > 0:
            if depth == _depth:
                return queue

            new_queue = set()
            for _mode in queue:
                for _incoming_mode in _mode.incoming:
                    new_queue.add(_incoming_mode.src)
            queue = new_queue
            _depth += 1

        return queue

    initial_modes, terminal_modes = calc_initial_terminal_modes(ha)
    modes_at_depth = _get_modes_at_depth(terminal_modes)

    merge_counter = 0
    found_mergable_mode = False
    merged_mode = None

    for mode_at_depth in modes_at_depth:
        merge_counter += 1
        print("searching for mergable mode ... {}".format(merge_counter))
        merged_mode, is_merged = merge_mode(mode_at_depth, mode, ha)
        found_mergable_mode = found_mergable_mode or is_merged

    if found_mergable_mode:
        print("found mergable mode : {}".format(merged_mode))
        _set_ha(mode)
    else:
        print("found no mergable mode")


def encode_possible_path_as_formula(formula: Constraint, bound: int, assignment: dict):
    def _update_set_of_vars(_categorized_set: set, _set_of_vars: set):
        for cl in _categorized_set:
            _set_of_vars = _set_of_vars.union(get_vars(cl))
        return _set_of_vars

    clause_of_formula = clause(formula)
    s_forall_i, s_integral_i, s_0_i, s_tau_i, s_reset_i, s_guard_i = unit_split(clause_of_formula, bound)

    set_of_vars = set()

    set_of_vars = _update_set_of_vars(s_forall_i, set_of_vars)
    set_of_vars = _update_set_of_vars(s_integral_i, set_of_vars)
    set_of_vars = _update_set_of_vars(s_0_i, set_of_vars)
    set_of_vars = _update_set_of_vars(s_tau_i, set_of_vars)
    set_of_vars = _update_set_of_vars(s_reset_i, set_of_vars)
    set_of_vars = _update_set_of_vars(s_guard_i, set_of_vars)

    new_path_constraint_children = list()
    counter_variable = set()

    # print("assignment {}".format(assignment))

    for v in set_of_vars:
        if v in assignment:
            counter_variable.add(v)
            value = assignment[v]
            if isinstance(v, Bool):
                if isinstance(value, BoolVal) and value.value == "False":
                    new_path_constraint_children.append(Eq(v, BoolVal("True")))
                elif isinstance(value, BoolVal) and value.value == "True":
                    new_path_constraint_children.append(Eq(v, BoolVal("False")))
                else:
                    raise NotSupportedError("impossible assignment")
            else:
                # real or int case
                new_path_constraint_children.append(Neq(v, value))

    old_path_constraint_children = list()

    for v in assignment:
        if v not in counter_variable:
            old_path_constraint_children.append(Eq(v, assignment[v]))

    print("new path constraint {}".format(Or(new_path_constraint_children)))
    print("old path constraint {}".format(And(old_path_constraint_children)))

    return And(old_path_constraint_children), Or(new_path_constraint_children)