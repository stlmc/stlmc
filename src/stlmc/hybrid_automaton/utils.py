from typing import Tuple, Optional, List, Set

import z3

from ..constraints.operations import *
from ..exception.exception import NotSupportedError
from ..hybrid_automaton.hybrid_automaton import HybridAutomaton, BaseMode, AggregatedMode, Transition, Mode
from ..solver.ode_utils import remove_index
from ..solver.strategy import unit_split
from ..solver.z3 import z3Obj
from ..tree.operations import elements_of_tree
from ..util.logger import Logger


def update_dynamics_with_replacement(dynamics: Dynamics, v: Variable, e: Expr):
    is_update = False
    for i, dyn_var in enumerate(dynamics.vars):
        if dyn_var.id == v.id:
            dynamics.exps[i] = e
            is_update = True
    if not is_update:
        dynamics.vars.append(v)
        dynamics.exps.append(e)


def vars_in_ha(ha: HybridAutomaton):
    assert ha is not None
    var_set = set()
    for mode in ha.modes:
        for (var, exp) in mode.dynamics:
            # add left hand variable
            var_set.add(var)

            # add variables in exp
            exp_var_set = get_vars(exp)
            var_set = var_set.union(exp_var_set)

        for inv in mode.invariant:
            inv_var_set = get_vars(inv)
            var_set = var_set.union(inv_var_set)

    for transition in ha.transitions:
        for guard in transition.guard:
            var_set = var_set.union(get_vars(guard))

        for reset in transition.reset:
            var_set = var_set.union(get_vars(reset))

    return var_set


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


# p subsumes q, p >= q
def syntactic_subsumption(p: Constraint, q: Constraint):
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

    p_set = set(p.children)
    q_set = set(q.children)

    if p_set.issubset(q_set):
        return True
    return False


def merge_mode_pool_syntatically(modes: Set[BaseMode], ha: HybridAutomaton) -> Tuple[
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

    def _invariant_eq(c: And, c1: And):
        if c is None and c1 is None:
            return True

        if c is None or c1 is None:
            return False

        assert isinstance(c, And) and isinstance(c1, And)
        return elements_of_tree(c) == elements_of_tree(c1)

    def _all_modes_are_the_same():
        _category_dict = dict()
        for _m in modes:
            find_key = False
            for _mode_key in _category_dict:
                if dynamic_syntatic_eqaulity(_m.dynamics, _mode_key.dynamics) and _invariant_eq(_m.invariant,
                                                                                                _mode_key.invariant):
                    _category_dict[_mode_key].add(_m)
                    find_key = True
                    break
            if not find_key:
                _category_dict[_m] = {_m}

        assert len(_category_dict) == 1
        # get a representative key
        return _category_dict

    category_dict = _all_modes_are_the_same()
    key = list(category_dict.keys())[0]
    new_agg_mode = AggregatedMode("mode", category_dict[key], ha)
    new_agg_mode.set_dynamics(key.dynamics)
    new_agg_mode.set_invariant(key.invariant)

    for _modes in category_dict[key]:
        mode_inv = _remove_forall_from_invariant(_modes.invariant)
        for out_going_trans in _modes.outgoing:
            g = out_going_trans.guard
            # flatten guard constraint if it is And
            if mode_inv is None:
                out_going_trans.src = new_agg_mode
                new_agg_mode.outgoing.add(out_going_trans)
            else:
                if isinstance(g, And):
                    children = g.children.copy()
                    children.extend(mode_inv)
                    out_going_trans.set_guard(And(children))
                    out_going_trans.src = new_agg_mode
                    new_agg_mode.outgoing.add(out_going_trans)
                else:
                    children = mode_inv.copy()
                    children.append(g)
                    out_going_trans.src = new_agg_mode
                    out_going_trans.set_guard(And(children))
        for in_coming_trans in _modes.incoming:
            in_coming_trans.trg = new_agg_mode
            new_agg_mode.incoming.add(in_coming_trans)

    return new_agg_mode, True


def merge_mode_syntatically(m1: BaseMode, m2: BaseMode, ha: HybridAutomaton) -> Tuple[
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

    def _invariant_eq(c: And, c1: And):
        if c is None and c1 is None:
            return True

        if c is None or c1 is None:
            return False

        assert isinstance(c, And) and isinstance(c1, And)
        return elements_of_tree(c) == elements_of_tree(c1)

    if dynamic_syntatic_eqaulity(m1.dynamics, m2.dynamics):
        m1_inv_without_forall = _remove_forall_from_invariant(m1.invariant)
        m2_inv_without_forall = _remove_forall_from_invariant(m2.invariant)

        # invariants to be checked subsumption relation
        m1_inv = None
        m2_inv = None
        if m1_inv_without_forall is not None:
            m1_inv = And(m1_inv_without_forall)

        if m2_inv_without_forall is not None:
            m2_inv = And(m2_inv_without_forall)

        if not _invariant_eq(m1_inv, m2_inv):
            return None, False

        new_agg_mode = AggregatedMode("{}_{}".format(m1.name, m2.name), set(), ha)
        new_agg_mode.add(m1)
        new_agg_mode.add(m2)
        new_agg_mode.set_dynamics(m1.dynamics)

        new_out_going = set()
        new_out_going = new_out_going.union(m1.outgoing)
        new_out_going = new_out_going.union(m2.outgoing)

        new_agg_mode.set_invariant(m1.invariant)

        for out_going_trans in new_out_going:
            g = out_going_trans.guard
            # flatten guard constraint if it is And
            if isinstance(g, And):
                children = g.children.copy()
                if m1.invariant is not None and out_going_trans.belongs_to() is m1.belongs_to():
                    children.extend(m1_inv_without_forall)
                elif m2.invariant is not None and out_going_trans.belongs_to() is m2.belongs_to():
                    children.extend(m2_inv_without_forall)
                out_going_trans.set_guard(And(children))
            else:
                if m1.invariant is not None and out_going_trans.belongs_to() is m1.belongs_to():
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

    if dynamic_syntatic_eqaulity(m1.dynamics, m2.dynamics):
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


def merge_transition_syntatically(trans1: Transition, trans2: Transition):
    if id(trans1.src) == id(trans2.src) and id(trans1.trg) == id(trans2.trg):
        if trans1.guard is None and trans2.guard is None:
            return True

        if trans1.guard is None or trans2.guard is None:
            return False

        if trans1.reset is None and trans2.reset is None:
            return True

        if trans1.reset is None or trans2.reset is None:
            return False

        guard_eq = elements_of_tree(trans1.guard) == elements_of_tree(trans2.guard)
        reset_eq = elements_of_tree(trans1.reset) == elements_of_tree(trans2.reset)
        return guard_eq and reset_eq
    return False


def merge_transition_pool_syntatically(trans_set: Set[Transition], ha: HybridAutomaton) -> Set[Transition]:
    def _categorize():
        _categories = dict()
        for _trans in trans_set:
            find_key = False
            for _trans_key in _categories:
                if merge_transition_syntatically(_trans, _trans_key):
                    find_key = True
                    _categories[_trans_key].add(_trans)
                    break

            if not find_key:
                _categories[_trans] = {_trans}
        return _categories

    categories = _categorize()
    transitions = set()
    for _trans in categories:
        _new_trans = Transition(_trans.name, _trans.src, _trans.trg, ha)
        _new_trans.set_guard(_trans.guard)
        _new_trans.set_reset(_trans.reset)
        transitions.add(_new_trans)

    return transitions


def new_merge(*hybrid_automata, **option):
    """
    Merge given hybrid automata. In order to merged, two hybrid automaton must have the common
    terminal nodes. See a test case with the different length.

    :param hybrid_automata: Any hybrid automata
    :param option: chi_optimization True to enable chi optimization else false
    :return: A new merged hybrid automata
    """
    chi_keyword = "chi_optimization"
    syntatic_keyword = "syntatic_merging"
    is_optimize = False
    is_syntatic = False
    if chi_keyword in option.keys():
        if isinstance(option[chi_keyword], bool):
            is_optimize = option[chi_keyword]
    if syntatic_keyword in option.keys():
        if isinstance(option[syntatic_keyword], bool):
            is_syntatic = option[syntatic_keyword]

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

    def _categorize_with_invs(_hybrid_automata_mode_queue):
        def _invariant_eq(c: And, c1: And):
            if c is None and c1 is None:
                return True

            if c is None or c1 is None:
                return False

            assert isinstance(c, And) and isinstance(c1, And)
            return elements_of_tree(c) == elements_of_tree(c1)

        _category_dict = dict()
        for _mode in _hybrid_automata_mode_queue:
            _find_key = False
            for _mode_key in _category_dict:
                if dynamic_syntatic_eqaulity(_mode_key.dynamics, _mode.dynamics) and _invariant_eq(_mode_key.invariant,
                                                                                                   _mode.invariant):
                    _find_key = True
                    _category_dict[_mode_key].add(_mode)
                    break
            if not _find_key:
                _category_dict[_mode] = {_mode}
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

    terminal_merged_modes = set()
    further_remove_mode_queue = set()
    merged_ha_name = "new_agg_mode"
    for hybrid_automaton in hybrid_automata:
        merged_ha_name = "{}__{}".format(merged_ha_name, hybrid_automaton.name)
        for terminal_node in _get_terminal_nodes(hybrid_automaton):
            waiting_queue.add(terminal_node)

    merged_ha = HybridAutomaton(merged_ha_name)

    # print("this is waiting queue {}".format(waiting_queue))
    is_reset_waiting_queue = False
    logger = Logger()
    logger.start_timer("mode merging")
    merging_counter = 0
    inner_logger = Logger()
    while len(waiting_queue) > 0:
        inner_logger.start_timer("mode merging timer")
        merging_counter += 1

        inner_logger.start_timer("new categorize timer")
        categories = _categorize_with_invs(waiting_queue)
        inner_logger.stop_timer("new categorize timer")

        # print(waiting_queue)
        is_update = False
        inner_logger.start_timer("possible merging timer")
        for c in categories:
            categories_queue = categories[c]
            merged_mode, _ = merge_mode_pool_syntatically(categories_queue, merged_ha)
            all_merged_modes.add(merged_mode)

            if merging_counter == 1:
                terminal_merged_modes.add(merged_mode)

        inner_logger.stop_timer("possible merging timer")

        new_waiting_queue = set()
        for _mode in waiting_queue:
            for _trans in _mode.incoming:
                new_waiting_queue.add(_trans.src)

        inner_logger.stop_timer("mode merging timer")
        print("mode merging ... {} (depth {}) --> categorize : {} --> possible merging : {} --> total : {})".format(
            len(waiting_queue),
            merging_counter,
            inner_logger.get_duration_time("new categorize timer"),
            inner_logger.get_duration_time("possible merging timer"),
            inner_logger.get_duration_time("mode merging timer")), flush=True)
        inner_logger.reset_timer()
        waiting_queue.clear()
        waiting_queue = new_waiting_queue

    logger.stop_timer("mode merging")
    print("mode merging time : {}".format(logger.get_duration_time("mode merging")), flush=True)

    def _update_mode_name(_mode: BaseMode):
        _mode_belongs_to = _mode.belongs_to().name
        if _mode_belongs_to == merged_ha_name:
            _mode.name = "{}_{}".format(_mode_belongs_to, _mode.name)
        else:
            _mode.name = "{}_{}_{}".format(merged_ha_name, _mode_belongs_to, _mode.name)
        merged_ha.modes.add(_mode)

    for m in all_merged_modes:
        _update_mode_name(m)

    def _update_trans_name(_trans: Transition):
        _trans_belongs_to = _trans.belongs_to().name
        if _trans_belongs_to == merged_ha_name:
            _trans.name = "{}_{}".format(_trans_belongs_to, _trans.name)
        else:
            _trans.name = "{}_{}_{}".format(merged_ha_name, _trans_belongs_to, _trans.name)
        merged_ha.transitions.add(trans)

    transition_queue = set()
    for _m in terminal_merged_modes:
        transition_queue = transition_queue.union(_m.incoming)

    inner_logger.reset_timer()
    merged_transitions = set()
    transition_merged_counter = 0
    logger.start_timer("total trans merging timer")
    while len(transition_queue) > 0:
        inner_logger.start_timer("trans merging timer")
        transition_merged_counter += 1
        _merged_transitions = merge_transition_pool_syntatically(transition_queue, merged_ha)
        merged_transitions = merged_transitions.union(_merged_transitions)

        new_transition_queue = set()
        for _trans in transition_queue:
            new_transition_queue = new_transition_queue.union(_trans.src.incoming)
        inner_logger.stop_timer("trans merging timer")
        print("trans merging ... {} (depth {}, size {})".format(inner_logger.get_duration_time("trans merging timer"),
                                                                transition_merged_counter, len(transition_queue)),
              flush=True)
        transition_queue.clear()
        transition_queue = new_transition_queue
        inner_logger.reset_timer()
    logger.stop_timer("total trans merging timer")
    print("total transition merging ... {}".format(logger.get_duration_time("total trans merging timer")), flush=True)

    for trans in merged_transitions:
        _update_trans_name(trans)

    return merged_ha


def merge(*hybrid_automata, **option):
    """
    Merge given hybrid automata. In order to merged, two hybrid automaton must have the common
    terminal nodes. See a test case with the different length.

    :param hybrid_automata: Any hybrid automata
    :param option: chi_optimization True to enable chi optimization else false
    :return: A new merged hybrid automata
    """
    chi_keyword = "chi_optimization"
    syntatic_keyword = "syntatic_merging"
    is_optimize = False
    is_syntatic = False
    if chi_keyword in option.keys():
        if isinstance(option[chi_keyword], bool):
            is_optimize = option[chi_keyword]
    if syntatic_keyword in option.keys():
        if isinstance(option[syntatic_keyword], bool):
            is_syntatic = option[syntatic_keyword]

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

    def _categorize_with_invs(_hybrid_automata_mode_queue):
        def _invariant_eq(c: And, c1: And):
            if c is None and c1 is None:
                return True

            if c is None or c1 is None:
                return False

            assert isinstance(c, And) and isinstance(c1, And)
            return elements_of_tree(c) == elements_of_tree(c1)

        _category_dict = dict()
        for _mode in _hybrid_automata_mode_queue:
            _find_key = False
            for _mode_key in _category_dict:
                if dynamic_syntatic_eqaulity(_mode_key.dynamics, _mode.dynamics) and _invariant_eq(_mode_key.invariant,
                                                                                                   _mode.invariant):
                    _find_key = True
                    _category_dict[_mode_key].add(_mode)

            if not _find_key:
                _category_dict[_mode] = set()
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
    inner_logger = Logger()
    while len(waiting_queue) > 0:
        inner_logger.start_timer("mode merging timer")
        merging_counter += 1
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

        inner_logger.start_timer("categorize timer")
        categories = _categorize(waiting_queue)
        inner_logger.stop_timer("categorize timer")

        inner_logger.start_timer("new categorize timer")
        new_categories = _categorize_with_invs(waiting_queue)
        inner_logger.stop_timer("new categorize timer")

        print("  new categorize timer : {}".format(inner_logger.get_duration_time("new categorize timer")))

        # print(waiting_queue)
        is_update = False
        inner_logger.start_timer("possible merging timer")
        for c in categories:
            # print("normal => {}".format(categories))
            print("  size of categories : {}".format(len(categories[c])))
            possibilities = list(combinations(categories[c], 2))
            if len(possibilities) == 0:
                is_reset_waiting_queue = True
                break

            for (m1, m2) in possibilities:
                print("  size of possibilities : {}".format(len(possibilities)))
                # print("is optimize {}".format(is_optimize))
                is_same_valuation = _check_chi_valuation(m1.chi_valuation, m2.chi_valuation, is_optimize)
                # print("{}, {} : and {}, {} => {}".format(m1.belongs_to().name, m1.name, m2.belongs_to().name, m2.name,
                #                                          is_same_valuation, m1 is m2))
                if is_same_valuation:
                    # print("valuation")
                    if is_syntatic:
                        merged_mode, is_merged = merge_mode_syntatically(m1, m2, merged_ha)
                    else:
                        merged_mode, is_merged = merge_mode(m1, m2, merged_ha)
                    if is_merged:
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
        inner_logger.stop_timer("possible merging timer")
        # remove modes in the removing queue
        if is_optimize:
            if len(further_remove_mode_queue) > 0:
                is_reset_waiting_queue = True

        if is_update is False:
            is_reset_waiting_queue = True

        inner_logger.stop_timer("mode merging timer")
        print("mode merging ... {} (step {}) --> categorize : {} --> possible merging : {} --> total : {})".format(
            len(waiting_queue),
            merging_counter,
            inner_logger.get_duration_time("categorize timer"),
            inner_logger.get_duration_time("possible merging timer"),
            inner_logger.get_duration_time("mode merging timer")), flush=True)
        inner_logger.reset_timer()

    logger.stop_timer("mode merging")
    print("mode merging time : {}".format(logger.get_duration_time("mode merging")), flush=True)

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

    # reduced_merged_trans = all_merged_trans.copy()
    # reduce transition

    def _make_splited_dict(_mode):
        _split_dict = dict()
        for _in_trans in _mode.incoming:
            if _in_trans.src in _split_dict:
                _split_dict[_in_trans.src].add(_in_trans)
            else:
                _split_dict[_in_trans.src] = {_in_trans}
        return _split_dict

    def _transition_pool_fixed_point_calculator(_transition_pool: set):
        _merging_counter = 0
        while True:
            _merging_counter += 1
            print("transition merging ... {}".format(len(_transition_pool)), end="", flush=True)
            _reduced_merged_trans_before = _transition_pool.copy()
            _possible_transitions = list(combinations(_transition_pool, 2))
            for (_trans1, _trans2) in _possible_transitions:
                if is_syntatic:
                    if merge_transition(_trans1, _trans2):
                        _transition_pool.remove(_trans1)
                        break
                else:
                    if merge_transition_syntatically(_trans1, _trans2):
                        _transition_pool.remove(_trans1)
                        break
            if _reduced_merged_trans_before.issubset(_transition_pool) and \
                    _reduced_merged_trans_before.issuperset(_transition_pool):
                print(" (step {}) (reach fixed point)".format(_merging_counter), flush=True)
                break
            print(" (step {})".format(_merging_counter), flush=True)
        return _transition_pool

    reduced_merged_queue = set(_get_terminal_nodes(merged_ha))
    reduced_merged_trans = set()
    next_reduced_merged_queue = set()
    for rmq in reduced_merged_queue:
        next_reduced_merged_queue.add(rmq)

    logger.start_timer("transition merging")

    merging_counter = 0
    while len(next_reduced_merged_queue) > 0:
        if merging_counter > 0:
            reduced_merged_queue = next_reduced_merged_queue.copy()
        next_reduced_merged_queue.clear()
        while len(reduced_merged_queue) > 0:
            merging_counter += 1
            possible_mode = reduced_merged_queue.pop()
            for incoming_transition in possible_mode.incoming:
                next_reduced_merged_queue.add(incoming_transition.src)
            _split_dict = _make_splited_dict(possible_mode)

            for _mode in _split_dict:
                _split_reduced_merged = _split_dict[_mode]
                reduced_merged_trans.update(_transition_pool_fixed_point_calculator(_split_reduced_merged))
    logger.stop_timer("transition merging")
    print("transition merging time : {}".format(logger.get_duration_time("transition merging")), flush=True)
    # logger.start_timer("transition merging")
    # merging_counter = 0
    # while True:
    #     merging_counter += 1
    #     print("transition merging ... {}".format(len(reduced_merged_trans)), end="")
    #     reduced_merged_trans_before = reduced_merged_trans.copy()
    #     possible_transitions = list(combinations(reduced_merged_trans, 2))
    #     for (trans1, trans2) in possible_transitions:
    #         # print("=======>>")
    #         # print(trans1)
    #         # print(trans2)
    #         if merge_transition(trans1, trans2):
    #             # print("=======>>")
    #             # print("{}_id_{} => ( {} ) {}_id_{}".format(trans1.src.name, id(trans1.src), trans1, trans1.trg, id(trans1.trg)))
    #             # print("{}_id_{} => ( {} ) {}_id_{}".format(trans2.src.name, id(trans2.src), trans2, trans2.trg, id(trans2.trg)))
    #             reduced_merged_trans.remove(trans1)
    #             break
    #     if reduced_merged_trans_before.issubset(reduced_merged_trans) and \
    #             reduced_merged_trans_before.issuperset(reduced_merged_trans):
    #         print(" (step {}) (reach fixed point)".format(merging_counter))
    #         break
    #     print(" (step {})".format(merging_counter))
    # logger.stop_timer("transition merging")
    # print("transition merging time : {}".format(logger.get_duration_time("transition merging")))
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
        print("searching for mergable mode ... {}".format(merge_counter), flush=True)
        merged_mode, is_merged = merge_mode(mode_at_depth, mode, ha)
        found_mergable_mode = found_mergable_mode or is_merged

    if found_mergable_mode:
        print("found mergable mode : {}".format(merged_mode), flush=True)
        _set_ha(mode)
    else:
        print("found no mergable mode", flush=True)


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