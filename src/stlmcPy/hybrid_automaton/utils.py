from itertools import product
from typing import FrozenSet

from ..constraints.aux.operations import get_vars
from ..hybrid_automaton.hybrid_automaton import *
from ..solver.abstract_solver import SMTSolver
from ..solver.z3 import Z3Solver
from ..objects.configuration import *


def composition(ha1: HybridAutomaton, ha2: HybridAutomaton) -> HybridAutomaton:
    ha = HybridAutomaton()

    ha.add_init(*ha1.init)
    ha.add_init(*ha2.init)

    candidate_modes: Set[Tuple[Mode, Mode]] = set(product(ha1.get_modes(), ha2.get_modes()))
    mode_dict: Dict[Tuple[Mode, Mode], Mode] = dict()

    for m_id, (mode1, mode2) in enumerate(candidate_modes):
        mode = _compose_modes(mode1, mode2, m_id + 1)
        mode_dict[(mode1, mode2)] = mode
        ha.add_mode(mode)

    for mode1, mode2 in candidate_modes:
        _make_composed_jumps(mode1, mode2, candidate_modes, mode_dict, ha1, ha2, ha)

    # remove redundancy
    remove_unreachable(ha)
    remove_equal_jumps(ha)

    return ha


def _make_composed_jumps(mode1: Mode, mode2: Mode,  candidate_modes: Set[Tuple[Mode, Mode]], mode_dict: Dict[Tuple[Mode, Mode], Mode],
                         ha1: HybridAutomaton, ha2: HybridAutomaton, ha: HybridAutomaton) -> Set[Transition]:
    c_mode = mode_dict[mode1, mode2]

    for cn_m in candidate_modes:
        c_m = mode_dict[cn_m]
        m1, m2 = cn_m
        
        c_jp1, ty1, jp1_s = _can_jump(mode1, m1, ha1)
        c_jp2, ty2, jp2_s = _can_jump(mode2, m2, ha2)

        if c_jp1 and c_jp2:
            # if there is no transition exists
            if ty1 == ty2 == "stutt":
                continue

            assert len(jp1_s) > 0 or len(jp2_s) > 0

            if len(jp1_s) <= 0:
                jp1_s.add(Transition(mode1, m1))

            if len(jp2_s) <= 0:
                jp2_s.add(Transition(mode2, m2))

            tr_s: Set[Tuple[Transition, Transition]] = set(product(jp1_s, jp2_s))

            for tr1, tr2 in tr_s:
                new_jp = Transition(c_mode, c_m)
                new_jp.add_guard(*tr1.guard)
                new_jp.add_guard(*tr2.guard)

                new_jp.add_reset(*tr1.reset)
                new_jp.add_reset(*tr2.reset)
                
                ha.add_transition(new_jp)


def _can_jump(src: Mode, trg: Mode, ha: HybridAutomaton) -> Tuple[bool, str, Set[Transition]]:
    if _jp_exists(src, trg, ha):
        nxt = ha.get_next_edges(src)
        prd = ha.get_pred_edges(trg)
        return True, "yes", nxt.intersection(prd)
    elif src == trg:
        return True, "stutt", set()
    else:
        return False, "no", set()


def _compose_modes(mode1: Mode, mode2: Mode, m_id: int) -> Mode:
    mode = Mode(m_id)

    mode.add_dynamic(*{(v, mode1.dynamics[v]) for v in mode1.dynamics})
    mode.add_dynamic(*{(v, mode2.dynamics[v]) for v in mode2.dynamics})

    mode.add_invariant(*mode1.invariant)
    mode.add_invariant(*mode2.invariant)

    if mode1.is_initial() and mode2.is_initial():
        mode.set_as_initial()

    if mode1.is_final() and mode2.is_final():
        mode.set_as_final()

    return mode


def _jp_exists(src: Mode, trg: Mode, ha: HybridAutomaton) -> bool:
    return trg in ha.get_next_vertices(src)


def remove_unreachable(ha: HybridAutomaton):
    _remove_unreachable_to_final(ha)
    _remove_unreachable_from_initial(ha)


def _remove_unreachable_from_initial(ha: HybridAutomaton):
    f_ns = set(filter(lambda x: x.is_initial(), ha.get_modes()))
    new_states, reachable = f_ns.copy(), f_ns.copy()

    while len(new_states) > 0:
        temp = set()
        for s in new_states:
            temp.update(ha.get_next_vertices(s))
        new_states = temp.difference(reachable)
        reachable.update(new_states)

    unreachable = ha.get_modes().difference(reachable)
    for s in unreachable:
        ha.remove_mode(s)


def _remove_unreachable_to_final(ha: HybridAutomaton):
    f_ns = set(filter(lambda x: x.is_final(), ha.get_modes()))
    new_states, reachable = f_ns.copy(), f_ns.copy()

    while len(new_states) > 0:
        temp = set()
        for s in new_states:
            temp.update(ha.get_pred_vertices(s))
        new_states = temp.difference(reachable)
        reachable.update(new_states)

    unreachable = ha.get_modes().difference(reachable)
    for s in unreachable:
        ha.remove_mode(s)


def remove_contradiction(ha: HybridAutomaton):
    # make solver config
    config = Configuration()
    section = Section()
    section.name = "z3"
    section.arguments["logic"] = "QF_LRA"
    config.add_section(section)

    # initialize solver
    solver = Z3Solver(config)
    to_be_removed_modes = set()

    # 1) invariant contradiction checking
    for m in ha.get_modes():
        r = solver.check_sat(*m.invariant)
        
        # contradiction
        if r == SMTSolver.unsat:
            to_be_removed_modes.add(m)
    
    for m in to_be_removed_modes:
        ha.remove_mode(m)
    
    jp_s = get_jumps(ha)
    to_be_removed_jp_s = set()

    # 2) jump guard contradiction checking
    for jp in jp_s:
        r = solver.check_sat(*jp.guard)

        # contradiction
        if r == SMTSolver.unsat:
            to_be_removed_jp_s.add(jp)

    for jp in to_be_removed_jp_s:
        ha.remove_transition(jp)

    to_be_removed_jp_s.clear()

    # 3) incoming/outgoing guards and invariant contradiction
    for m in ha.get_modes():

        # incoming
        for jp in ha.get_pred_edges(m):
            r = solver.check_sat(*m.invariant.union(jp.guard))
            
            # contradiction
            if r == SMTSolver.unsat:
                to_be_removed_jp_s.add(jp)

        # outgoing
        for jp in ha.get_next_edges(m):
            r = solver.check_sat(*m.invariant.union(jp.guard))
            
            # contradiction
            if r == SMTSolver.unsat:
                to_be_removed_jp_s.add(jp)

    for jp in to_be_removed_jp_s:
        ha.remove_transition(jp)
    
    remove_unreachable(ha)


def remove_equal_jumps(ha: HybridAutomaton):
    eq_dict: Dict[Tuple[int, int, FrozenSet[Formula], FrozenSet[Tuple[Variable, Formula]]], Set[Transition]] = dict()
    jp_s = get_jumps(ha)
    for jp in jp_s:
        k = (jp.get_src().id, jp.get_trg().id, frozenset(jp.guard), frozenset(jp.reset))
        if k in eq_dict:
            eq_dict[k].add(jp)
        else:
            eq_dict[k] = {jp}

    for eq in eq_dict:
        eq_dict[eq].pop()
        for o_jp in eq_dict[eq]:
            ha.remove_transition(o_jp)


def get_ha_vars(ha: HybridAutomaton) -> Set[Variable]:
    var_set = set()
    for m in ha.get_modes():
        for v in m.dynamics:
            var_set.add(v)
            var_set.update(get_vars(m.dynamics[v]))

        for inv in m.invariant:
            var_set.update(get_vars(inv))

    jp_s = get_jumps(ha)

    for jp in jp_s:
        for guard in jp.guard:
            var_set.update(get_vars(guard))

        for v, e in jp.reset:
            var_set.add(v)
            var_set.update(get_vars(e))

    return var_set


def get_jumps(ha: HybridAutomaton) -> Set[Transition]:
    jp_s: Set[Transition] = set()
    for m in ha.get_modes():
        jp_s = jp_s.union(ha.get_next_edges(m))

    return jp_s


def print_ha_size(name: str, ha: HybridAutomaton):
    print(name)
    print(indented_str("v: {}, e: {}".format(len(ha.get_modes()), len(get_jumps(ha))), 2))
