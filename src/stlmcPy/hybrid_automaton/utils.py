from itertools import product
from typing import FrozenSet, Type

from ..constraints.aux.operations import get_vars
from ..hybrid_automaton.hybrid_automaton import *


def composition(ha1: HybridAutomaton, ha2: HybridAutomaton) -> HybridAutomaton:
    ha = HybridAutomaton()

    # ha1vars, ha2vars = get_ha_vars(ha1), get_ha_vars(ha2)
    # v_s = ha1vars.union(ha2vars)

    ha.add_init(*ha1.init)
    ha.add_init(*ha2.init)

    candidate_modes: Set[Tuple[Mode, Mode]] = set(product(ha1.get_modes(), ha2.get_modes()))
    mode_dict: Dict[Tuple[Mode, Mode], Mode] = dict()

    for m_id, (mode1, mode2) in enumerate(candidate_modes):
        mode = _compose_modes(mode1, mode2, m_id + 1)
        mode_dict[(mode1, mode2)] = mode
        ha.add_mode(mode)

    for mode1, mode2 in candidate_modes:
        _make_composed_jump((mode1, mode2), mode_dict, ha1, ha2)

    # assert no redundant mode exists
    for mode in ha.get_modes().copy():
        if len(mode.pred) == 0 and len(mode.succ) == 0:
            if not mode.is_initial() or not mode.is_final():
                raise Exception("redundant mode found")

    remove_equal_jumps(ha)

    return ha


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


def _make_composed_jump(composed_mode: Tuple[Mode, Mode], mode_dict: Dict[Tuple[Mode, Mode], Mode],
                        ha1: HybridAutomaton, ha2: HybridAutomaton):
    (mode1, mode2), c_mode = composed_mode, mode_dict[composed_mode]
    mode1_set, mode2_set = _find_composed_modes(composed_mode, mode_dict)

    for m_1 in mode1_set:
        # assert (m_1, mode2) in mode_dict
        trg_mode = mode_dict[(m_1, mode2)]

        if _jp_exists(mode1, m_1, ha1):
            for jp in _get_jp_s(mode1, m_1, ha1):
                new_jp = Transition(c_mode, trg_mode)
                copy_jump(jp, new_jp)

    for m_2 in mode2_set:
        # assert (mode1, m_2) in mode_dict
        trg_mode = mode_dict[(mode1, m_2)]

        if _jp_exists(mode2, m_2, ha2):
            for jp in _get_jp_s(mode2, m_2, ha2):
                new_jp = Transition(c_mode, trg_mode)
                copy_jump(jp, new_jp)


def _jp_exists(src: Mode, trg: Mode, ha: HybridAutomaton) -> bool:
    return trg in ha.get_next_vertices(src)


def _get_jp_s(src: Mode, trg: Mode, ha: HybridAutomaton) -> Set[Transition]:
    if trg not in ha.get_next_vertices(src):
        raise Exception("jump does not exist")

    jp_s = set()
    for jp in ha.get_next_edges(src):
        if jp.get_trg() == trg:
            jp_s.add(jp)
    return jp_s


def _find_composed_modes(composed_mode: Tuple[Mode, Mode],
                         mode_dict: Dict[Tuple[Mode, Mode], Mode]) -> Tuple[Set[Mode], Set[Mode]]:
    mode1_set: Set[Mode] = set()
    mode2_set: Set[Mode] = set()

    mode1, mode2 = composed_mode
    for m1, m2 in mode_dict:
        if m2 == mode2:
            mode1_set.add(m1)

        if m1 == mode1:
            mode2_set.add(m2)

    return mode1_set, mode2_set


def copy_jump(src_jp: Transition, trg_jp: Transition):
    trg_jp.add_guard(*src_jp.guard)
    trg_jp.add_reset(*src_jp.reset)


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
