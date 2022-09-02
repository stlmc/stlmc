from itertools import product
from typing import Tuple

from ..constraints.aux.operations import get_vars
from ..hybrid_automaton.hybrid_automaton import *


def composition(ha1: HybridAutomaton, ha2: HybridAutomaton) -> HybridAutomaton:
    ha = HybridAutomaton()

    # ha1vars, ha2vars = get_ha_vars(ha1), get_ha_vars(ha2)
    # v_s = ha1vars.union(ha2vars)

    ha.add_init(*ha1.init)
    ha.add_init(*ha2.init)

    candidate_modes: Set[Tuple[Mode, Mode]] = set(product(ha1.modes, ha2.modes))
    mode_dict: Dict[Tuple[Mode, Mode], Mode] = dict()

    for m_id, (mode1, mode2) in enumerate(candidate_modes):
        mode = _compose_modes(mode1, mode2, m_id + 1)
        mode_dict[(mode1, mode2)] = mode
        ha.add_mode(mode)

    for mode1, mode2 in candidate_modes:
        mode = mode_dict[(mode1, mode2)]
        make_composed_jump(mode, mode1, mode_dict)
        make_composed_jump(mode, mode2, mode_dict)

    # assert no redundant mode exists
    for mode in ha.modes.copy():
        if len(mode.pred) == 0 and len(mode.succ) == 0:
            if not mode.is_initial() or not mode.is_final():
                raise Exception("redundant mode found")
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


def make_composed_jump(composed_mode: Mode, mode: Mode, mode_dict: Dict[Tuple[Mode, Mode], Mode]):
    for succ in mode.succ:
        found = _find_composed_modes(succ, mode_dict)

        assert succ in mode.s_jumps
        jp_s = mode.s_jumps[succ]

        for m_found in found:
            for jp in jp_s:
                new_jp = make_jump(composed_mode, m_found)
                _copy_jump(jp, new_jp)

    for pred in mode.pred:
        found = _find_composed_modes(pred, mode_dict)

        assert pred in mode.p_jumps
        jp_s = mode.p_jumps[pred]

        for m_found in found:
            for jp in jp_s:
                new_jp = make_jump(m_found, composed_mode)
                _copy_jump(jp, new_jp)


def _find_composed_modes(mode: Mode, mode_dict: Dict[Tuple[Mode, Mode], Mode]) -> Set[Mode]:
    found: Set[Mode] = set()
    for pair in mode_dict:
        if mode in pair:
            found.add(mode_dict[pair])

    return found


def _copy_jump(src_jp: Transition, trg_jp: Transition):
    trg_jp.add_guard(*src_jp.guard)
    trg_jp.add_reset(*src_jp.reset)


def get_ha_vars(ha: HybridAutomaton) -> Set[Variable]:
    var_set = set()
    for m in ha.modes:
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
    jps_set: Set[Transition] = set()
    for m in ha.modes:
        for p_m in m.p_jumps:
            jps_set.update(m.p_jumps[p_m])

        for s_m in m.s_jumps:
            jps_set.update(m.s_jumps[s_m])

    return jps_set
