from typing import List

from .aux import translate_formula, symbolic_interval
from .graph import *
from .label import TimeProposition
from .optimizer import reduce
from ....constraints.aux.operations import VarSubstitution, inf, sup, get_vars, variable_equal
from ....hybrid_automaton.hybrid_automaton import *


class HAConverter:
    def __init__(self, tau_subst: VarSubstitution):
        self._time_pre_guard: Dict[Mode, Set[Formula]] = dict()
        self._time_post_guard: Dict[Mode, Set[Formula]] = dict()
        self._tau_subst: VarSubstitution = tau_subst

        #
        self._clk_subst_dict: Dict[int, VarSubstitution] = dict()
        self._time_dyns: Set[Tuple[Real, Expr]] = set()
        self._time_resets_dict: Dict[int, Set[Tuple[Variable, Expr]]] = dict()

        #
        self._node2mode_dict: Dict[Node, Mode] = dict()
        self._mode_depth_dict: Dict[Mode, int] = dict()
        self._empty_final_mode = Mode(-1)
        self._empty_initial_mode = Mode(-2)

    def clear(self):
        self._time_pre_guard.clear()
        self._time_post_guard.clear()
        self._clk_subst_dict.clear()
        self._time_dyns.clear()
        self._time_resets_dict.clear()
        self._node2mode_dict.clear()
        self._mode_depth_dict.clear()
        self._empty_final_mode = Mode(-1)
        self._empty_initial_mode = Mode(-2)

    def convert(self, graph: Graph):
        automata = HybridAutomaton()
        max_depth = graph.get_max_depth()
        self._prepare(max_depth)

        # add time initial conditions
        _add_time_init(automata, max_depth)

        # make mode
        for index, node in enumerate(graph.nodes):
            mode = self._make_mode(node, index + 1)
            automata.add_mode(mode)

        # make outgoing jp
        for node in graph.nodes:
            self._make_jp(node)

        # add time conditions
        for node in graph.nodes:
            self._add_time_condition_at(automata, node)

        # _remove_equivalent_modes(automata, self._mode_depth_dict)
        # print(automata)
        return automata

    def _make_mode(self, node: Node, node_id: int) -> Mode:
        tau_subst = self._tau_subst
        clk_subst_dict, time_dyns = self._clk_subst_dict, self._time_dyns

        mode = Mode(node_id)
        mode.add_dynamic(*time_dyns)

        if node.is_final():
            mode.set_as_final()

        if node.is_initial():
            mode.set_as_initial()

        clk_subst = clk_subst_dict[node.depth]

        for f in node.non_intermediate:
            if isinstance(f, TimeProposition):
                t_f = tau_subst.substitute(translate_formula(f, node.depth))
                t_f = clk_subst.substitute(t_f)
                # print("@{} :: {} --> {}".format(node.depth, f, t_f))

                t_f, r = reduce(t_f)

                if r:
                    self._add_to_guard(mode, t_f)
            else:
                mode.add_invariant(translate_formula(f, node.depth))

        self._node2mode_dict[node] = mode
        self._mode_depth_dict[mode] = node.depth
        return mode

    def _make_jp(self, node: Node):
        mode = self._node2mode_dict[node]

        for s_node in node.succ:
            s_mode = self._node2mode_dict[s_node]
            jp = make_jump(mode, s_mode)
            jp.add_reset(*self._time_resets_dict[node.depth])

    def _add_time_condition_at(self, automaton: HybridAutomaton, node: Node):
        # move time guard to the next jump
        empty_initial_mode, empty_final_mode = self._empty_initial_mode, self._empty_final_mode
        mode = self._node2mode_dict[node]
        is_empty_final_needed = False
        is_empty_initial_needed = False

        # check if there's something to propagate
        if mode in self._time_pre_guard:
            t_pre_fs = self._time_pre_guard[mode]
            if mode.is_initial():
                is_empty_initial_needed = True
                mode.set_as_non_initial()
                jp = make_jump(empty_initial_mode, mode)
                jp.add_guard(*t_pre_fs)
            else:
                for p_m in mode.p_jumps:
                    for p_jp in mode.p_jumps[p_m]:
                        p_jp.add_guard(*t_pre_fs)

        # check if there's something to propagate
        if mode in self._time_post_guard:
            t_post_fs = self._time_post_guard[mode]
            if mode.is_final():
                is_empty_final_needed = True
                mode.set_as_non_final()
                jp = make_jump(mode, empty_final_mode)
                jp.add_guard(*t_post_fs)
                jp.add_reset(*self._time_resets_dict[node.depth])
            else:
                for s_m in mode.s_jumps:
                    for s_jp in mode.s_jumps[s_m]:
                        s_jp.add_guard(*t_post_fs)

        if is_empty_final_needed:
            automaton.add_mode(empty_final_mode)

        if is_empty_initial_needed:
            automaton.add_mode(empty_initial_mode)

    def _prepare(self, max_depth: int):
        self._clk_subst_dict = _global_clk_subst(max_depth)
        self._time_dyns = _time_dynamics(max_depth)
        self._time_resets_dict = _time_resets(max_depth)
        self._prepare_empty_mode(max_depth)

    def _prepare_empty_mode(self, max_depth: int):
        t_dyn = _time_dynamics(max_depth)

        self._empty_initial_mode.add_dynamic(*t_dyn)
        self._empty_initial_mode.set_as_initial()

        self._empty_final_mode.add_dynamic(*t_dyn)
        self._empty_final_mode.set_as_final()

        self._mode_depth_dict[self._empty_initial_mode] = self._empty_initial_mode.id
        self._mode_depth_dict[self._empty_final_mode] = self._empty_final_mode.id

    def _add_to_guard(self, mode: Mode, t_f: Formula):
        # if global clk contained move the post guard
        if _is_global_clk_in(t_f):
            _add_to_guard_dict(self._time_post_guard, mode, t_f)
        else:
            _add_to_guard_dict(self._time_pre_guard, mode, t_f)


def _add_time_init(automaton: HybridAutomaton, max_depth: int):
    s = set()
    time_vars: Set[Real] = _time_variables(max_depth)
    time_vars.add(_global_clk())
    zero = RealVal("0.0")
    for v in time_vars:
        s.add(v == zero)
    automaton.add_init(*s)


def _time_dynamics(max_depth: int) -> Set[Tuple[Real, Expr]]:
    time_vars: Set[Real] = _time_variables(max_depth)
    time_dyns: Set[Tuple[Real, Expr]] = set()

    clk = _global_clk()
    one, zero = RealVal("1.0"), RealVal("0.0")
    for v in time_vars:
        if variable_equal(v, clk):
            time_dyns.add((v, one))
        else:
            time_dyns.add((v, zero))

    return time_dyns


# def _time_resets(max_depth: int) -> Set[Tuple[Variable, Expr]]:
#     time_vars: Set[Real] = _time_variables(max_depth)
#     time_rsts: Set[Tuple[Variable, Expr]] = set()
#
#     for time_v in time_vars:
#         time_rsts.add((time_v, time_v))
#
#     return time_rsts


def _time_resets(max_depth: int) -> Dict[int, Set[Tuple[Real, Expr]]]:
    time_dict: Dict[int, Set[Tuple[Real, Expr]]] = dict()
    cur_depth = 1
    while max_depth >= cur_depth:
        time_dict[cur_depth] = _time_resets_at(cur_depth, max_depth)
        cur_depth += 1

    return time_dict


def _time_resets_at(cur_depth: int, max_depth: int) -> Set[Tuple[Real, Expr]]:
    time_resets: Set[Tuple[Real, Expr]] = set()
    clk = _global_clk()

    depth = 1
    while max_depth >= depth:
        interval = symbolic_interval(depth)
        s_v, e_v = inf(interval), sup(interval)

        if depth == cur_depth:
            time_resets.update({(s_v, s_v), (e_v, clk)})
        elif depth == cur_depth + 1:
            time_resets.add((e_v, e_v))
        else:
            time_resets.update({(s_v, s_v), (e_v, e_v)})

        depth += 1

    return time_resets


def _time_variables(max_depth: int) -> Set[Real]:
    time_vars: Set[Real] = {_global_clk()}
    cur_depth = 1
    while True:
        if cur_depth > max_depth:
            break
        interval = symbolic_interval(cur_depth)
        time_vars.update({inf(interval), sup(interval)})

        cur_depth += 1

    return time_vars


def _global_clk_subst(max_depth: int) -> Dict[int, VarSubstitution]:
    clk_dict: Dict[int, VarSubstitution] = dict()

    cur_depth = 1
    while cur_depth <= max_depth:
        clk_dict[cur_depth] = _global_clk_subst_at(cur_depth)
        cur_depth += 1

    return clk_dict


def _global_clk_subst_at(cur_depth: int) -> VarSubstitution:
    interval = symbolic_interval(cur_depth)

    subst = VarSubstitution()
    subst.add(sup(interval), _global_clk())
    return subst


def _global_clk():
    return Real("g@clk")


def _is_global_clk_in(formula: Formula) -> bool:
    return _global_clk() in get_vars(formula)


def _add_to_guard_dict(guard_dict: Dict[Mode, Set[Formula]], mode: Mode, t_f: Formula):
    if mode in guard_dict:
        guard_dict[mode].add(t_f)
    else:
        guard_dict[mode] = {t_f}


def _remove_equivalent_modes(ha: HybridAutomaton, mode_depth_dict: Dict[Mode, int]):
    equiv_rel = _calc_equivalent_relation(ha, mode_depth_dict)
    new_jps = set()
    to_be_removed = set()
    for mode in ha.modes:
        if _redundant_mode(mode, equiv_rel):
            to_be_removed.add(mode)
            new_jps.update(_reduce_mode(mode, equiv_rel))

    for m in to_be_removed:
        ha.remove_mode(m)

    for p, s, g, r in new_jps:
        jp = make_jump(p, s)
        jp.add_guard(*g)
        jp.add_reset(*r)


def _calc_equivalent_relation(ha: HybridAutomaton, mode_depth_dict: Dict[Mode, int]) -> Dict[Mode, Mode]:
    equiv: Dict[Mode, Set[Mode]] = dict()
    equiv_rel: Dict[Mode, Mode] = dict()
    waiting = ha.modes.copy()
    while len(waiting) > 0:
        mode = waiting.pop()
        mode_depth = mode_depth_dict[mode]

        to_be_removed = False
        for m in equiv:
            m_depth = mode_depth_dict[m]
            dyn_eq = m.dynamics == mode.dynamics
            inv_eq = m.invariant == mode.invariant
            type_eq = mode.is_final() == m.is_final() and mode.is_initial() == m.is_initial()
            depth_eq = mode_depth == m_depth
            if dyn_eq and inv_eq and type_eq and depth_eq:
                equiv[m].add(mode)
                to_be_removed = True

        if not to_be_removed:
            assert mode not in equiv
            equiv[mode] = {mode}

    for mode in equiv:
        modes = equiv[mode]
        for m in modes:
            assert m not in equiv_rel
            equiv_rel[m] = mode

    return equiv_rel


def _redundant_mode(mode: Mode, equiv_rel: Dict[Mode, Mode]) -> bool:
    rep = equiv_rel[mode]
    return mode != rep


def _reduce_mode(mode: Mode, equiv_rel: Dict[Mode, Mode]):
    new_jps: Set[Tuple[Mode, Mode, FrozenSet[Formula], FrozenSet[Tuple[Variable, Formula]]]] = set()
    rep = equiv_rel[mode]

    for s in mode.s_jumps:
        r_s = equiv_rel[s]
        for s_jp in mode.s_jumps[s]:
            new_jps.add((rep, r_s, frozenset(s_jp.guard), frozenset(s_jp.reset)))

    return new_jps

