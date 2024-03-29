from .graph import *
from .label import TimeProposition
from ....constraints.aux.operations import VarSubstitution
from ....hybrid_automaton.hybrid_automaton import *
from ....hybrid_automaton.utils import get_jumps
from ....objects.configuration import Configuration


class HAConverter:
    def __init__(self, tau_subst: VarSubstitution):
        self._tau_subst: VarSubstitution = tau_subst
        self._tau_subst.add(global_clk(), self._global_clk())
        self._node2mode_dict: Dict[Node, Mode] = dict()

    def clear(self):
        self._node2mode_dict.clear()

    @classmethod
    def _get_clocks(cls, graph: TableauGraph) -> Set[Real]:
        clk_s = set()
        for n in graph.get_nodes():
            clk_s.update(get_clock_pool(*n.cur_goals))
        return clk_s

    def _make_time_dynamics(self, clock_vars: Set[Real]) -> Set[Tuple[Real, RealVal]]:
        d_s, one = set(), RealVal("1.0")
        # add global clock
        d_s.add((self._global_clk(), one))

        for clk in clock_vars:
            d_s.add((clk, one))
        return d_s

    def _make_initial_bounds(self, clock_vars: Set[Real]) -> Set[Formula]:
        f_s = set()
        zero = RealVal("0.0")
        for clk in clock_vars:
            f_s.add(clk == zero)
        f_s.add(self._global_clk() == zero)
        return f_s

    def convert(self, graph: TableauGraph):
        self.clear()

        automata = HybridAutomaton()

        # get all clock variables used in goals
        # and make time dynamics (i.e., d{clk}/dt = 1)
        clk_s = self._get_clocks(graph)
        d_s = self._make_time_dynamics(clk_s)

        # make clock invariants
        clk_inv_s = self._make_clk_invariants(clk_s)

        # add initial bounds and conditions
        b_s = self._make_initial_bounds(clk_s)
        automata.add_init(*b_s)

        for index, node in enumerate(graph.get_nodes()):
            mode = self._make_mode(index + 1, node.is_initial(), node.is_final())

            # assert node in i_d
            # get non intermediate goals (i.e., invariants)
            inv, r = self._translate_goals(*self._non_intermediate(node.cur_goals))

            # assert no reset exist
            assert len(r) <= 0

            mode.add_invariant(*inv)
            mode.add_invariant(*clk_inv_s)
            mode.add_dynamic(*d_s)

            automata.add_mode(mode)

            self._node2mode_dict[node] = mode

        # get jumps, and make guard, reset information dictionaries
        jumps = get_node_jumps(graph)

        # make transition
        for jp in jumps:
            s, t = jp.get_src(), jp.get_trg()

            assert s in self._node2mode_dict
            assert t in self._node2mode_dict

            s_m, t_m = self._node2mode_dict[s], self._node2mode_dict[t]
            j_inv, j_r = self._translate_goals(*jp.get_ap())

            # there should be no self loop in the tableau
            assert s != t

            # if the jump has an open interval condition
            # do not add this as a jump
            if self._contain_open(*j_inv):
                continue

            # ignore close conditions
            j_inv = self._ignore_close(*j_inv)

            tr = Transition(s_m, t_m)
            tr.add_guard(*j_inv)
            tr.add_reset(*j_r)

            automata.add_transition(tr)

        # self._remove_equiv_transitions(automata)
        return automata

    @classmethod
    def _make_mode(cls, node_id: int, is_initial=False, is_final=False) -> Mode:
        mode = Mode(node_id)

        if is_final:
            mode.set_as_final()

        if is_initial:
            mode.set_as_initial()

        return mode
    
    def _make_clk_invariants(self, clocks: Set[Real]) -> Set[Formula]:
        inv_s, tau_subst = set(), self._tau_subst
        zero, tb = RealVal("0.0"), tau_max()
        for clk in clocks:
            inv_s.add(clk >= zero)
            inv_s.add(tau_subst.substitute(clk <= tb))
        return inv_s

    def _translate_goals(self, *goals) -> Tuple[Set[Formula], Set[Tuple[Real, RealVal]]]:
        tau_subst = self._tau_subst

        # get guards (invariants) and time resets from the goals
        guard_s, r_s = set(), set()
        for g in goals:
            if isinstance(g, TimeProposition) or isinstance(g, TimeBound):
                t_f = tau_subst.substitute(translate_time_goal(g))
                # time propositions go to pre-guard
                guard_s.add(t_f)
                # print("@{} :: {} --> {}".format(node.depth, f, t_f))

                # t_f, r = reduce(t_f)

                # if r:
                #     self._add_to_guard(mode, t_f)
            elif isinstance(g, ClkAssn):
                # clock resets go to pre-guard resets
                r_s.add((g.clock, g.value))
            elif isinstance(g, OCProposition):
                # ignore open close propositions
                continue
            elif isinstance(g, TimeFinal):
                continue
            elif isinstance(g, Proposition):
                # other propositions go to invariant
                guard_s.add(g)
            else:
                # ignore other cases
                continue
        return guard_s, r_s

    @classmethod
    def _global_clk(cls):
        return Real("gClk")

    @classmethod
    def _non_intermediate(cls, goals: Set[Formula]) -> Set[Formula]:
        return set(filter(lambda x: isinstance(x, Proposition), goals))

    @classmethod
    def _contain_open(cls, *goals) -> bool:
        # check if the goals contain any open conditions
        for g in goals:
            if isinstance(g, Open):
                return True
        return False

    @classmethod
    def _ignore_close(cls, *goals) -> Set[Formula]:
        return set(filter(lambda x: not isinstance(x, Close), goals))

    @classmethod
    def _remove_equiv_transitions(cls, automata: HybridAutomaton):
        # get jumps
        tr_s: Set[Transition] = set()
        for m in automata.get_modes():
            tr_s = tr_s.union(automata.get_next_edges(m))

        # make equivalent transition dictionary
        equiv = dict()
        for tr in tr_s:
            f_g, f_r = frozenset(tr.guard), frozenset(tr.reset)
            h = (tr.get_src(), f_g, f_r, tr.get_trg())

            if h in equiv:
                equiv[h].add(tr)
            else:
                equiv[h] = {tr}

        for h in equiv:
            # save one to be alive
            equiv[h].pop()

            # remove all the others
            for tr in equiv[h]:
                automata.remove_transition(tr)


class HaBoundProcessor:
    def __init__(self, config: Configuration):
        common_section = config.get_section("common")
        self._tb = float(common_section.get_value("time-bound"))
        self._bound = int(common_section.get_value("bound"))

    def _make_tb_invariant(self) -> Formula:
        tb, zero = RealVal(str(self._tb)), RealVal("0.0")
        g_clk = self._global_clk()
        return And([g_clk >= zero, g_clk <= tb])

    def _make_jp_bound_conditions(self) -> Optional[Tuple[Formula, Tuple[Real, Expr], Tuple[Real, Expr], Formula]]:
        one, zero, b_val = RealVal("1.0"), RealVal("0.0"), RealVal(str(self._bound))
        jb_c = self._jump_bound_counter()

        # jump-bound condition
        if self._bound < 0:
            return None
        else:
            jb_f = And([jb_c >= zero, jb_c <= b_val])
            jb_r = (jb_c, jb_c + one)
            jb_d = (jb_c, zero)
            jb_i = jb_c == zero

            return jb_f, jb_r, jb_d, jb_i

    def add_time_bound(self, ha: HybridAutomaton):
        # make time bound invariant
        tb_inv = self._make_tb_invariant()

        # add time bound invariant and jump bound condition
        for m in ha.get_modes():
            m.add_invariant(tb_inv)

    def add_jump_bound(self, ha: HybridAutomaton):
        # make jump bound invariant
        jb_c = self._make_jp_bound_conditions()

        # if jump bound conditions exists
        if jb_c is not None:
            _, _, _, jb_i = jb_c
            ha.add_init(jb_i)

        # add time bound invariant and jump bound condition
        for m in ha.get_modes():

            # if jump bound condition exists
            if jb_c is not None:
                jb_f, _, jb_d, _ = jb_c
                m.add_dynamic(jb_d)
                m.add_invariant(jb_f)

        # add jump bound to the resets and guards
        for jp in get_jumps(ha):
            # add jump bound condition if any exists
            if jb_c is not None:
                jb_f, jb_r, _, _ = jb_c
                jp.add_guard(jb_f)
                jp.add_reset(jb_r)

    @classmethod
    def _jump_bound_counter(cls):
        return Real("jbc")

    @classmethod
    def _global_clk(cls):
        return Real("gClk")
