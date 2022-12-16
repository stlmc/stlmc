from .aux import translate_formula, tau_max
from .clock import *
from .graph import *
from .label import TimeProposition
from .optimizer import reduce
from ....constraints.aux.operations import VarSubstitution, inf, sup, variable_equal
from ....hybrid_automaton.hybrid_automaton import *


class HAConverter:
    def __init__(self, tau_subst: VarSubstitution):
        self._tau_subst: VarSubstitution = tau_subst
        self._node2mode_dict: Dict[Node, Mode] = dict()

    def clear(self):
        self._node2mode_dict.clear()

    @classmethod
    def _get_clocks(cls, graph: TableauGraph) -> Set[Real]:
        clk_s = set()
        for n in graph.get_nodes():
            clk_s.update(get_clock_pool(*n.goals))
        return clk_s

    @classmethod
    def _make_time_dynamics(cls, clock_vars: Set[Real]) -> Set[Tuple[Real, RealVal]]:
        d_s, one = set(), RealVal("1.0")
        # add global clock
        d_s.add((global_clk(), one))

        for clk in clock_vars:
            d_s.add((clk, one))
        return d_s

    def convert(self, graph: TableauGraph):
        self.clear()

        automata = HybridAutomaton()

        # get all clock variables used in goals
        # and make time dynamics (i.e., d{clk}/dt = 1)
        clk_s = self._get_clocks(graph)
        d_s = self._make_time_dynamics(clk_s)

        # get node information
        g_d, i_d, r_d, t_d = self._get_node_info(graph)

        for index, node in enumerate(graph.get_nodes()):
            mode = self._make_mode(index + 1, node.is_initial(), node.is_final())

            assert node in i_d
            mode.add_invariant(*i_d[node])
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

            assert t in g_d and t in r_d and t in t_d

            tr = Transition(s_m, t_m)
            tr.add_guard(*g_d[t])
            tr.add_reset(*r_d[t])

            # if trg is in time bound
            if t_d[t]:
                # make time bound consts
                b_c = global_clk() >= tau_max()
                assert isinstance(b_c, Geq)

                b_c = self._tau_subst.substitute(b_c)
                tr.add_guard(b_c)

            automata.add_transition(tr)

        self._remove_equiv_transitions(automata)
        return automata

    def _get_node_info(self, graph: TableauGraph) -> Tuple[Dict[Node, Set[Formula]],
                                                           Dict[Node, Set[Formula]],
                                                           Dict[Node, Set[Tuple[Real, RealVal]]],
                                                           Dict[Node, bool]]:
        g_d, i_d, r_d, t_d = dict(), dict(), dict(), dict()
        # make mode
        for node in graph.get_nodes():
            g, inv, r, tb = self._translate_goals(*node.goals)

            assert node not in g_d
            g_d[node] = g

            assert node not in i_d
            i_d[node] = inv

            assert node not in r_d
            r_d[node] = r

            assert node not in t_d
            t_d[node] = tb

        return g_d, i_d, r_d, t_d

    @classmethod
    def _make_mode(cls, node_id: int, is_initial=False, is_final=False) -> Mode:
        mode = Mode(node_id)

        if is_final:
            mode.set_as_final()

        if is_initial:
            mode.set_as_initial()

        return mode

    def _translate_goals(self, *goals) -> Tuple[Set[Formula], Set[Formula],
                                                Set[Tuple[Real, RealVal]], bool]:
        tau_subst = self._tau_subst

        is_time_bound = False
        # get guards, invariants, and time resets from the goals
        guard, inv, r_s = set(), set(), set()
        for g in goals:
            if isinstance(g, TimeProposition):
                t_f = tau_subst.substitute(_translate_time_goal(g))
                # time propositions go to pre-guard
                guard.add(t_f)
                # print("@{} :: {} --> {}".format(node.depth, f, t_f))

                # t_f, r = reduce(t_f)

                # if r:
                #     self._add_to_guard(mode, t_f)
            elif isinstance(g, TimeBound):
                is_time_bound = True
            elif isinstance(g, ClkReset):
                # clock resets go to pre-guard resets
                r_s.add((g.clock, g.value))
            elif isinstance(g, Proposition):
                # other propositions go to invariant
                inv.add(g)
            else:
                # ignore other cases
                continue
        return guard, inv, r_s, is_time_bound

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


@singledispatch
def _translate_time_goal(formula: Formula) -> Formula:
    return formula


@_translate_time_goal.register(TimeGloballyPre)
def _(formula: TimeGloballyPre) -> Formula:
    # ignore strict case
    return formula.clock <= inf(formula.interval)


@_translate_time_goal.register(TimeGloballyFinal)
def _(formula: TimeGloballyFinal) -> Formula:
    # ignore strict case
    return formula.clock <= sup(formula.interval)


@_translate_time_goal.register(TimeBound)
def _(formula: TimeBound) -> Formula:
    return tau_max()
