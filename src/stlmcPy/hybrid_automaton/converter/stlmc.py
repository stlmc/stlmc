from .converter import Converter
from ..utils import *
from ...encoding.automata.goal.label import *
from ...objects.configuration import Configuration


class StlmcConverter(Converter):
    def __init__(self, config: Configuration):
        self._string = ""
        self.config: Configuration = config

    def convert(self, ha: HybridAutomaton):
        self._reset()
        self._preprocessing(ha)
        ha_vs = get_ha_vars(ha)

        # make variable declarations
        # currently, continuous variables' bounds should be given manually
        v_decl = ["int modeId;", "bool final;"]
        for v in ha_vs:
            v_decl.append("# [-9999, 9999] {};".format(v))
        v_s = "\n".join(v_decl)

        m_s = ""
        for m in ha.get_modes():
            # make inv
            inv_s = ["{};".format(f) for f in m.invariant]

            # make flow
            flow_s = ["d/dt[{}] = {};".format(v, m.dynamics[v]) for v in m.dynamics]

            # make jump
            jp_s = list()
            for jp in ha.get_next_edges(m):
                # pre
                if len(jp.guard) == 1:
                    jp_pre = str(jp.guard.copy().pop())
                elif len(jp.guard) <= 0:
                    jp_pre = "true"
                else:
                    jp_pre = "(and {})".format(" ".join(["({})".format(g) for g in jp.guard]))

                # post
                jp_post_l = ["(modeId' = {})".format(jp.get_trg().id)]
                if jp.get_trg().is_final():
                    jp_post_l.append("(final' = true)")
                else:
                    jp_post_l.append("(final' = false)")

                for v, f in jp.reset:
                    jp_post_l.append("({}' = {})".format(v, f))

                jp_post = "(and {})".format(" ".join(jp_post_l))

                jp_s.append("{} => {};".format(jp_pre, jp_post))

            if m.is_final():
                mode_s = "mode: modeId = {}; final;".format(m.id)
            else:
                mode_s = "mode: modeId = {}; final = false;".format(m.id)

            m_str = [
                "{{ {}".format(mode_s),
                "  inv: \n{}".format("\n".join([indented_str(i_s, 4) for i_s in inv_s])),
                "  flow: \n{}".format("\n".join([indented_str(f, 4) for f in flow_s])),
                "  jump: \n{}".format("\n".join([indented_str(jp, 4) for jp in jp_s])),
                "}"
            ]

            m_s += "\n".join(m_str) + "\n"

        # make initial conditions
        init = ["init:"]
        init.extend(indented_str("{};".format(f), 2) for f in ha.init)
        init.append(indented_str("(final = false);", 2))

        init_m = ""
        init_modes = list(filter(lambda x: x.is_initial(), ha.get_modes()))

        # there must at least more than one initial modes
        assert len(init_modes) > 0
        if len(init_modes) == 1:
            init_m += "(modeId = {});".format(init_modes[0].id)
        else:
            init_m_s = list()
            for i_m in init_modes:
                init_m_s.append("(modeId = {})".format(i_m.id))
            init_m = "(or {});".format(" ".join(init_m_s))

        init.append(indented_str(init_m, 2))
        init_s = "\n".join(init)

        goal = ["goal:",
                indented_str("reach final;", 2)]
        goal_s = "\n".join(goal)

        self._string = "{}\n{}\n{}\n\n{}\n".format(v_s, m_s, init_s, goal_s)

    def write(self, file_name: str):
        common_section = self.config.get_section("common")
        g_n, b = common_section.get_value("goal"), common_section.get_value("bound")

        stl_n = "{}_{}_b{}_stlmc.model".format(file_name, g_n, b)
        f = open(stl_n, "w")
        f.write(self._string)
        f.close()
        print("write hybrid automaton to {}".format(stl_n))

    def _preprocessing(self, ha: HybridAutomaton):
        self._make_dummy_initial(ha)
        self._make_self_resets(ha)

    @classmethod
    def _make_self_resets(cls, ha: HybridAutomaton):
        # add self resets
        ha_v = get_ha_vars(ha)
        jp_s = get_jumps(ha)
        for jp in jp_s:
            # get reset variables
            covered = set()
            for v, _ in jp.reset:
                covered.add(v)

            to_be_covered = ha_v.difference(covered)
            # add self reset for the rests
            for v in to_be_covered:
                jp.add_reset((v, v))

    @classmethod
    def _make_dummy_initial(cls, ha: HybridAutomaton):
        ha_v = get_ha_vars(ha)
        # get old initial modes
        ha_init_m = set(filter(lambda x: x.is_initial(), ha.get_modes()))

        g_clk, zero = Real("gClk"), RealVal("0.0")

        # make dummy initial
        initial = Mode(0)
        initial.add_invariant(g_clk <= RealVal("0.001"))
        initial.set_as_initial()
        for v in ha_v:
            initial.add_dynamic((v, zero))

        ha.add_mode(initial)

        for m in ha_init_m:
            m.set_as_non_initial()
            tr = Transition(initial, m)
            tr.add_guard(g_clk >= zero)
            ha.add_transition(tr)

    def _reset(self):
        self._string = ""
