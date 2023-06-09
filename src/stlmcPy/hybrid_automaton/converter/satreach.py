from functools import singledispatch

from .converter import Converter
from .spaceex import _make_model, _make_conf
from ..hybrid_automaton import *
from ..utils import get_ha_vars, get_jumps
from ...constraints.constraints import *
from ...constraints.aux.operations import VarSubstitution
from ...objects.configuration import Configuration


class SatReachConverter(Converter):
    def __init__(self, config: Configuration):
        self._model_string = ""
        self._config_string = ""
        self._config: Configuration = config

    def convert(self, ha: HybridAutomaton):
        self._reset()
        self._preprocessing_sat_reach(ha)

        # use spaceex converter
        self._model_string = _make_model(ha)
        self._config_string = _make_conf(ha, self._config)

    def write(self, file_name: str):
        common_section = self._config.get_section("common")
        g_n, bound = common_section.get_value("goal"), int(common_section.get_value("bound"))

        if bound < 0:
            b = "ub"
        else:
            b = "b{}".format(bound)

        m_n = "{}_{}_{}_sr.xml".format(file_name, g_n, b)
        c_n = "{}_{}_{}_sr.cfg".format(file_name, g_n, b)

        f = open(m_n, "w")
        f.write(self._model_string)
        f.close()

        f = open(c_n, "w")
        f.write(self._config_string)
        f.close()
        print("write hybrid automaton to {} and {}".format(m_n, c_n))

    def _reset(self):
        self._model_string = ""
        self._config_string = ""

    @classmethod
    def _preprocessing_sat_reach(cls, ha: HybridAutomaton):
        cls._add_single_init_final(ha)
        cls._add_t_var(ha)
        cls._apply_non_strictize(ha)
        cls._rename_y(ha)

    @classmethod
    def _add_single_init_final(cls, ha: HybridAutomaton):
        zero, one, delta = RealVal("0.0"), RealVal("1.0"), RealVal("0.001")
        g_clk = Real("gClk")

        # get initial and final modes
        init, final = set(), set()
        for mode in ha.get_modes():
            if mode.is_initial():
                init.add(mode)

            if mode.is_final():
                final.add(mode)

        # make new initial and final mode
        init_m = Mode(100001)
        init_m.set_as_initial()
        init_m.add_invariant(g_clk <= delta)

        final_m = Mode(100002)
        final_m.set_as_final()

        v_s = get_ha_vars(ha)
        for v in v_s:
            if v.id == g_clk.id:
                init_m.add_dynamic((v, one))
            else:
                init_m.add_dynamic((v, zero))

        for v in v_s:
            final_m.add_dynamic((v, zero))

        ha.add_mode(init_m)
        ha.add_mode(final_m)

        for m in init:
            m.set_as_non_initial()
            tr = Transition(init_m, m)
            tr.add_guard(g_clk >= zero)
            ha.add_transition(tr)

        for m in final:
            m.set_as_non_final()
            tr = Transition(m, final_m)
            ha.add_transition(tr)

    @classmethod
    def _apply_non_strictize(cls, ha: HybridAutomaton):
        # SAT Reach requires all conditions to be non-strict.
        for m in ha.get_modes():
            n_inv = [_make_non_strict(inv) for inv in m.invariant]
            
            # update invariant
            m.invariant.clear()
            m.add_invariant(*n_inv)

        for jp in get_jumps(ha):
            n_g = [_make_non_strict(g) for g in jp.guard]
            
            # update guard
            jp.guard.clear()
            jp.add_guard(*n_g)

    @classmethod
    def _rename_y(cls, ha: HybridAutomaton):
        # SAT Reach raises error for using non-local variable named y.
        subst = VarSubstitution()
        subst.add(Real("y"), Real("renamed_y"))

        for m in ha.get_modes():
            n_inv = [subst.substitute(inv) for inv in m.invariant]
            
            # update invariant
            m.invariant.clear()
            m.add_invariant(*n_inv)

            # update flow
            dyn_d: Dict[Variable, Expr] = dict()
            for v in m.dynamics:
                dyn_d[subst.substitute(v)] = subst.substitute(m.dynamics[v])

            m.dynamics.clear()
            m.dynamics.update(dyn_d) 

        for jp in get_jumps(ha):
            n_g = [subst.substitute(g) for g in jp.guard]
            n_r = [(subst.substitute(v), subst.substitute(e)) for v, e in jp.reset]

            # update guard
            jp.guard.clear()
            jp.add_guard(*n_g)

            # update reset
            jp.reset.clear()
            jp.add_reset(*n_r)

        n_init = [subst.substitute(init) for init in ha.init]
        ha.init.clear()
        ha.init.update(n_init)

    @classmethod
    def _add_t_var(cls, ha: HybridAutomaton):
        # SAT Reach requires a variable named t for CEGAR.
        t, one, zero = Real("t"), RealVal("1.0"), RealVal("0.0")

        # add initial
        ha.add_init(t == zero)
        
        # add dynamics
        for m in ha.get_modes():
            m.add_dynamic((t, one))

        for jp in get_jumps(ha):
            jp.add_reset((t, t))


@singledispatch
def _make_non_strict(const: Formula):
    return const


@_make_non_strict.register(Gt)
def _(const: Gt):
    return Geq(const.left, const.right)


@_make_non_strict.register(Lt)
def _(const: Lt):
    return Leq(const.left, const.right)


@_make_non_strict.register(And)
def _(const: And):
    return And([_make_non_strict(c) for c in const.children])