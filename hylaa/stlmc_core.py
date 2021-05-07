from functools import singledispatch

from stlmcPy.constraints.constraints import Variable, Constraint, Real, And, Eq
from stlmcPy.constraints.operations import infix, substitution, get_vars, reduce_not
from stlmcPy.exception.exception import NotSupportedError, NotFoundElementError
from stlmcPy.hybrid_automaton.hybrid_automaton import HybridAutomaton as StlMCHybridAutomaton
from hylaa import lputil, symbolic
from hylaa.core import Core
from hylaa.hybrid_automaton import HybridAutomaton
from hylaa.settings import HylaaSettings
from hylaa.stateset import StateSet
from stlmcPy.hybrid_automaton.converter import AbstractConverter
from stlmcPy.solver.strategy import unit_split


class HylaaConverter(AbstractConverter):
    def __init__(self, l_v):
        self.var_set = set()
        # self.ha = HybridAutomaton('ha')
        # self.sigma = sigma
        self.l_v = l_v
        # self.max_bound = max_bound
        # self.s_integrals = s_integrals
        # self.s_foralls = s_foralls

    def _find_index(self, input_list: list, v: Variable):
        index = 0
        for e in input_list:
            if e == remove_index(v).id:
                return index
            index += 1
        raise NotFoundElementError(v, "index not found")

    #
    # def make_transition(self, s_psi_abs_i, i, mode_p, mode_n):
    #     trans_i = self.ha.new_transition(mode_p, mode_n)
    #     s_forall_i, s_integral_i, s_0, s_tau_i, s_reset_i, s_guard_i = unit_split(s_psi_abs_i, i)
    #
    #     # printer = Printer()
    #     guard_i_children = list(s_guard_i)
    #     tau_i_children = list(s_tau_i)
    #     total_children = list()
    #
    #     total_children.extend(guard_i_children)
    #     total_children.extend(tau_i_children)
    #
    #     phi_reset_children = list()
    #     for c in total_children:
    #         vs = get_vars(c)
    #         new_dict = dict()
    #         for v in vs:
    #             new_dict[v] = remove_index(v)
    #         phi_reset_children.append(reduce_not(substitution(c, new_dict)))
    #
    #     # printer.print_debug("\n\ntransition : {}".format(trans_i))
    #     # printer.print_debug("* variables : {}".format(l_v))
    #     # printer.print_debug("* guard condition : ")
    #     # for g_cond in infix(And(phi_reset_children)).split('&'):
    #     #     printer.print_debug("  * {}".format(g_cond))
    #
    #     m_guard, m_guard_rhs = symbolic.make_condition(self.l_v, infix(And(phi_reset_children)).split('&'), {},
    #                                                    has_affine_variable=True)
    #     trans_i.set_guard(m_guard, m_guard_rhs)
    #
    #     remove_var_dict = dict()
    #     for c in s_reset_i:
    #         vs = get_vars(c)
    #         for v in vs:
    #             remove_var_dict[v] = remove_index(v)
    #
    #     l_r = self.l_v.copy()
    #     for r in s_reset_i:
    #         k = self._find_index(self.l_v, r.left)
    #         l_r[k] = infix(substitution(r.right, remove_var_dict))
    #
    #     if "tau" in self.l_v:
    #         for j in range(1, self.max_bound + 1):
    #             k_t_j = self._find_index(self.l_v, Real("tau_" + str(j)))
    #             l_r[k_t_j] = "tau_" + str(j)
    #
    #     # printer.print_debug("* reset condition : {}".format(l_r))
    #
    #     reset_mat = symbolic.make_reset_mat(self.l_v, l_r, {}, has_affine_variable=True)
    #     trans_i.set_reset(reset_mat)

    def convert(self, ha: StlMCHybridAutomaton):
        hylaa_ha = HybridAutomaton(ha.name)
        new_mode_dict = dict()
        for m in ha.modes:
            new_mode = hylaa_ha.new_mode(m)
            new_mode_dict[ha.modes[m]] = new_mode
            l_integral = self.l_v.copy()

            if ha.modes[m].dynamics is not None:
                for j, v in enumerate(ha.modes[m].dynamics.vars):
                    e = ha.modes[m].dynamics.exps[j]
                    try:
                        k = self._find_index(self.l_v, v)
                        vs = get_vars(e)
                        new_dict = dict()
                        for v_elem in vs:
                            new_dict[v_elem] = remove_index(v_elem)
                        l_integral[k] = infix(substitution(e, new_dict))
                    except NotFoundElementError as ne:
                        print(ne)
                        raise NotSupportedError("element should be found!")

            m_integral = symbolic.make_dynamics_mat(self.l_v, l_integral, {}, has_affine_variable=True)
            # printer.print_debug("\n\n* variables : {} \n* integrals : {}".format(l_v, l_integral))
            new_mode.set_dynamics(m_integral)

            if ha.modes[m].invariant is not None:
                inv = ha.modes[m].invariant
                if isinstance(inv, And) and len(inv.children) > 0:
                    m_forall, m_forall_rhs = symbolic.make_condition(self.l_v, infix(inv).split('&'), {},
                                                                     has_affine_variable=True)
                    new_mode.set_invariant(m_forall, m_forall_rhs)
                else:
                    m_forall, m_forall_rhs = symbolic.make_condition(self.l_v, infix(inv), {},
                                                                     has_affine_variable=True)
                    new_mode.set_invariant(m_forall, m_forall_rhs)

        # transition
        for i, t in enumerate(ha.trans):
            print("{} , {} -> {}".format(t, new_mode_dict[ha.trans[t].src].name, new_mode_dict[ha.trans[t].trg].name))

            new_trans = hylaa_ha.new_transition(new_mode_dict[ha.trans[t].src], new_mode_dict[ha.trans[t].trg])
            if ha.trans[t].guard is not None:
                m_guard, m_guard_rhs = symbolic.make_condition(self.l_v, infix(ha.trans[t].guard).split('&'), {},
                                                               has_affine_variable=True)
                new_trans.set_guard(m_guard, m_guard_rhs)

            if ha.trans[t].reset is not None:
                reset = ha.trans[t].reset
                l_r = self.l_v.copy()
                if isinstance(reset, And) and len(reset.children) > 0:
                    for r in reset.children:
                        if isinstance(r, Eq) and isinstance(r.left, Variable):
                            try:
                                k = self._find_index(self.l_v, r.left)
                                l_r[k] = infix(r.right)
                            except NotFoundElementError as ne:
                                print(ne)
                                raise NotSupportedError("element should be found!")

                reset_mat = symbolic.make_reset_mat(self.l_v, l_r, {}, has_affine_variable=True)
                new_trans.set_reset(reset_mat)
        return hylaa_ha


class HylaaRawSolver:
    def __init__(self):
        self.result = None

    def run(self, ha: HybridAutomaton, new_bound_box_list):
        mode = ha.modes['mode0']
        init_lpi = lputil.from_box(new_bound_box_list, mode)
        init_list = [StateSet(init_lpi, mode)]
        settings = HylaaSettings(0.1, 100)
        # settings.stop_on_aggregated_error = False
        settings.aggstrat.deaggregate = True  # use deaggregationboolean_abstract_dict
        # settings.stdout = HylaaSettings.STDOUT_VERBOSE
        core = Core(ha, settings)
        ce = core.run(init_list)

        self.result = core.is_counterexample


@singledispatch
def remove_index(c: Constraint) -> Variable:
    raise NotSupportedError("input should be variable type : " + str(c))


@remove_index.register(Variable)
def _(v: Variable) -> Variable:
    if "tau" not in v.id and "_" in v.id:
        start_index = v.id.find("_")
        var_id = v.id[:start_index]
        return Real(var_id)
    return v