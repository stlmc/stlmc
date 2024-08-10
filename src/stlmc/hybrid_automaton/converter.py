import abc
from typing import *

from ..objects.configuration import Configuration
from sympy import simplify, StrictGreaterThan, GreaterThan, LessThan, StrictLessThan, Float

from ..constraints.constraints import *
from ..constraints.operations import substitution, reduce_not
from ..hybrid_automaton.hybrid_automaton import HybridAutomaton
from ..hybrid_automaton.utils import vars_in_ha
from ..solver.ode_utils import remove_index, expr_to_sympy, get_vars_from_set, find_index
from ..solver.strategy import unit_split
from ..util.print import Printer


class HaGenerator:
    def __init__(self):
        self.s_f_list = None
        self.max_bound = None
        self.sigma = None
        # s_f_list, max_bound, sigma, conf_dict

    def _reset(self):
        self.s_f_list = None
        self.max_bound = None
        self.sigma = None

    def _check_pre_cond(self):
        assert self.s_f_list is not None
        assert self.max_bound is not None
        assert self.sigma is not None

    def set(self, s_f_list: list, max_bound, sigma: dict):
        self.s_f_list = s_f_list
        self.max_bound = max_bound
        self.sigma = sigma

    def generate(self):
        def _instantiate(_old_s_f_list, _sigma):
            _new_s_f_list = list()
            for s in _old_s_f_list:
                _new_s = set()
                for c in s:
                    _new_s.add(substitution(c, _sigma))
                _new_s_f_list.append(_new_s)
            return _new_s_f_list

        def _make_variable_ordering(_s_f_list):
            _variable_ordering = list()
            _var_set = get_vars_from_set(_s_f_list)
            for _var in _var_set:
                _var_without_index = remove_index(_var)
                if _var_without_index.id not in _variable_ordering:
                    _variable_ordering.append(_var_without_index.id)
            # get its canonical form
            return sorted(_variable_ordering)

        def _make_bound_box(_var_ordering: list, _init_consts: set):
            _sympy_bound_box = list()
            for _ in _var_ordering:
                _sympy_bound_box.append([None, None])

            for t in _var_ordering:
                if ("tau" in t) or ("timeStep" in t):
                    index = find_index(_var_ordering, Real(t))
                    _sympy_bound_box[index][0] = Float(0.0)
                    _sympy_bound_box[index][1] = Float(0.0)

            _sympy_init_constraints = list()

            for c in _init_consts:
                _sympy_init_constraints.append(simplify(expr_to_sympy(reduce_not(c))))

            for expr in _sympy_init_constraints:
                if isinstance(expr, GreaterThan) or isinstance(expr, StrictGreaterThan):
                    # left is variable
                    if expr.lhs.is_symbol:
                        var_id = str(expr.lhs)
                        index = find_index(_var_ordering, Real(var_id))
                        if _sympy_bound_box[index][0] is None:
                            _sympy_bound_box[index][0] = expr.rhs
                        else:
                            if str(simplify(_sympy_bound_box[index][0] <= expr.rhs)) == "True":
                                _sympy_bound_box[index][0] = expr.rhs
                    elif expr.rhs.is_symbol:
                        var_id = str(expr.rhs)
                        index = find_index(_var_ordering, Real(var_id))
                        if _sympy_bound_box[index][1] is None:
                            _sympy_bound_box[index][1] = expr.lhs
                        else:
                            if str(simplify(_sympy_bound_box[index][1] <= expr.lhs)) == "True":
                                _sympy_bound_box[index][1] = expr.lhs

                elif isinstance(expr, LessThan) or isinstance(expr, StrictLessThan):
                    # left is variable
                    if expr.lhs.is_symbol:
                        var_id = str(expr.lhs)
                        index = find_index(_var_ordering, Real(var_id))
                        if _sympy_bound_box[index][1] is None:
                            _sympy_bound_box[index][1] = expr.rhs
                        else:
                            if str(simplify(_sympy_bound_box[index][1] >= expr.rhs)) == "True":
                                _sympy_bound_box[index][1] = expr.rhs
                    elif expr.rhs.is_symbol:
                        var_id = str(expr.rhs)
                        index = find_index(_var_ordering, Real(var_id))
                        if _sympy_bound_box[index][0] is None:
                            _sympy_bound_box[index][0] = expr.lhs
                        else:
                            if str(simplify(_sympy_bound_box[index][0] >= expr.lhs)) == "True":
                                _sympy_bound_box[index][0] = expr.lhs

            _bound_box_list = list()
            for e in _sympy_bound_box:
                printer.print_debug("bound box list test : {}".format(e))
                bound_box_left = -float("inf")
                bound_box_right = float("inf")
                if e[0] is not None:
                    bound_box_left = float(e[0])
                if e[1] is not None:
                    bound_box_right = float(e[1])
                _bound_box_list.append([bound_box_left, bound_box_right])

            return _bound_box_list

        self._check_pre_cond()
        printer = Printer()
        new_s_f_list = _instantiate(self.s_f_list, self.sigma)
        variable_ordering = _make_variable_ordering(new_s_f_list)

        s_forall = list()
        s_integral = list()
        s_0 = list()
        s_tau = list()
        s_reset = list()
        s_guard = list()

        for i in range(self.max_bound + 1):
            s_forall_i, s_integral_i, s_0_i, s_tau_i, s_reset_i, s_guard_i = unit_split(self.s_f_list[i], i)
            s_forall.append(s_forall_i)
            s_integral.append(s_integral_i)
            s_0.append(s_0_i)
            s_tau.append(s_tau_i)
            s_reset.append(s_reset_i)
            s_guard.append(s_guard_i)

        ha = HybridAutomaton('ha')
        l_mode = list()

        for i in range(self.max_bound + 1):
            l_mode.append(
                HaGenerator.make_mode(
                    s_integral[i], s_forall[i], i, self.max_bound, ha, self.sigma
                )
            )

        l_mode.append(ha.new_mode("error"))

        for i in range(self.max_bound + 1):
            HaGenerator.make_transition(self.s_f_list[i], i, ha, l_mode[i], l_mode[i + 1])

        HaGenerator.refine_ha(ha)
        _, _, init_set, _, _, _ = unit_split(self.s_f_list[0], self.max_bound)
        bound_box = _make_bound_box(variable_ordering, init_set)
        self._reset()
        return ha, bound_box, variable_ordering

    @staticmethod
    def make_mode(s_integral_i, s_forall_i, i, max_bound, ha: HybridAutomaton, sigma):
        mode_i = ha.new_mode("mode" + str(i))
        for integral in s_integral_i:
            if integral in sigma:
                dyns = sigma[integral].dynamics

                # add tau dynamics
                for j in range(1, i + 1):
                    dyns.vars.append(Real("tau_" + str(j)))
                    dyns.exps.append(RealVal("0"))

                for j in range(i + 1, max_bound + 2):
                    dyns.vars.append(Real("tau_" + str(j)))
                    dyns.exps.append(RealVal("1"))

                assert len(dyns.vars) == len(dyns.exps)
                for k, v in enumerate(dyns.vars):
                    mode_i.set_dynamic(v, dyns.exps[k])

        for c in s_forall_i:
            assert isinstance(c, Bool)
            forall_const = substitution(c, sigma)

            assert isinstance(forall_const, Forall)
            reduced_inv = reduce_not(forall_const.const)

            mode_i.set_invariant(reduced_inv)

        return mode_i

    @staticmethod
    def make_transition(s_psi_abs_i, i, ha: HybridAutomaton, mode_p, mode_n):
        trans_i = ha.new_transition("trans{}".format(i), mode_p, mode_n)
        s_forall_i, s_integral_i, s_0, s_tau_i, s_reset_i, s_guard_i = unit_split(s_psi_abs_i, i)

        guard_tau_consts = s_guard_i.union(s_tau_i)

        for const in guard_tau_consts:
            trans_i.set_guard(const)

        for const in s_reset_i:
            trans_i.set_reset(const)

    @staticmethod
    def refine_ha(ha: HybridAutomaton):
        def _make_subst_dict_and_var_set(_var_set: set):
            _var_set_without_index = set()
            _subst_dict = dict()
            for _var in _var_set:
                _var_without_index = remove_index(_var)
                _var_set_without_index.add(_var_without_index)
                _subst_dict[_var] = _var_without_index
            return _subst_dict, _var_set_without_index

        indexed_var_set = vars_in_ha(ha)
        subst_dict, _ = _make_subst_dict_and_var_set(indexed_var_set)

        for mode in ha.modes:
            for (var, exp) in mode.dynamics:
                mode.remove_dynamic(var, exp)
                new_var = substitution(var, subst_dict)
                new_exp = substitution(exp, subst_dict)

                mode.set_dynamic(new_var, new_exp)

            for inv in mode.invariant:
                mode.remove_invariant(inv)
                mode.set_invariant(substitution(inv, subst_dict))

        for transition in ha.transitions:
            guard_to_be_removed = set()
            guard_to_be_updated = set()
            for guard in transition.guard:
                guard_to_be_removed.add(guard)
                guard_to_be_updated.add(substitution(guard, subst_dict))
            transition.remove_guards(guard_to_be_removed)
            for guard in guard_to_be_updated:
                transition.set_guard(guard)

            reset_to_be_removed = set()
            reset_to_be_updated = set()
            for reset in transition.reset:
                reset_to_be_removed.add(reset)
                reset_to_be_updated.add(substitution(reset, subst_dict))
            transition.remove_resets(reset_to_be_removed)

            for reset in reset_to_be_updated:
                transition.set_reset(reset)


class AbstractConverter:
    def __init__(self):
        self.convert_result = None

    @abc.abstractmethod
    def convert(self, ha: HybridAutomaton, setting: Dict, variable_ordering: List, bound_box: List):
        pass

    @abc.abstractmethod
    def solve(self, config: Configuration):
        pass

    @abc.abstractmethod
    def preprocessing(self, ha: HybridAutomaton):
        pass
