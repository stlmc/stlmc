import time
from functools import singledispatch

import z3
from typing import Dict, Set, Tuple

from .label import Label
from ....constraints.aux.operations import VarSubstitution
from ....constraints.constraints import *
from ....solver.z3 import translate as z3translate

Labels = Set[Label]


class ContradictionChecker:
    def __init__(self, clk_subst_dict: Dict[int, VarSubstitution], tau_subst: VarSubstitution):
        self._contradiction_cache: Dict[Label, bool] = dict()
        self._reduction_cache: Dict[Labels, Tuple[Set[Label], Set[Label]]] = dict()
        self._reduction_label_cache: Dict[Label, bool] = dict()

        self._clk_subst_dict = clk_subst_dict
        self._tau_subst = tau_subst
        self._z3_solver = z3.SolverFor("QF_LRA")

        self.contradiction_call = 0
        self.translate_time = 0.0
        self.z3obj_time = 0.0
        self.contradiction_time = 0.0

    def check_contradiction(self, label: Label, depth: int, *assumptions):
        if label in self._contradiction_cache:
            return self._contradiction_cache[label]
        else:
            self._contradiction_cache[label] = self._check_contradiction(label, depth, *assumptions)
            return self._contradiction_cache[label]

    def _check_contradiction(self, label: Label, depth: int, *assumptions) -> bool:
        self.contradiction_call += 1
        f_set = self._label2_formula(label, depth)
        f, a = self._formula2_z3obj(*f_set), self._formula2_z3obj(*assumptions)
        r, t = self._z3_check_sat(f, a)
        self.contradiction_time += t
        if r == z3.z3.unsat:
            return True
        return False

    def _z3_check_sat(self, f, *assumptions):
        s = time.time()
        self._z3_solver.push()
        for a in assumptions:
            self._z3_solver.add(a)
        r = self._z3_solver.check(f)
        self._z3_solver.pop()
        e = time.time()
        return r, e - s

    def _label2_formula(self, label: Label, depth: int) -> Set[Formula]:
        s = time.time()
        f_set, (tr_f_set, _) = set(), translate(label, depth)
        for f in tr_f_set:
            r = self._tau_subst.substitute(f)
            r = self._clk_subst_dict[depth].substitute(r)
            f_set.add(r)
        e = time.time()
        self.translate_time += e - s
        return f_set

    def _formula2_z3obj(self, *formula):
        if len(formula) < 1:
            return z3translate(BoolVal("True"))

        s = time.time()
        f = z3translate(And([f for f in formula]))
        e = time.time()
        self.z3obj_time += e - s
        return f

    def time_clear(self):
        self.contradiction_call = 0
        self.translate_time = 0.0
        self.contradiction_time = 0.0
        self.z3obj_time = 0.0


def reduce(*formula) -> Tuple[Union[Formula, None], bool]:
    all_f: Set[Formula] = set()
    for f in formula:
        all_f.update(_flat_formula(f))

    reduced: Set[Formula] = set()
    for f in all_f:
        if not _reducible(f):
            reduced.add(f)

    if len(reduced) <= 0:
        return None, False
    elif len(reduced) == 1:
        return reduced.pop(), True
    else:
        return And(list(reduced)), True


def _reducible(formula):
    f = z3translate(formula)
    return z3.is_true(z3.simplify(f))


@singledispatch
def _flat_formula(formula: Formula) -> Set[Formula]:
    return {formula}


@_flat_formula.register(And)
def _(formula: And) -> Set[Formula]:
    return set(formula.children)
