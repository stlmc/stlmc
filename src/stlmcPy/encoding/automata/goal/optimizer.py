import time
import z3
from typing import Dict, Set, Tuple

from .aux import translate
from .label import Label
from ....constraints.aux.operations import VarSubstitution
from ....constraints.constraints import *
from ....solver.z3 import translate as z3translate

Labels = Set[Label]


class PropositionOptimizer:
    def __init__(self, tau_subst: VarSubstitution):
        self._contradiction_cache: Dict[Label, bool] = dict()
        self._reduction_cache: Dict[Labels, Tuple[Set[Label], Set[Label]]] = dict()
        self._reduction_label_cache: Dict[Label, bool] = dict()
        self._translate_cache: Dict[Formula, Formula] = dict()

        self._tau_subst = tau_subst
        self._z3_solver = z3.SolverFor("QF_LRA")

        self.contradiction_call = 0
        self.reduction_call = 0
        self.reduction_time = 0.0
        self.translate_time = 0.0
        self.z3obj_time = 0.0
        self.contradiction_time = 0.0

    def check_contradiction(self, label: Label, depth: int, *assumptions):
        if label in self._contradiction_cache:
            return self._contradiction_cache[label]
        else:
            self._contradiction_cache[label] = True if self._check_contradiction(label, depth, *assumptions) else False
            return self._contradiction_cache[label]

    def reduce_label(self, labels: Labels) -> Tuple[Set[Label], Set[Label]]:
        if labels not in self._reduction_cache:
            print(labels)
            raise Exception("calculate label reduction first")
        return self._reduction_cache[labels]

    def calc_label_reduction(self, *labels, **optional):
        assumptions = list()
        if "assumptions" in optional:
            assumptions = list(map(lambda x: self._tau_subst.substitute(x), optional["assumptions"]))

        for label in labels:
            self._calc_label_reduction(label, *assumptions)

    def _calc_label_reduction(self, labels: Labels, *assumptions):
        if labels not in self._reduction_cache:
            self._reduction_cache[labels] = self._calc_prop_reduction(labels, *assumptions)

    def _check_contradiction(self, label: Label, depth: int, *assumptions) -> bool:
        self.contradiction_call += 1
        f_set = self._label2_formula(label, depth)
        f, a = self._formula2_z3obj(*f_set), self._formula2_z3obj(*assumptions)
        r, t = self._z3_check_sat(f, a)
        self.contradiction_time += t
        if r == z3.z3.unsat:
            return True
        return False

    def _calc_prop_reduction(self, labels: Set[Label], *assumptions) -> Tuple[Set[Label], Set[Label]]:
        self.reduction_call += 1
        self._labels2_formula(labels)
        non_intermediate, intermediate = set(), set()

        for label in labels:
            # use cache
            if label in self._reduction_label_cache:
                # check if it is non-trivial
                if not self._reduction_label_cache[label]:
                    non_intermediate.add(label)
            else:
                # if in translate cache = non_intermediate
                if label in self._translate_cache:
                    p_f = self._translate_cache[label]

                    f, a = self._formula2_z3obj(Not(p_f)), self._formula2_z3obj(*assumptions)
                    r, t = self._z3_check_sat(f, a)
                    self.reduction_time += t

                    if r == z3.z3.unsat:
                        self._reduction_label_cache[label] = True
                    else:
                        self._reduction_label_cache[label] = False
                        non_intermediate.add(label)
                else:
                    intermediate.add(label)

        return non_intermediate, intermediate

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
            if f in self._translate_cache:
                f_set.add(self._translate_cache[f])
            else:
                r = self._tau_subst.substitute(f)
                self._translate_cache[f] = r
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
        self.reduction_call = 0
        self.translate_time = 0.0
        self.reduction_time = 0.0
        self.contradiction_time = 0.0
        self.z3obj_time = 0.0
