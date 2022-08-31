import time
import z3
from typing import Dict, Set, Tuple

from .aux import is_post_time
from ....constraints.aux.operations import VarSubstitution
from ....constraints.constraints import *
from ....encoding.automata.goal.aux import Label, split_label, translate
from ....solver.z3 import translate as z3translate


class PropositionOptimizer:
    def __init__(self, tau_subst: VarSubstitution,
                 hash_dict1: Dict[hash, Formula], hash_dict2: Dict[hash, Interval]):
        self._contradiction_cache: Dict[Label, bool] = dict()
        self._reduction_cache: Dict[Label, Tuple[Set[Bool], Set[Bool]]] = dict()
        self._reduction_prop_cache: Dict[Bool, bool] = dict()
        self._translate_cache: Dict[Bool, Formula] = dict()

        self._tau_subst = tau_subst
        self._hash_dict1: Dict[hash, Formula] = hash_dict1
        self._hash_dict2: Dict[hash, Interval] = hash_dict2

        self._z3_solver = z3.SolverFor("QF_LRA")

        self.contradiction_call = 0
        self.reduction_call = 0
        self.reduction_time = 0.0
        self.translate_time = 0.0
        self.z3obj_time = 0.0
        self.contradiction_time = 0.0

    def check_contradiction(self, label: Label, *assumptions):
        if label in self._contradiction_cache:
            return self._contradiction_cache[label]
        else:
            self._contradiction_cache[label] = True if self._check_contradiction(label, *assumptions) else False
            return self._contradiction_cache[label]

    def reduce_label(self, label) -> Tuple[Set[Bool], Set[Bool]]:
        if label not in self._reduction_cache:
            raise Exception("calculate label reduction first")
        return self._reduction_cache[label]

    def calc_label_reduction(self, *labels, **optional):
        assumptions = list()
        if "assumptions" in optional:
            assumptions = optional["assumptions"]

        for label in labels:
            self._calc_label_reduction(label, *assumptions)

    def _calc_label_reduction(self, label: Label, *assumptions):
        if label not in self._reduction_cache:
            self._reduction_cache[label] = self._calc_prop_reduction(label, *assumptions)

    def _check_contradiction(self, label: Label, *assumptions) -> bool:
        self.contradiction_call += 1
        f_set = self._label2_formula(label)
        f, a = self._formula2_z3obj(*f_set), self._formula2_z3obj(*assumptions)
        r, t = self._z3_check_sat(f, a)
        self.contradiction_time += t
        if r == z3.z3.unsat:
            return True
        return False

    def _calc_prop_reduction(self, label: Label, *assumptions) -> Tuple[Set[Bool], Set[Bool]]:
        self.reduction_call += 1
        self._label2_formula(label)
        ap, non_ap = set(), set()

        for p in label:
            # use cache
            if p in self._reduction_prop_cache:
                # check if it is non-trivial
                if not self._reduction_prop_cache[p]:
                    ap.add(p)
            else:
                # if in translate cache = prop
                if p in self._translate_cache:
                    p_f = self._translate_cache[p]

                    f, a = self._formula2_z3obj(Not(p_f)), self._formula2_z3obj(*assumptions)
                    r, t = self._z3_check_sat(f, a)
                    self.reduction_time += t

                    if r == z3.z3.unsat:
                        self._reduction_prop_cache[p] = True
                    else:
                        self._reduction_prop_cache[p] = False
                        ap.add(p)
                else:
                    non_ap.add(p)

        return ap, non_ap

    def _z3_check_sat(self, f, *assumptions):
        s = time.time()
        self._z3_solver.push()
        for a in assumptions:
            self._z3_solver.add(a)
        r = self._z3_solver.check(f)
        self._z3_solver.pop()
        e = time.time()
        return r, e - s

    def _label2_formula(self, label: Label) -> Set[Formula]:
        s = time.time()
        f_set: Set[Formula] = set()
        ap, _ = split_label(label, self._hash_dict1)
        for v in ap:
            if v in self._translate_cache:
                f_set.add(self._translate_cache[v])
            else:
                tr = translate({v}, self._tau_subst, self._hash_dict1, self._hash_dict2)

                if len(tr) < 1:
                    raise Exception("fail to translate proposition")

                f = tr.pop()
                self._translate_cache[v] = f
                f_set.add(f)
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
