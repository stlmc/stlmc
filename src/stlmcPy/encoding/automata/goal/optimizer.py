import time

import z3
from typing import Dict, Set, Tuple

from .label import Label
from ....constraints.aux.operations import VarSubstitution
from ....constraints.constraints import *
from ....solver.z3 import translate as z3translate


class ContradictionChecker:
    def __init__(self):
        self._z3_solver = z3.SolverFor("QF_LRA")

        self.contradiction_call = 0
        self.translate_time = 0.0
        self.z3obj_time = 0.0
        self.contradiction_time = 0.0

    def is_contradiction(self, *f_set) -> bool:
        self.contradiction_call += 1
        f = self._formula2_z3obj(*f_set)
        r, t = self._z3_check_sat(f)
        self.contradiction_time += t

        # return true if contradiction
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