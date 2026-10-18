"""Numeric discrete modes must never acquire continuous endpoint aliases."""
from types import SimpleNamespace
import unittest
import z3

from stlmc.constraints.analysis import get_vars
from stlmc.constraints.constraints import (
    And, Bool, BoolVal, Eq, Geq, Int, IntVal, Integral, Ode, Real, RealVal,
)
from stlmc.encoding.model_linking import contradiction_gen, path2const
from stlmc.encoding.symbolic_discrete import chi
from stlmc.encoding.symbolic_ids import rename
from stlmc.solver.z3 import z3Obj


class NumericModeMatchingTest(unittest.TestCase):
    def model(self):
        start, end = Real('x_0_0'), Real('x_0_t')
        integral = Integral(0, [end], [start],
                            Ode([Real('x_0_0_t')], [RealVal('0')]))
        return SimpleNamespace(mode_var_dict={'b2': Real('b2'), 'location': Int('location')},
                               modules=[{}], boolean_abstract={Bool('newIntegral_0_0'): integral})

    def check(self, formula, *fixed):
        solver = z3.Solver()
        solver.add(z3Obj(formula), *fixed)
        return solver.check()

    def test_rename_uses_declared_type_and_mode_indices(self):
        model = self.model()
        formula = And([Geq(Real('b2'), RealVal('2')),
                       Geq(Int('location'), IntVal('2')),
                       Geq(Real('x'), RealVal('0'))])
        for vertex, continuous in ((True, 'x_3_0'), (False, 'x_2_t')):
            with self.subTest(vertex=vertex):
                actual, mapping = rename(formula, 3, vertex, model.mode_var_dict)
                self.assertEqual(mapping[Real('b2')], Real('b2_3'))
                self.assertEqual(mapping[Int('location')], Int('location_3'))
                self.assertEqual(mapping[Real('x')], Real(continuous))
                self.assertNotIn(Real('b2_3_0'), get_vars(actual))

    def test_full_matching_connects_both_polarities_to_real_mode(self):
        model = self.model()
        atom = Geq(Real('b2'), RealVal('2'))
        for depth in (1, 2):
            tracked = chi(depth, depth, atom)
            matching = path2const({(depth, tracked): atom}, model)
            self.assertNotIn(Real('b2_0_0'), get_vars(matching))
            for mode, truth in ((1, True), (1, False), (3, True), (3, False)):
                with self.subTest(depth=depth, mode=mode, truth=truth):
                    result = self.check(matching, z3.Real('b2_0') == mode,
                                        z3.Bool(tracked.id) == truth,
                                        z3.Real('tau_0') == 0, z3.Real('tau_1') == 1)
                    self.assertEqual(result, z3.sat if (mode >= 2) == truth else z3.unsat)

    def test_empty_interval_remains_vacuous_but_point_is_not(self):
        atom = Geq(Real('b2'), RealVal('2'))
        for depth in (1, 2):
            tracked = chi(depth, depth, atom)
            matching = path2const({(depth, tracked): atom}, self.model())
            self.assertEqual(self.check(matching, z3.Real('b2_0') == 1,
                                        z3.Bool(tracked.id), z3.Real('tau_0') == 0,
                                        z3.Real('tau_1') == 0),
                             z3.sat if depth == 2 else z3.unsat)

    def test_mixed_mode_state_atom_has_no_phantom_mode_endpoint(self):
        atom = Geq(Real('x') + Real('b2'), RealVal('2'))
        tracked = chi(2, 2, atom)
        matching = path2const({(2, tracked): atom}, self.model())
        self.assertNotIn(Real('b2_0_0'), get_vars(matching))
        self.assertEqual(self.check(matching, z3.Real('b2_0') == 1,
                                    z3.Real('x_0_0') == 0, z3.Real('x_0_t') == 0,
                                    z3.Real('currentMode_0') == 0,
                                    z3.Real('tau_0') == 0, z3.Real('tau_1') == 1,
                                    z3.Bool(tracked.id)), z3.unsat)

    def test_refinement_interval_closure_keeps_prejump_mode(self):
        atom = Geq(Real('b2'), RealVal('2'))
        tracked = chi(2, 2, atom)
        vertex, edge = contradiction_gen({tracked}, {atom}, self.model())
        self.assertNotIn(Real('b2_0_0'), get_vars(vertex))
        # Mode is 1 throughout segment 0 and changes to 3 at its endpoint.
        # Its open-interval predicate is false: the closure must not bind
        # the previous segment's mode to the next segment's mode.
        self.assertEqual(self.check(And([vertex, edge]),
                                    z3.Real('b2_0') == 1, z3.Real('b2_1') == 3,
                                    z3.Real('tau_0') == 0, z3.Real('tau_1') == 1,
                                    z3.Not(z3.Bool(tracked.id))), z3.sat)


if __name__ == '__main__':
    unittest.main()
