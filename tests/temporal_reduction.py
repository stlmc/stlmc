import sys
import unittest
from pathlib import Path

import z3


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.constraints.constraints import (
    And, Bool, BoolVal, Eq, FinallyFormula, GloballyFormula, Not, Or,
    Real, RealVal,
    ReleaseFormula, UntilFormula,
)
from stlmc.constraints.interval import (
    Interval, inInterval, is_positive_infinity, universeInterval,
)
from stlmc.constraints.operations import remove_binary
import stlmc.encoding.enumerate as enumerate_encoding
import stlmc.encoding.monolithic as monolithic_encoding
from stlmc.encoding.enumerate import (
    calc_sub_formulas, chi, fully_stable_partition_const,
    k_depth_stl_consts, partition_obligations, rho, stl_depth_components,
    symbolic_goal, time_ordering,
)
from stlmc.solver.z3 import z3Obj


class BoundedTemporalReductionTest(unittest.TestCase):
    def setUp(self):
        self.left = Bool("p")
        self.right = Bool("q")

    def _interval(self, left_closed):
        return Interval(
            left_closed, RealVal("1"), False, RealVal("3")
        )

    def test_infinite_endpoint_detection_is_structural(self):
        self.assertTrue(is_positive_infinity(float("inf")))
        self.assertTrue(is_positive_infinity(RealVal("inf")))
        self.assertFalse(is_positive_infinity(RealVal("infinite_limit")))
        self.assertFalse(is_positive_infinity(Real("infinite_limit")))

    def test_interval_variable_named_inf_is_not_an_infinite_endpoint(self):
        constraint = inInterval(
            Real("x"),
            Interval(True, RealVal("0"), True, Real("infinite_limit")),
        )
        self.assertIn("infinite_limit", str(constraint))
        self.assertIsInstance(constraint, And)

    def test_one_step_uses_shared_fully_stable_formula_builder(self):
        self.assertIs(
            monolithic_encoding.fully_stable_stl_formula,
            enumerate_encoding.k_size_stl_formula,
        )
        self.assertIn(
            "fully_stable_stl_formula",
            monolithic_encoding.OneStepAlgorithm.run.__code__.co_names,
        )

    def test_one_and_two_step_share_temporal_component_builders(self):
        two_step_names = enumerate_encoding.TwoStepAlgorithm.run.__code__.co_names
        one_step_names = (
            enumerate_encoding.k_size_stl_formula_from_threshold
            .__code__.co_names
        )
        self.assertIn("prepare_fully_stable_stl_formula", two_step_names)
        self.assertIn(
            "prepare_fully_stable_stl_formula",
            enumerate_encoding.k_size_stl_formula.__code__.co_names,
        )
        self.assertIn("stl_depth_components", two_step_names)
        self.assertIn("stl_depth_components", one_step_names)
        self.assertIn("fully_stable_partition_const", two_step_names)
        self.assertIn("fully_stable_partition_const", one_step_names)

    def test_shared_depth_and_partition_components_match_primitives(self):
        formula = UntilFormula(
            self._interval(True), universeInterval, self.left, self.right,
        )
        sub_formulas = calc_sub_formulas(formula)
        stl_children, time_children, terminal = stl_depth_components(
            sub_formulas, range(1, 5), 4.0
        )
        expected_stl, expected_time, expected_terminal = (
            k_depth_stl_consts(sub_formulas, 4, 4.0)
        )
        self.assertEqual(4, len(stl_children))
        self.assertEqual(4, len(time_children))
        self.assertEqual(str(expected_stl), str(stl_children[-1]))
        self.assertEqual(str(expected_time), str(time_children[-1]))
        self.assertEqual(str(expected_terminal), str(terminal))
        self.assertEqual(
            str(And(partition_obligations(sub_formulas, 4))),
            str(fully_stable_partition_const(sub_formulas, 4)),
        )

    def test_until_prefix_includes_current_time(self):
        reduced = remove_binary(UntilFormula(
            self._interval(False), universeInterval,
            self.left, self.right,
        ))

        self.assertIsInstance(reduced, And)
        prefix, witness, split = reduced.children
        self.assertIsInstance(prefix, GloballyFormula)
        self.assertTrue(prefix.local_time.left_end)
        self.assertTrue(prefix.local_time.right_end)
        self.assertEqual(str(prefix.local_time), "[0.0,1]")
        self.assertIsInstance(witness, FinallyFormula)
        self.assertEqual(witness.local_time, self._interval(False))
        self.assertIsInstance(split.child, UntilFormula)
        self.assertFalse(split.child.local_time.left_end)
        self.assertEqual(str(split.child.local_time), "(0.0,inf)")

    def test_closed_until_allows_split_point_witness(self):
        reduced = remove_binary(UntilFormula(
            self._interval(True), universeInterval,
            self.left, self.right,
        ))

        continuation = reduced.children[2].child
        self.assertIsInstance(continuation, UntilFormula)
        self.assertTrue(continuation.local_time.left_end)
        self.assertEqual(str(continuation.local_time), "[0.0,inf)")

    def test_release_is_boolean_dual_shape(self):
        reduced = remove_binary(ReleaseFormula(
            self._interval(False), universeInterval,
            self.left, self.right,
        ))

        self.assertIsInstance(reduced, Or)
        prefix, witness, split = reduced.children
        self.assertIsInstance(prefix, FinallyFormula)
        self.assertEqual(str(prefix.local_time), "[0.0,1]")
        self.assertIsInstance(witness, GloballyFormula)
        self.assertEqual(witness.local_time, self._interval(False))
        self.assertIsInstance(split, GloballyFormula)
        self.assertIsInstance(split.child, ReleaseFormula)
        self.assertFalse(split.child.local_time.left_end)

    def test_strict_until_preserves_original_start_index(self):
        strict = UntilFormula(
            Interval(False, RealVal("0"), False, RealVal("inf")),
            universeInterval, self.left, self.right,
        )

        singular_rule = symbolic_goal(strict, 1, 1, 10)
        self.assertIn(str(rho(1, 2, strict)), str(singular_rule))
        self.assertNotIn(str(chi(2, 2, strict)), str(singular_rule))

    def test_strict_release_preserves_original_start_index(self):
        strict = ReleaseFormula(
            Interval(False, RealVal("0"), False, RealVal("inf")),
            universeInterval, self.left, self.right,
        )

        singular_rule = symbolic_goal(strict, 1, 1, 10)
        self.assertIn(str(rho(1, 2, strict)), str(singular_rule))
        self.assertNotIn(str(chi(2, 2, strict)), str(singular_rule))

    def _symbolic_truth(self, formula, p_bits, q_bits=None):
        depth = 4
        sub_formulas = calc_sub_formulas(formula)
        children = [time_ordering(depth, 2.0),
                    Eq(Real("tau_1"), RealVal("1.0"))]
        final_const = None
        for current in range(1, depth + 1):
            stl, timing, final_const = k_depth_stl_consts(
                sub_formulas, current, 2.0
            )
            children.extend((stl, timing))
        children.append(final_const)
        for index, value in enumerate(p_bits, 1):
            children.append(Eq(
                chi(index, index, self.left), BoolVal(str(value))
            ))
        if q_bits is not None:
            for index, value in enumerate(q_bits, 1):
                children.append(Eq(
                    chi(index, index, self.right), BoolVal(str(value))
                ))

        root = chi(1, 1, formula)
        results = []
        for requested in (False, True):
            solver = z3.SolverFor("QF_LRA")
            solver.add(z3Obj(And(
                children + ([root] if requested else [Not(root)])
            )))
            results.append(solver.check() == z3.sat)
        self.assertNotEqual(results[0], results[1])
        return results[1]

    def _fully_stable_sat(self, formula, tau_values, p_bits, q_bits,
                          require_formula=True):
        depth = 2 * (len(tau_values) - 1)
        sub_formulas = calc_sub_formulas(formula)
        children = [time_ordering(depth, tau_values[-1])]
        if require_formula:
            children.append(chi(1, 1, formula))
        for index, value in enumerate(tau_values):
            children.append(Eq(
                Real("tau_{}".format(index)), RealVal(str(value))
            ))
        final_const = None
        for current in range(1, depth + 1):
            stl, timing, final_const = k_depth_stl_consts(
                sub_formulas, current, tau_values[-1]
            )
            children.extend((stl, timing))
        children.extend((
            final_const,
            And(partition_obligations(sub_formulas, depth)),
        ))
        for index, value in enumerate(p_bits, 1):
            children.append(Eq(
                chi(index, index, self.left), BoolVal(str(value))
            ))
        for index, value in enumerate(q_bits, 1):
            children.append(Eq(
                chi(index, index, self.right), BoolVal(str(value))
            ))
        solver = z3.SolverFor("QF_LRA")
        solver.add(z3Obj(And(children)))
        return solver.check() == z3.sat

    def test_binary_rewrite_does_not_preserve_same_partition_bound(self):
        """Guard the reason remove_binary is excluded from BMC preprocessing."""
        direct = UntilFormula(
            Interval(True, RealVal("0"), True, RealVal("1")),
            universeInterval, self.left, self.right,
        )
        reduced = remove_binary(direct)
        tau_values = (0.0, 1.5, 2.0)
        p_bits = (True, False, False, False)
        q_bits = (True, False, False, True)

        self.assertTrue(self._fully_stable_sat(
            direct, tau_values, p_bits, q_bits
        ))
        self.assertFalse(self._fully_stable_sat(
            reduced, tau_values, p_bits, q_bits
        ))

    def test_paper_time_ordering_allows_equal_internal_points(self):
        solver = z3.SolverFor("QF_LRA")
        solver.add(z3Obj(And([
            time_ordering(6, 2.0),
            Eq(Real("tau_1"), RealVal("0")),
            Eq(Real("tau_2"), RealVal("1")),
        ])))
        self.assertEqual(solver.check(), z3.sat)

    def test_paper_time_ordering_keeps_last_point_strict(self):
        solver = z3.SolverFor("QF_LRA")
        solver.add(z3Obj(And([
            time_ordering(6, 2.0),
            Eq(Real("tau_2"), RealVal("2")),
        ])))
        self.assertEqual(solver.check(), z3.unsat)

    def test_no_legacy_time_alias_or_unused_chi_terminal(self):
        formula = FinallyFormula(
            Interval(True, RealVal("0"), True, RealVal("1")),
            universeInterval, self.left,
        )
        _, timing, terminal = k_depth_stl_consts(
            calc_sub_formulas(formula), 4, 2.0
        )
        self.assertEqual(str(timing), "True")
        self.assertNotIn("T^", str(timing))
        self.assertNotIn("chi^", str(terminal))
        self.assertIn("rho^", str(terminal))

    def test_fully_stable_partition_requires_shifted_falling_endpoint(self):
        formula = FinallyFormula(
            Interval(True, RealVal("2"), True, RealVal("3")),
            universeInterval, self.left,
        )
        child_truth = (False, False, False, False, False, True)
        unused_truth = (False,) * len(child_truth)

        # A fall at sup(J_6) creates the Definition 3.3 candidate
        # tau_3 - inf([2,3]). The old wat-ode/f2 counterexample used
        # tau=(0, 2.500489, 5.500489, 8), so candidate 6 was absent.
        self.assertFalse(self._fully_stable_sat(
            formula, (0, 2.500489, 5.500489, 8),
            child_truth, unused_truth, require_formula=False,
        ))
        self.assertTrue(self._fully_stable_sat(
            formula, (0, 3, 6, 8),
            child_truth, unused_truth, require_formula=False,
        ))

    def test_open_finally_rejects_current_point_witness(self):
        formula = FinallyFormula(
            Interval(False, RealVal("0"), False, RealVal("1")),
            universeInterval, self.left,
        )
        self.assertFalse(self._symbolic_truth(
            formula, (True, False, False, False)
        ))

    def test_closed_lower_finally_rejects_pre_boundary_truth(self):
        formula = FinallyFormula(
            Interval(True, RealVal("1"), False, RealVal("2")),
            universeInterval, self.left,
        )
        self.assertFalse(self._symbolic_truth(
            formula, (False, True, False, False)
        ))

    def test_strict_until_accepts_later_singleton_witness(self):
        formula = UntilFormula(
            Interval(False, RealVal("0"), False, RealVal("inf")),
            universeInterval, self.left, self.right,
        )
        self.assertTrue(self._symbolic_truth(
            formula,
            (True, True, True, False),
            (False, False, True, False),
        ))

    def test_strict_release_uses_until_dual_semantics(self):
        formula = ReleaseFormula(
            Interval(False, RealVal("0"), False, RealVal("inf")),
            universeInterval, self.left, self.right,
        )
        self.assertFalse(self._symbolic_truth(
            formula,
            (False, False, False, False),
            (False, True, False, True),
        ))


if __name__ == "__main__":
    unittest.main()
