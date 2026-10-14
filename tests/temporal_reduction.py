import sys
import importlib.util
import unittest
from pathlib import Path

import z3


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.constraints.constraints import (
    And, Bool, BoolVal, Eq, FinallyFormula, GloballyFormula, Not, Or, Real,
    RealVal, ReleaseFormula, UntilFormula,
)
from stlmc.constraints.interval import (
    Interval, inInterval, is_positive_infinity, universeInterval,
)
from stlmc.constraints.temporal_rewrite import to_unary_bounded_temporal_form
from stlmc.constraints.logical_normalization import reduce_not
from stlmc.constraints.robustness_transform import relaxing, strengthening
import stlmc.algorithms.two_step as enumerate_encoding
import stlmc.algorithms.one_step as monolithic_encoding
from stlmc.algorithms.two_step import (
    calc_sub_formulas, chi,
    k_depth_stl_consts, rho, stl_depth_components,
    symbolic_goal, time_ordering,
)
from stlmc.encoding.fully_stable_partition import (
    FullyStablePartitionEncoding, fully_stable_partition_const,
    partition_obligations,
)
from stlmc.encoding.fully_stable_stl import prepare_fully_stable_stl_formula
from stlmc.encoding.symbolic_discrete import chi as shared_chi, formula_id
from stlmc.objects.goal import StlGoal
from stlmc.solver.z3 import z3Obj


class BoundedTemporalReductionTest(unittest.TestCase):
    def test_empty_interval_is_skipped_by_all_temporal_recurrences(self):
        interval = Interval(True, RealVal("0"), True, RealVal("3"))
        for formula, next_value, expected in (
                (FinallyFormula(interval, universeInterval, Bool("p")), False, False),
                (GloballyFormula(interval, universeInterval, Bool("p")), True, True),
                (UntilFormula(interval, universeInterval, Bool("p"), Bool("q")), True, True),
                (ReleaseFormula(interval, universeInterval, Bool("p"), Bool("q")), False, False)):
            with self.subTest(operator=type(formula).__name__):
                solver = z3.Solver()
                solver.add(z3Obj(And([
                    symbolic_goal(formula, 1, 4, 3),
                    Eq(Real("tau_0"), RealVal("0")),
                    Eq(Real("tau_1"), RealVal("1")),
                    Eq(Real("tau_2"), RealVal("1")),
                    Eq(rho(1, 5, formula), BoolVal(str(next_value))),
                    Eq(rho(1, 4, formula), BoolVal(str(not expected))),
                    Eq(chi(4, 4, Bool("p")), BoolVal(str(not next_value))),
                    Eq(chi(4, 4, Bool("q")), BoolVal("True")),
                ])))
                self.assertEqual(solver.check(), z3.unsat)

    def test_empty_interval_cannot_supply_a_future_witness(self):
        formula = FinallyFormula(
            Interval(True, RealVal("0"), True, RealVal("2")),
            universeInterval, self.left,
        )
        # Only J4=(tau1,tau2) has p=true, but tau1=tau2. All real
        # points and nonempty intervals have p=false.
        self.assertFalse(self._fully_stable_sat(
            formula, (0.0, 1.0, 1.0, 2.0),
            (False, False, False, True, False, False),
            (False,) * 6,
        ))

    def test_legacy_partition_encodings_are_removed(self):
        removed = (
            "stlmc.constraints.encoding",
            "stlmc.constraints.partition",
            "stlmc.constraints.separation",
            "stlmc.constraints.enhanced_partition",
            "stlmc.constraints.enhanced_separation",
            "stlmc.legacy",
        )
        self.assertFalse([
            name for name in removed if importlib.util.find_spec(name)
        ])

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

    def test_unary_bounded_form_rewrites_bounded_until(self):
        rewritten = to_unary_bounded_temporal_form(UntilFormula(
            self._interval(True), universeInterval, self.left, self.right,
        ))
        self.assertIsInstance(rewritten, And)
        self.assertEqual(3, len(rewritten.children))
        prefix, witness, continuation = rewritten.children
        self.assertIsInstance(prefix, GloballyFormula)
        self.assertIsInstance(witness, FinallyFormula)
        self.assertIsInstance(continuation, FinallyFormula)
        self.assertIsInstance(continuation.child, UntilFormula)
        self.assertEqual(universeInterval, continuation.child.local_time)

    def test_unary_bounded_form_rewrites_release_as_boolean_dual(self):
        rewritten = to_unary_bounded_temporal_form(ReleaseFormula(
            self._interval(False), universeInterval, self.left, self.right,
        ))
        self.assertIsInstance(rewritten, Or)
        self.assertEqual(3, len(rewritten.children))
        prefix, invariant, continuation = rewritten.children
        self.assertIsInstance(prefix, FinallyFormula)
        self.assertIsInstance(invariant, GloballyFormula)
        self.assertIsInstance(continuation, GloballyFormula)
        self.assertIsInstance(continuation.child, ReleaseFormula)
        self.assertFalse(continuation.child.local_time.left_end)

    def test_unary_bounded_form_recurses_below_unbounded_binary(self):
        nested = UntilFormula(
            universeInterval,
            universeInterval,
            self.left,
            UntilFormula(
                self._interval(True), universeInterval, self.left, self.right,
            ),
        )
        rewritten = to_unary_bounded_temporal_form(nested)
        self.assertIsInstance(rewritten, UntilFormula)
        self.assertIsInstance(rewritten.right, And)

    def test_formula_preparation_defaults_to_unary_bounded_temporal_form(self):
        goal = StlGoal(UntilFormula(
            self._interval(True), universeInterval, self.left, self.right,
        ))
        rewritten = prepare_fully_stable_stl_formula(goal, {}, 0.0)
        direct = prepare_fully_stable_stl_formula(goal, {}, 0.0, False)
        self.assertIsInstance(rewritten, Or)
        self.assertIsInstance(direct, ReleaseFormula)

    def test_paper_counterexample_reduction_precedes_formula_form_choice(self):
        formula = UntilFormula(
            self._interval(True), universeInterval, self.left, self.right,
        )
        paper_order = to_unary_bounded_temporal_form(
            reduce_not(Not(strengthening(formula, 0.1)))
        )
        legacy_order = relaxing(
            to_unary_bounded_temporal_form(reduce_not(Not(formula))), 0.1
        )
        self.assertEqual(paper_order, legacy_order)
        prepared = prepare_fully_stable_stl_formula(
            StlGoal(formula), {}, 0.1
        )
        self.assertEqual(paper_order, prepared)

    def test_equivalent_form_does_not_preserve_partition_bound(self):
        direct = UntilFormula(
            Interval(True, RealVal("0"), True, RealVal("1")),
            universeInterval, self.left, self.right,
        )
        unary_bounded = to_unary_bounded_temporal_form(direct)
        tau_values = (0.0, 1.5, 2.0)
        p_bits = (True, False, False, False)
        q_bits = (True, False, False, True)

        self.assertTrue(self._fully_stable_sat(
            direct, tau_values, p_bits, q_bits
        ))
        self.assertFalse(self._fully_stable_sat(
            unary_bounded, tau_values, p_bits, q_bits
        ))

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
            "bounded_stl_formula",
            monolithic_encoding.OneStepAlgorithm.run.__code__.co_names,
        )
        self.assertEqual(
            enumerate_encoding.k_size_stl_formula.__module__,
            "stlmc.algorithms.shared_stl",
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
        self.assertIn("FullyStablePartitionEncoding", two_step_names)
        self.assertIn("FullyStablePartitionEncoding", one_step_names)

    def test_partition_encoding_is_strategy_independent(self):
        self.assertEqual(
            fully_stable_partition_const.__module__,
            "stlmc.encoding.fully_stable_partition",
        )
        self.assertIs(chi, shared_chi)

    def test_stl_encoding_is_strategy_independent(self):
        self.assertEqual(
            symbolic_goal.__module__,
            "stlmc.encoding.fully_stable_stl",
        )
        self.assertEqual(
            k_depth_stl_consts.__module__,
            "stlmc.encoding.fully_stable_stl",
        )

    def test_structural_formula_identifier_is_cached(self):
        formula = UntilFormula(
            self._interval(True), universeInterval, self.left, self.right,
        )
        identifier = formula_id(formula)
        self.assertEqual(identifier, formula_id(formula))
        self.assertEqual(identifier, formula._stlmc_structural_id)
        self.assertEqual(len(identifier), 64)

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

    def test_incremental_partition_matches_fresh_encoding_at_each_depth(self):
        formula = UntilFormula(
            self._interval(True), universeInterval, self.left, self.right,
        )
        sub_formulas = calc_sub_formulas(formula)
        incremental = FullyStablePartitionEncoding(sub_formulas)
        for depth in range(1, 7):
            incremental.extend_to(depth)
            self.assertEqual(
                str(incremental.formula()),
                str(fully_stable_partition_const(sub_formulas, depth)),
            )

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
