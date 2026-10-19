import sys
import unittest
from types import SimpleNamespace
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

import z3

from stlmc.constraints.constraints import (
    And, Bool, BoolVal, Eq, Geq, Gt, Int, Integral, Leq, Lt, Not, Ode, Or, Real, RealVal,
)
from stlmc.encoding.batching import (
    candidate_batch_formula, partitioned_candidate_batch_formula,
)
from stlmc.algorithms.two_step import (
    assert_and_track_assignment, boolean_core_assignments, get_bools,
    evaluated_arithmetic_literals, relevant_boolean_abstract_links,
    rename, scenario_enumeration_finished, time_path2const, type1_index_info,
)
from stlmc.encoding.static_learning import renamed_discrete_variable
from stlmc.encoding.model_linking import path2const, contradiction_gen
from stlmc.encoding.symbolic_discrete import chi
from stlmc.solver.abstract_solver import SolverStatus
from stlmc.solver.z3 import Z3FormulaSolver, z3Obj
from stlmc.algorithms.scenario_refinement import is_temporal_auxiliary
from stlmc.algorithms.shared_stl import bounded_proposition_matching


class ScenarioMinimizationPolarityTest(unittest.TestCase):
    false = BoolVal("False")

    def test_full_matching_rejects_incompatible_false_interval_label(self):
        proposition = Lt(Real('g'), RealVal('7.5'))
        model = SimpleNamespace(mode_var_dict={}, modules=[{}], boolean_abstract={})
        for bound in range(2):
            start, end = Real(f'g_{bound}_0'), Real(f'g_{bound}_t')
            model.boolean_abstract[Bool(f'newIntegral_0_{bound}')] = Integral(
                0, [end], [start], Ode([start], [RealVal('0')]))
        previous, selected = chi(2, 2, proposition), chi(4, 4, proposition)
        solver = z3.Solver()
        solver.add(z3Obj(And([
            Eq(previous, BoolVal('False')), Eq(selected, BoolVal('True')),
            Eq(Real('tau_0'), RealVal('0')), Eq(Real('tau_1'), RealVal('1')),
            Eq(Real('tau_2'), RealVal('2')),
            Eq(Real('currentMode_0'), RealVal('0')),
            Eq(Real('currentMode_1'), RealVal('0')),
            Eq(Real('g_0_0'), Real('g_0_t')),
            Eq(Real('g_0_t'), Real('g_1_0')),
            Eq(Real('g_1_0'), Real('g_1_t')),
        ])))
        # The old positive-only reconstruction accepts this impossible signal.
        solver.add(z3Obj(path2const({(4, selected): proposition}, model)))
        self.assertEqual(solver.check(), z3.sat)
        solver.add(z3Obj(bounded_proposition_matching(model, {proposition}, 4)))
        self.assertEqual(solver.check(), z3.unsat)

    def test_only_private_temporal_helpers_are_untracked(self):
        for name in ('rho^{1,2}_p', 'parU^{1,2}_p', 'parEndfall^{1,2}_p'):
            self.assertTrue(is_temporal_auxiliary(Bool(name)))
        for name in ('chi^{1,1}_p', 'newIntegral_0_0', 'invAtomicID_0', 'mode'):
            self.assertFalse(is_temporal_auxiliary(Bool(name)))
        self.assertFalse(is_temporal_auxiliary(Real('rho^{1,2}_p')))

    def test_conditional_core_blocking_retains_background(self):
        auxiliary, primary = z3.Bools('auxiliary primary')
        # A failed refinement under A=true does not justify blocking pi alone.
        alternative = z3.And(primary, z3.Not(auxiliary))
        solver = z3.Solver()
        solver.add(alternative, z3.Not(z3.And(auxiliary, primary)))
        self.assertEqual(solver.check(), z3.sat)
        solver.add(z3.Not(primary))
        self.assertEqual(solver.check(), z3.unsat)

    def test_interval_learning_respects_open_endpoints_and_empty_intervals(self):
        proposition = Gt(Real("x"), RealVal("0"))
        flag = chi(2, 2, proposition)
        intervals, points = contradiction_gen({flag}, {proposition})
        for start, end, value, duration, expected in (
                (0, 1, True, 1, z3.sat),
                (-1, 0, False, 1, z3.sat),
                (0, 0, True, 1, z3.sat),
                (-1, 1, True, 1, z3.unsat),
                (1, -1, False, 1, z3.unsat),
                (-1, -1, True, 0, z3.sat)):
            with self.subTest(start=start, end=end, value=value, duration=duration):
                solver = z3.Solver()
                solver.add(z3Obj(And([
                    intervals, points, Eq(flag, BoolVal(str(value))),
                    Eq(Real("x_0_0"), RealVal(str(start))),
                    Eq(Real("x_0_t"), RealVal(str(end))),
                    Eq(Real("tau_0"), RealVal("0")),
                    Eq(Real("tau_1"), RealVal(str(duration))),
                ])))
                self.assertEqual(solver.check(), expected)

    def test_flow_proposition_matches_both_polarities_on_open_interval(self):
        start, end = Real("x_0_0"), Real("x_0_t")
        integral = Integral(0, [end], [start], Ode([start], [RealVal("1")]))
        model = SimpleNamespace(
            mode_var_dict={}, modules=[{}],
            boolean_abstract={Bool("newIntegral_0_0"): integral},
        )
        flag = Bool("interval-proposition")
        matching = path2const({(2, flag): Gt(Real("x"), RealVal("2"))}, model)
        # x evolves from initial to final with derivative +1. A crossing
        # inside the interval must be rejected for either Boolean value.
        # Equality at an excluded endpoint must remain allowed.
        for initial, final, truth, expected in (
                (0, 10, False, z3.unsat), (0, 10, True, z3.unsat),
                (0, 2, False, z3.sat), (2, 10, True, z3.sat),
                (2, 2, False, z3.sat), (2, 2, True, z3.sat)):
            with self.subTest(initial=initial, final=final, truth=truth):
                solver = z3.Solver()
                solver.add(z3Obj(And([
                    matching, Eq(start, RealVal(str(initial))),
                    Eq(end, RealVal(str(final))),
                    Eq(Real("currentMode_0"), RealVal("0")),
                    Eq(Real("tau_0"), RealVal("0")),
                    Eq(Real("tau_1"), RealVal(str(final - initial))),
                    Eq(flag, BoolVal(str(truth))),
                ])))
                self.assertEqual(solver.check(), expected)

    def test_refinement_helpers_are_strategy_subcomponents(self):
        self.assertEqual(
            relevant_boolean_abstract_links.__module__,
            "stlmc.algorithms.scenario_refinement",
        )

    def test_symbolic_identifier_helpers_are_strategy_subcomponents(self):
        self.assertEqual(
            rename.__module__, "stlmc.encoding.symbolic_ids"
        )
        self.assertEqual(type1_index_info("chi^{2,5}_formula"), (2, 5))

        renamed, mapping = rename(
            And([Bool("enabled"), Gt(Real("x"), RealVal("0"))]),
            3,
            is_vertex=False,
        )
        self.assertIn(Bool("enabled_3"), mapping.values())
        self.assertIn(Real("x_2_t"), mapping.values())
        self.assertIn("x_2_t", repr(renamed))

    def test_scenario_path_decoding_is_a_strategy_subcomponent(self):
        self.assertEqual(
            get_bools.__module__, "stlmc.encoding.path_decoding"
        )
        left, right = Bool("left"), Bool("right")
        self.assertEqual(get_bools(Eq(left, right)), {left, right})

    def test_scenario_constraint_generation_is_a_strategy_subcomponent(self):
        self.assertEqual(
            time_path2const.__module__,
            "stlmc.encoding.model_linking",
        )
        constraint = time_path2const({
            (3, Bool("p@clock")): Leq(Real("x"), RealVal("1")),
        })
        self.assertIn("clock", repr(constraint))
        self.assertIn("x_1_0", repr(constraint))
        self.assertNotIn("x_0_t", repr(constraint))

    def test_slicing_keeps_boolean_dependency_closure(self):
        a, b, c, unused = (Bool(name) for name in ("a", "b", "c", "unused"))
        links = relevant_boolean_abstract_links(
            {a: b, b: c, c: BoolVal("True"), unused: BoolVal("False")},
            a,
        )

        text = str(links)
        self.assertIn("(a = b)", text)
        self.assertIn("(b = c)", text)
        self.assertIn("(c = True)", text)
        self.assertNotIn("unused", text)

    def test_slicing_inlines_boolean_core_assignments(self):
        a, b = Bool("a"), Bool("b")
        assignments = boolean_core_assignments(
            And([Eq(a, BoolVal("True")), Eq(b, BoolVal("False"))])
        )
        links = relevant_boolean_abstract_links(
            {
                a: Geq(Real("x"), RealVal("0")),
                b: Leq(Real("y"), RealVal("1")),
            },
            And([a, b]),
            assignments,
        )

        text = str(links)
        self.assertIn("(x >= 0)", text)
        self.assertIn("(not (y <= 1))", text)
        self.assertNotIn("(a =", text)
        self.assertNotIn("(b =", text)

    def test_preprocessing_is_existentially_equivalent(self):
        a, b, c, unused = (Bool(name) for name in ("a", "b", "c", "unused"))
        x = Real("x")
        abstraction = {
            a: Geq(x, RealVal("0")),
            b: c,
            c: Leq(x, RealVal("2")),
            unused: Geq(x, RealVal("100")),
        }
        roots = And([
            Eq(a, BoolVal("True")),
            Eq(b, BoolVal("False")),
        ])
        assignments = boolean_core_assignments(roots)
        original = And([
            roots,
            And([
                Eq(variable, definition)
                for variable, definition in abstraction.items()
            ]),
        ])
        preprocessed = And([
            roots,
            relevant_boolean_abstract_links(
                abstraction, roots, assignments
            ),
        ])

        abstract_variables = [z3Obj(variable) for variable in abstraction]
        solver = z3.Solver()
        solver.add(z3.Xor(
            z3.Exists(abstract_variables, z3Obj(original)),
            z3.Exists(abstract_variables, z3Obj(preprocessed)),
        ))

        self.assertEqual(solver.check(), z3.unsat)

    def test_false_boolean_literal_keeps_its_polarity(self):
        solver = Z3FormulaSolver()
        proposition = Bool("proposition")
        literal = assert_and_track_assignment(
            solver, proposition, self.false, "boolean-false"
        )
        solver.add(proposition)
        self.assertEqual(literal, Eq(proposition, self.false))
        self.assertEqual(solver.check(), SolverStatus.UNSAT)
        self.assertIn("boolean-false", solver.unsat_core())

    def test_false_arithmetic_literal_is_available_to_the_core(self):
        solver = Z3FormulaSolver("QF_LRA")
        x = Real("x")
        clause = Gt(x, RealVal("0"))
        literal = assert_and_track_assignment(
            solver, clause, self.false, "arithmetic-false"
        )
        solver.add(clause)
        self.assertEqual(literal, Eq(clause, self.false))
        self.assertEqual(solver.check(), SolverStatus.UNSAT)
        self.assertIn("arithmetic-false", solver.unsat_core())

    def test_temporal_auxiliary_core_implies_the_checked_formula(self):
        # Without fixed definitions, temporal variables must remain tracked.
        # Treating their model values as untracked context can produce a pi for which
        # pi and not(Psi) is satisfiable.
        auxiliary = Bool("rho^{aux}")
        primary = Bool("primary")
        psi = And([Eq(auxiliary, primary), auxiliary])
        assignments = {
            "auxiliary": Eq(auxiliary, BoolVal("True")),
            "primary": Eq(primary, BoolVal("True")),
        }
        solver = Z3FormulaSolver()
        for track_id, literal in assignments.items():
            solver.track(literal, track_id)
        solver.add(Not(psi))

        self.assertEqual(solver.check(), SolverStatus.UNSAT)
        core_literals = [assignments[item] for item in solver.unsat_core()]
        implication_check = Z3FormulaSolver()
        implication_check.add(And(core_literals))
        implication_check.add(Not(psi))
        self.assertEqual(implication_check.check(), SolverStatus.UNSAT)

    def test_unsat_core_is_subset_minimal(self):
        a, b, redundant = (Bool(name) for name in ("a", "b", "redundant"))
        assignments = {
            "a-track": Eq(a, BoolVal("True")),
            "b-track": Eq(b, BoolVal("True")),
            "redundant-track": Eq(redundant, BoolVal("True")),
        }
        base = Not(And([a, b]))
        solver = Z3FormulaSolver()
        solver.add(base)
        for track_id, literal in assignments.items():
            solver.track(literal, track_id)

        self.assertEqual(solver.check(), SolverStatus.UNSAT)
        core = solver.unsat_core()
        self.assertNotIn("redundant-track", core)
        for omitted in core:
            necessity_check = Z3FormulaSolver()
            necessity_check.add(base)
            necessity_check.add(And([
                assignments[item] for item in core if item != omitted
            ]))
            self.assertEqual(
                necessity_check.check(), SolverStatus.SAT,
                "core literal {} is not necessary".format(omitted),
            )

    def test_concrete_scenario_keeps_arithmetic_clause_polarity(self):
        x = Real("x")
        clause = Gt(x, RealVal("0"))
        solver = Z3FormulaSolver("QF_LRA")
        solver.add(Leq(x, RealVal("0")))
        self.assertEqual(solver.check(), SolverStatus.SAT)
        literals = evaluated_arithmetic_literals({clause}, {x}, solver.model())
        self.assertEqual(literals, [Eq(clause, self.false)])

    def test_candidate_batch_factors_shared_constraints(self):
        common = Bool("common")
        first = Bool("first")
        second = Bool("second")
        batch = candidate_batch_formula([
            (common, first),
            (common, second),
        ])
        self.assertEqual(
            repr(batch), repr(And([common, Or([first, second])]))
        )

    def test_candidate_batch_preserves_distinct_constraints(self):
        common_a = Bool("common-a")
        common_b = Bool("common-b")
        first = Bool("first")
        second = Bool("second")
        batch = candidate_batch_formula([
            (common_a, first),
            (common_b, second),
        ])
        self.assertEqual(repr(batch), repr(Or([
            And([common_a, first]),
            And([common_b, second]),
        ])))

    def test_partitioned_batch_cannot_drop_partition_condition(self):
        partition = Bool("partition")
        batch = partitioned_candidate_batch_formula(
            [(Bool("common"), Bool("scenario"))], partition
        )
        solver = z3.Solver()
        solver.add(z3Obj(batch), z3Obj(Not(partition)))
        self.assertEqual(solver.check(), z3.unsat)

    def test_unknown_finishes_unchanged_scenario_query(self):
        self.assertTrue(scenario_enumeration_finished(SolverStatus.UNKNOWN))
        self.assertTrue(scenario_enumeration_finished(SolverStatus.UNSAT))
        self.assertFalse(scenario_enumeration_finished(SolverStatus.SAT))

    def test_static_learning_renames_numeric_mode_variables(self):
        self.assertEqual(
            renamed_discrete_variable(Real("mode"), 3), Real("mode_3")
        )
        self.assertEqual(
            renamed_discrete_variable(Int("mode"), 2), Int("mode_2")
        )
        self.assertIsNone(renamed_discrete_variable(Bool("mode"), 1))


if __name__ == "__main__":
    unittest.main()
