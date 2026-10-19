import sys
import math
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.constraints.robustness import release_robustness, until_robustness
from stlmc.constraints.constraints import (
    Add, And, Bool, Div, Eq, Geq, Gt, Implies, Leq, Lt, Neq, Not, Or, Real,
    RealVal, Sub,
)
from stlmc.constraints.operations import relaxing, strengthening
from stlmc.constraints.formatting import infix
from stlmc.artifacts.formula_index import index_subformulas


class RobustnessOperationsTest(unittest.TestCase):
    def setUp(self):
        self.x = Real("x")
        self.zero = RealVal("0")
        self.epsilon = RealVal("0.5")

    def test_bat_ode_analytic_robust_counterexample_with_strict_margin(self):
        from stlmc.constraints.constraints import FinallyFormula, GloballyFormula
        from stlmc.constraints.interval import Interval, universeInterval
        from stlmc.constraints.logical_normalization import reduce_not
        from stlmc.constraints.temporal_rewrite import to_unary_bounded_temporal_form
        from stlmc.visualize.robustness import robustness

        g, d = Real('g1'), Real('d1')
        switch = 1.002
        peak = 2/.122*math.expm1(.122*switch)
        # Exact ON -> OFF solution with initial g=8, d=0. All invariants,
        # ranges and the g>1 switch guard hold. This is an independent
        # physical trajectory, not a certification of a solver's bound-3 box.
        times = [[0., .5, 1.], [1., switch], [switch, 3., 4., 7., 10.]]
        samples = {
            g: [[8-.5*min(t, switch) for t in part] for part in times],
            d: [[2/.122*math.expm1(.122*t) if t <= switch
                 else peak*math.exp(-.05*(t-switch)) for t in part]
                for part in times],
        }
        goal = GloballyFormula(
            Interval(True, RealVal('3'), True, RealVal('4')), universeInterval,
            Implies(Lt(g, RealVal('6')), FinallyFormula(
                Interval(True, RealVal('0'), True, RealVal('6')), universeInterval,
                Geq(d, RealVal('3')))))
        counterexample = reduce_not(Not(strengthening(goal, 1.5)))
        equivalent = to_unary_bounded_temporal_form(counterexample)
        # On [3,4], g=7.499 and d is positive, decreasing and <3.
        # Hence rho(goal)=1.499, with a strict .001 threshold margin.
        self.assertLess(peak, 3.)
        for formula, expected in ((goal, 1.499), (counterexample, .001),
                                  (equivalent, .001)):
            with self.subTest(formula=str(formula)):
                self.assertAlmostEqual(
                    robustness(formula, samples, {}, 0., times, 10., {}),
                    expected, places=12)

    def test_car_ode_analytic_robust_counterexample_at_threshold(self):
        from stlmc.constraints.constraints import FinallyFormula, GloballyFormula
        from stlmc.constraints.interval import Interval, universeInterval
        from stlmc.constraints.logical_normalization import reduce_not
        from stlmc.constraints.temporal_rewrite import to_unary_bounded_temporal_form
        from stlmc.visualize.robustness import robustness

        rx, ry = Real('rx'), Real('ry')
        # Exact mode-3 solution: rx=1-t, theta=1/2+t/20,
        # ry=-3+40*(cos(theta)-cos(13/20)). Thus ry(3)=-3.
        times = [[0., .5, 1.], [1., 1.5, 2., 2.5, 3.], [3., 4., 5.]]
        samples = {
            rx: [[1-t for t in part] for part in times],
            ry: [[-3+40*(math.cos(.5+.05*t)-math.cos(.65))
                  for t in part] for part in times],
        }
        goal = GloballyFormula(
            Interval(True, RealVal('0'), True, RealVal('2')), universeInterval,
            Implies(Gt(rx, RealVal('2')), FinallyFormula(
                Interval(True, RealVal('2'), True, RealVal('3')), universeInterval,
                Lt(ry, RealVal('-1')))))
        counterexample = reduce_not(Not(strengthening(goal, 2.0)))
        equivalent = to_unary_bounded_temporal_form(counterexample)
        # Both branches of the implication robustness increase with time;
        # the outer G minimum is max(1,-1-ry(3))=2 at time zero.
        for formula, expected in ((goal, 2.0), (counterexample, 0.0),
                                  (equivalent, 0.0)):
            with self.subTest(formula=str(formula)):
                self.assertAlmostEqual(
                    robustness(formula, samples, {}, 0., times, 5., {}),
                    expected, places=12)

    def test_atomic_weakening_matches_maude_rules(self):
        self.assertEqual(relaxing(Gt(self.x, self.zero), 0.5),
                         Gt(self.x, Sub(self.zero, self.epsilon)))
        self.assertEqual(relaxing(Lt(self.x, self.zero), 0.5),
                         Lt(self.x, Add(self.zero, self.epsilon)))
        self.assertEqual(relaxing(Eq(self.x, self.zero), 0.5), And([
            Geq(self.x, Sub(self.zero, self.epsilon)),
            Leq(self.x, Add(self.zero, self.epsilon)),
        ]))
        self.assertEqual(relaxing(Neq(self.x, self.zero), 0.5), Or([
            Lt(self.x, Add(self.zero, self.epsilon)),
            Gt(self.x, Sub(self.zero, self.epsilon)),
        ]))

    def test_infix_preserves_comparison_operators(self):
        self.assertEqual(infix(Gt(self.x, self.zero)), "x > 0")
        self.assertEqual(infix(Geq(self.x, self.zero)), "x >= 0")
        self.assertEqual(infix(Lt(self.x, self.zero)), "x < 0")
        self.assertEqual(infix(Leq(self.x, self.zero)), "x <= 0")
        self.assertEqual(infix(Eq(self.x, self.zero)), "x == 0")
        self.assertEqual(infix(Neq(self.x, self.zero)), "x != 0")

    def test_visualizer_boolean_robustness_uses_discrete_truth(self):
        from stlmc.visualize.visualizer import robustness

        self.assertEqual(
            robustness.__module__, "stlmc.visualize.robustness"
        )
        proposition = Bool("enabled")
        times = [[0.0, 1.0]]
        self.assertEqual(
            robustness(
                proposition, {}, {proposition: [[1, -1]]},
                0.0, times, 1.0, {},
            ),
            float("inf"),
        )
        self.assertEqual(
            robustness(
                proposition, {}, {proposition: [[1, -1]]},
                1.0, times, 1.0, {},
            ),
            float("-inf"),
        )

    def test_comparison_robustness_handlers_preserve_direction(self):
        from stlmc.visualize.visualizer import robustness

        # Dispatch may share the arithmetic implementation; its annotation is
        # not part of the public contract. All four registrations must retain
        # the appropriate robustness sign, including at the boundary.
        for comparison, sign in ((Lt, -1), (Leq, -1), (Gt, 1), (Geq, 1)):
            self.assertIsNot(robustness.dispatch(comparison), robustness.dispatch(object))
            for sample in (-2.0, 0.0, 2.0):
                with self.subTest(comparison=comparison.__name__, sample=sample):
                    self.assertEqual(
                        robustness(
                            comparison(self.x, self.zero), {self.x: [[sample]]}, {},
                            0.0, [[0.0]], 0.0, {},
                        ),
                        sign * sample,
                    )
    def test_atomic_strengthening_matches_maude_rules(self):
        self.assertEqual(strengthening(Gt(self.x, self.zero), 0.5),
                         Gt(self.x, Add(self.zero, self.epsilon)))
        self.assertEqual(strengthening(Lt(self.x, self.zero), 0.5),
                         Lt(self.x, Sub(self.zero, self.epsilon)))
        self.assertEqual(strengthening(Neq(self.x, self.zero), 0.5), Or([
            Lt(self.x, Sub(self.zero, self.epsilon)),
            Gt(self.x, Add(self.zero, self.epsilon)),
        ]))

    def test_negation_reverses_polarity(self):
        atom = Lt(self.x, self.zero)
        self.assertEqual(relaxing(Not(atom), 0.5),
                         Not(strengthening(atom, 0.5)))
        self.assertEqual(strengthening(Not(atom), 0.5),
                         Not(relaxing(atom, 0.5)))

    def test_double_negation_continues_normalizing_children(self):
        from stlmc.constraints.logical_normalization import reduce_not

        formula = Not(Not(And([Not(Lt(self.x, self.zero))])))
        self.assertEqual(
            reduce_not(formula), And([Geq(self.x, self.zero)])
        )

    def test_implication_antecedent_is_contravariant(self):
        antecedent = Lt(self.x, self.zero)
        consequent = Gt(self.x, self.zero)
        formula = Implies(antecedent, consequent)
        self.assertEqual(relaxing(formula, 0.5), Implies(
            strengthening(antecedent, 0.5), relaxing(consequent, 0.5)
        ))
        self.assertEqual(strengthening(formula, 0.5), Implies(
            relaxing(antecedent, 0.5), strengthening(consequent, 0.5)
        ))

    def test_until_uses_right_operand_at_witness(self):
        times = [0.0, 1.0, 2.0]
        left = {0.0: 2.0, 1.0: 2.0, 2.0: 2.0}
        right = {0.0: -5.0, 1.0: -5.0, 2.0: 3.0}

        value = until_robustness(
            times, lambda witness: [t for t in times if t <= witness],
            left.__getitem__, right.__getitem__,
        )

        self.assertEqual(value, 2.0)

    def test_release_uses_right_operand_at_witness(self):
        times = [0.0, 1.0, 2.0]
        left = {0.0: 3.0, 1.0: -5.0, 2.0: -5.0}
        right = {0.0: -2.0, 1.0: -2.0, 2.0: 4.0}

        value = release_robustness(
            times, lambda witness: [t for t in times if t <= witness],
            left.__getitem__, right.__getitem__,
        )

        self.assertEqual(value, 3.0)

    def test_empty_bounded_future_uses_temporal_identities(self):
        self.assertEqual(
            until_robustness([], lambda _: [], lambda _: 0, lambda _: 0),
            float("-inf"),
        )
        self.assertEqual(
            release_robustness([], lambda _: [], lambda _: 0, lambda _: 0),
            float("inf"),
        )

    def test_horizon_is_not_synthesized_as_a_future_sample(self):
        from stlmc.visualize.visualizer import get_sub_time_samples

        samples = [[0.0, 0.5, 1.0]]
        self.assertEqual(get_sub_time_samples(samples, 1.1, 2.0, 1.0), [])
        self.assertEqual(get_sub_time_samples(samples, 0.5, 1.0, 1.0), [0.5])
        self.assertEqual(
            get_sub_time_samples.__module__, "stlmc.visualize.sampling"
        )

    def test_artifact_formula_index_is_lightweight_and_deterministic(self):
        formula = Implies(Gt(self.x, self.zero), Leq(self.x, RealVal("2")))
        first_formulas, first_ids = index_subformulas(formula)
        second_formulas, second_ids = index_subformulas(formula)
        self.assertEqual(first_ids[formula], 0)
        self.assertEqual(
            sorted((repr(item), first_ids[item]) for item in first_formulas),
            sorted((repr(item), second_ids[item]) for item in second_formulas),
        )

    def test_latex_rendering_is_lightweight_and_handles_division(self):
        from stlmc.visualize.latex import formula2latex

        self.assertEqual(formula2latex(Div(self.x, RealVal("2"))), "(x / 2)")
        self.assertEqual(
            formula2latex.__module__, "stlmc.visualize.latex"
        )

    def test_numeric_evaluator_is_independent_from_plotting(self):
        from stlmc.visualize.numeric import infix_float

        expression = Div(Add(self.x, RealVal("2")), RealVal("2"))
        self.assertEqual(infix_float(expression, [4.0], [self.x]), 3.0)
        self.assertEqual(
            infix_float.__module__, "stlmc.visualize.numeric"
        )

    def test_assignment_projection_is_independent_from_plotting(self):
        from stlmc.visualize.projection import continuous_values
        from stlmc.visualize.visualizer import Projector

        first, second = Real("currentMode_0"), Real("currentMode_1")
        modules = [{"name": "zero"}, {"name": "one"}]
        projector = Projector(
            {second: RealVal("0"), first: RealVal("1")}, {}, {}, modules
        )
        self.assertEqual(Projector.__module__, "stlmc.visualize.projection")
        self.assertEqual(projector.get_ordered_mode_vars(), [first, second])
        self.assertEqual(
            projector.get_ordered_modules(), [modules[1], modules[0]]
        )
        self.assertEqual(projector.get_max_bound(), 1)

        x = Real("x")
        self.assertEqual(continuous_values({
            Real("x_0_0"): RealVal("1/2"),
            Real("x_0_t"): RealVal("3/2"),
        }, {x: (True, 0, 2, True)}, 0), {"x": [(0.5, 1.5)]})

    def test_plot_grouping_is_independent_from_plotting(self):
        from stlmc.visualize.visualizer import (
            flatten, pairwise_disjoint_check, split_groups,
        )

        groups = [{"x"}, {"rho"}]
        self.assertEqual(
            split_groups(groups, {"x"}, {"rho"}), ([{"x"}], [{"rho"}])
        )
        pairwise_disjoint_check(groups)
        self.assertEqual(flatten(groups), {"x", "rho"})
        self.assertEqual(flatten.__module__, "stlmc.visualize.grouping")
        with self.assertRaises(ValueError):
            pairwise_disjoint_check([{"x"}, {"x", "y"}])

    def test_bokeh_plot_construction_is_separate_from_facade(self):
        try:
            import bokeh
        except ImportError:
            self.skipTest("optional Bokeh HTML renderer is not installed")
        from stlmc.visualize.plotting import build_plot

        layout = build_plot(
            {self.x: [[0.0, 1.0]]}, {}, [[0.0, 1.0]], {}, "f", 0.0, {}
        )
        self.assertEqual(build_plot.__module__, "stlmc.visualize.plotting")
        self.assertEqual(len(layout.children), 1)


if __name__ == "__main__":
    unittest.main()
