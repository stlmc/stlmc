import tempfile
import unittest


class SolutionFunctionTest(unittest.TestCase):
    def parse(self, declarations, flow, invariant=""):
        from stlmc.parser.model_visitor import ModelVisitor

        source = """{}
{{ mode: true; inv: {} flow: {} jump: }}
init: true;
goal: true;
""".format(declarations, invariant, flow)
        with tempfile.NamedTemporaryFile("w", suffix=".model") as model_file:
            model_file.write(source)
            model_file.flush()
            return ModelVisitor().get_parse_tree(model_file.name)[0]

    def test_manual_closed_form_uses_local_duration_and_initial_values(self):
        from stlmc.constraints.constraints import Function

        model = self.parse(
            "[0, 100] x; [0, 100] y;",
            "x(t) = t ** 2 + 3 * t + x(0); y(t) = t + y(0);",
        )
        flow = model.modules[0]["flow"]
        self.assertIsInstance(flow, Function)
        _, integrals = model.make_flow_consts(0)
        expressions = [str(exp) for exp in integrals[0].dynamics.exps]
        self.assertIn("tau_1 - tau_0", expressions[0])
        self.assertIn("x_0_0", expressions[0])
        self.assertIn("y_0_0", expressions[1])

    def test_solution_lhs_must_be_declared_continuous_variable(self):
        from stlmc.exceptions import NotSupportedError

        with self.assertRaisesRegex(
            NotSupportedError, "solution function 'z'\\(t\\).*declared continuous"
        ):
            self.parse("[0, 10] x;", "z(t) = t;")

    def test_initial_reference_must_be_declared_continuous_variable(self):
        from stlmc.exceptions import NotSupportedError

        with self.assertRaisesRegex(
            NotSupportedError, "initial value 'z'\\(0\\).*declared continuous"
        ):
            self.parse("[0, 10] x;", "x(t) = t + z(0);")

    def test_bare_state_reference_explains_initial_value_syntax(self):
        from stlmc.exceptions import NotSupportedError

        with self.assertRaisesRegex(
            NotSupportedError, "bare state variable 'x'.*use x\\(0\\)"
        ):
            self.parse("[0, 10] x;", "x(t) = t + x;")

    def test_duplicate_solution_function_is_rejected(self):
        from stlmc.exceptions import NotSupportedError

        with self.assertRaisesRegex(
            NotSupportedError, "duplicate solution function for 'x'"
        ):
            self.parse("[0, 10] x;", "x(t) = t; x(t) = 2 * t;")

    def test_missing_solution_function_is_rejected(self):
        from stlmc.exceptions import NotSupportedError

        with self.assertRaisesRegex(
            NotSupportedError, "missing solution function.*y"
        ):
            self.parse("[0, 10] x; [0, 10] y;", "x(t) = t + x(0);")

    def test_solvers_use_endpoint_equalities(self):
        import cvc5

        from stlmc.solver.cvc5 import cvc5Obj
        from stlmc.solver.dreal import drealObj
        from stlmc.solver.yices import yicesObj
        from stlmc.solver.z3 import z3Obj

        model = self.parse("[0, 10] x;", "x(t) = t + x(0);")
        _, integrals = model.make_flow_consts(0)
        integral = integrals[0]
        self.assertIn("(= x_0_t", str(cvc5Obj(integral, cvc5.Solver())))
        self.assertIn("x_0_t ==", str(z3Obj(integral)))
        self.assertIn("(= x_0_t", yicesObj(integral))
        dreal = drealObj(integral)
        self.assertIn("(= x_0_t", dreal)
        self.assertNotIn("integral", dreal)
        self.assertNotIn("d/dt", dreal)

    def test_dreal_does_not_declare_solution_as_ode(self):
        from stlmc.solver.dreal import dRealSolver

        model = self.parse("[0, 10] x;", "x(t) = t + x(0);")
        _, integrals = model.make_flow_consts(0)
        declarations, _ = dRealSolver().get_declared_variables(
            integrals[0], 10, 10
        )
        self.assertFalse(any("define-ode" in line for line in declarations))

    def test_solution_invariant_derivative_uses_local_time(self):
        from stlmc.constraints.constraints import Real
        from stlmc.constraints.operations import diff
        from stlmc.solver.dreal import drealObj

        model = self.parse(
            "[0, 10] x;", "x(t) = t + x(0);", invariant="x >= 0;"
        )
        _, integrals = model.make_flow_consts(0)
        integral = integrals[0]
        derivative = str(diff(Real("x_0_0"), integral))
        self.assertIn("1", derivative)
        self.assertNotIn("1 - 1", derivative)

        model.make_invariant_consts(0, integrals)
        forall = next(
            value for value in model.boolean_abstract.values()
            if type(value).__name__ == "Forall"
        )
        translated = drealObj(forall)
        self.assertNotIn("forall_t", translated)
        self.assertIn("currentMode_0", translated)

    def test_strict_open_invariant_allows_zero_at_excluded_endpoint(self):
        from stlmc.constraints.constraints import (
            And, Eq, Forall, Function, Gt, Integral, Or, Real, RealVal,
        )
        from stlmc.constraints.translation import make_forall_consts

        start_value = Real("x_0_0")
        end_value = Real("x_0_t")
        integral = Integral(
            0, [end_value], [start_value],
            Function([start_value], [Real("tau_1")]),
        )
        translated = make_forall_consts(Forall(
            0, Real("tau_1"), RealVal("0"),
            Gt(start_value, RealVal("0")), integral,
        ))

        self.assertIsInstance(translated, Or)
        increasing_case = translated.children[0]
        self.assertIsInstance(increasing_case, And)
        endpoint_case = increasing_case.children[1]
        self.assertIsInstance(endpoint_case, Or)
        zero_then_positive = endpoint_case.children[1]
        self.assertIsInstance(zero_then_positive, And)
        self.assertIsInstance(zero_then_positive.children[0], Eq)
        self.assertEqual(zero_then_positive.children[0].left, start_value)
        self.assertIsInstance(zero_then_positive.children[1], Gt)
        self.assertEqual(zero_then_positive.children[1].left, end_value)

    def test_symbolic_derivative_evaluates_constant_exponent_without_eval(self):
        from stlmc.constraints.constraints import Pow, Real, RealVal, Sub
        from stlmc.constraints.differentiation import diff_aux

        exponent = Sub(RealVal("1"), RealVal("1"))
        self.assertEqual(
            diff_aux(Pow(Real("tau_1"), exponent)), RealVal("0")
        )

    def test_symbolic_derivative_capability_rejects_unsupported_functions(self):
        from stlmc.constraints.constraints import Function, Integral, Real, Sin
        from stlmc.constraints.differentiation import (
            diff, diff_aux, supports_symbolic_differentiation,
        )
        from stlmc.exceptions import NotSupportedError

        expression = Sin(Real("tau_1"))
        self.assertFalse(supports_symbolic_differentiation(expression))
        with self.assertRaisesRegex(
            NotSupportedError, "unsupported expression.*Sin"
        ):
            diff_aux(expression)

        start = Real("x_0_0")
        integral = Integral(
            0, [Real("x_0_t")], [start], Function([start], [expression])
        )
        with self.assertRaisesRegex(
            NotSupportedError, "polynomial invariant simplification"
        ):
            diff(start, integral)

    def test_zero_to_t_substitution_handles_logical_and_temporal_nodes(self):
        from stlmc.constraints.constraints import (
            Gt, Implies, Interval, Real, RealVal, UntilFormula,
        )
        from stlmc.constraints.normalization import substitution_zero2t

        interval = Interval(True, RealVal("0"), True, RealVal("1"))
        atom = Gt(Real("x_0_0"), RealVal("0"))
        logical = substitution_zero2t(Implies(atom, atom))
        temporal = substitution_zero2t(UntilFormula(interval, interval, atom, atom))

        self.assertIn("x_0_t", str(logical))
        self.assertIn("x_0_t", str(temporal))


if __name__ == "__main__":
    unittest.main()
