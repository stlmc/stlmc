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
        self.assertIn("1 - 0", derivative)
        self.assertNotIn("1 - 1", derivative)

        model.make_invariant_consts(0, integrals)
        forall = next(
            value for value in model.boolean_abstract.values()
            if type(value).__name__ == "Forall"
        )
        translated = drealObj(forall)
        self.assertNotIn("forall_t", translated)
        self.assertIn("currentMode_0", translated)


if __name__ == "__main__":
    unittest.main()
