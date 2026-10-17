import sys
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.constraints.constraints import (
    Arccos, Arcsin, Arctan, Cos, Pow, Real, RealVal, Sin, Sqrt, Tan,
)
from stlmc.exceptions import NotSupportedError
from stlmc.solver.capability import (
    expression_requires_dreal,
    validate_formula_solver_support,
)
from stlmc.solver.dreal import drealObj


class SolverCapabilityTest(unittest.TestCase):
    def test_boolean_propagation_preserves_generated_formulas(self):
        import random
        import z3
        from stlmc.constraints.constraints import (
            And, Bool, BoolVal, Eq, Implies, Neq, Not, Or,
        )
        from stlmc.constraints.boolean_simplification import propagate_boolean_constants
        from stlmc.solver.z3 import z3Obj
        rng = random.Random(20261018)
        variables = [Bool('simplify_'+str(i)) for i in range(4)]
        x = Real('simplify_x')
        atoms = variables + [BoolVal('True'), BoolVal('False'), x > RealVal('0')]
        def boolean_term(node):
            # Independent Boolean construction, including the standard
            # empty-AND/OR identities, rather than adapter normalization.
            if isinstance(node, And): return z3.And(*map(boolean_term, node.children))
            if isinstance(node, Or): return z3.Or(*map(boolean_term, node.children))
            if isinstance(node, Not): return z3.Not(boolean_term(node.child))
            if isinstance(node, Implies):
                return z3.Implies(boolean_term(node.left), boolean_term(node.right))
            if isinstance(node, Eq): return boolean_term(node.left) == boolean_term(node.right)
            if isinstance(node, Neq): return boolean_term(node.left) != boolean_term(node.right)
            return z3Obj(node)
        def generated(depth):
            if depth == 0 or rng.random() < .25:
                return rng.choice(atoms)
            operator = rng.choice((And, Or, Not, Eq, Neq, Implies))
            if operator is Not:
                return Not(generated(depth-1))
            if operator in (And, Or):
                return operator([generated(depth-1) for _ in range(rng.randrange(4))])
            return operator(generated(depth-1), generated(depth-1))
        for index in range(300):
            formula = And([generated(4), Eq(rng.choice(variables),
                                           BoolVal(str(bool(index % 2))))])
            solver = z3.Solver()
            solver.add(boolean_term(formula) != boolean_term(propagate_boolean_constants(formula)))
            self.assertEqual(solver.check(), z3.unsat, index)

    def test_boolean_propagation_does_not_leak_branch_assignments(self):
        import z3
        from stlmc.constraints.constraints import And, Bool, BoolVal, Eq, Implies, Not, Or
        from stlmc.constraints.boolean_simplification import propagate_boolean_constants
        from stlmc.solver.z3 import z3Obj
        p, q = Bool('branch_p'), Bool('branch_q')
        for formula in (
                Or([And([p, q]), And([Not(p), Not(q)])]),
                Implies(p, Eq(q, BoolVal('True'))),
                Not(And([p, q])),
                And([Eq(p, BoolVal('True')), Eq(p, BoolVal('False'))])):
            solver = z3.Solver()
            solver.add(z3Obj(formula) != z3Obj(propagate_boolean_constants(formula)))
            self.assertEqual(solver.check(), z3.unsat)

    def test_boolean_propagation_keeps_flow_atoms_and_dreal_declarations(self):
        import tempfile
        from stlmc.constraints.constraints import (
            And, Bool, BoolVal, Eq, Forall, Integral, Ode, Or, Not,
        )
        from stlmc.constraints.boolean_simplification import propagate_boolean_constants
        from stlmc.parser.config_visitor import ConfigVisitor
        from stlmc.solver.dreal import dRealSolver
        p = Bool('flow_choice')
        x = Real('x_0_0')
        integral = Integral(0, [Real('x_0_t')], [x],
                            Ode([Real('x_0_0_t')], [RealVal('1')]))
        condition = Forall(0, Real('tau_1'), Real('tau_0'),
                           x >= RealVal('0'), integral)
        formula = And([Eq(p, BoolVal('True')), integral,
                       Eq(Real('tau_0'), RealVal('0')),
                       Eq(Real('tau_1'), RealVal('1')),
                       Eq(Real('currentMode_0'), RealVal('0')),
                       Or([And([p, condition]), And([Not(p), BoolVal('False')])])])
        simplified = propagate_boolean_constants(formula)
        self.assertIn(str(condition), str(simplified))
        self.assertIn(str(integral), str(simplified))
        config = ConfigVisitor().parse_from_file(str(PROJECT_ROOT/'src/stlmc/default.cfg'))
        config.get_section('common').arguments['time-bound'] = '5'
        config.get_section('common').set_value('time-horizon', '2')
        with tempfile.TemporaryDirectory() as directory:
            config.get_section('common').set_value('save-smt2', 'true')
            config.get_section('common').set_value('smt2-dir', directory)
            backend = dRealSolver(config)
            command, cleanup = backend._prepare_solver_command(formula, 'propagation')
            content = Path(command[1]).read_text()
            self.assertIsNone(cleanup)
            self.assertEqual(content.count('forall_t'), 1)
            self.assertIn('(declare-fun tau_1', content)
            self.assertIn('(= flow_choice true)', content)

    def test_discrete_solvers_reject_transcendental_arithmetic(self):
        x = Real("x")
        expressions = (
            Sqrt(x), Sin(x), Cos(x), Tan(x),
            Arcsin(x), Arccos(x), Arctan(x),
        )
        for solver in ("cvc5", "z3", "yices"):
            for expression in expressions:
                with self.subTest(solver=solver, expression=expression):
                    with self.assertRaisesRegex(
                        NotSupportedError, "use dReal"
                    ):
                        validate_formula_solver_support(solver, expression)

    def test_discrete_solvers_accept_only_integer_constant_powers(self):
        x = Real("x")
        for solver in ("cvc5", "z3", "yices"):
            validate_formula_solver_support(
                solver, Pow(x, RealVal("2"))
            )
            for exponent in (RealVal("0.5"), RealVal("-1"), x):
                with self.subTest(solver=solver, exponent=exponent):
                    with self.assertRaisesRegex(
                        NotSupportedError, "non-negative integer"
                    ):
                        validate_formula_solver_support(
                            solver, Pow(x, exponent)
                        )

    def test_dreal_inverse_trigonometric_names(self):
        x = Real("x")
        expected = {
            Arcsin(x): "(asin x)",
            Arccos(x): "(acos x)",
            Arctan(x): "(atan x)",
        }
        for expression, output in expected.items():
            with self.subTest(expression=expression):
                self.assertEqual(drealObj(expression), output)

    def test_auto_solver_detects_nested_dreal_arithmetic(self):
        x = Real("x")
        self.assertTrue(expression_requires_dreal(Cos(Sqrt(x))))
        self.assertTrue(
            expression_requires_dreal(Pow(x, RealVal("0.5")))
        )
        self.assertFalse(expression_requires_dreal(Pow(x, RealVal("2"))))


if __name__ == "__main__":
    unittest.main()
