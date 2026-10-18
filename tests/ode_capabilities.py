"""Algebraic adapters must not silently approximate an unsupported ODE."""
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from stlmc.constraints.constraints import BoolVal, Ode, Real, RealVal
from stlmc.exceptions import NotSupportedError
from stlmc.solver.capability import validate_model_solver_support


def model(flow):
    return SimpleNamespace(init=BoolVal("True"), const_dict={}, modules=[{
        "mode": BoolVal("True"), "inv": BoolVal("True"), "jump": {},
        "flow": flow,
    }])


class OdeCapabilityTest(unittest.TestCase):
    def test_constant_acceleration_is_exactly_supported(self):
        x, v = Real("position"), Real("velocity")
        for solver in ("yices", "z3", "cvc5"):
            with self.subTest(solver=solver):
                validate_model_solver_support(solver, model(Ode([x, v], [v, RealVal("2")])))

    def test_cyclic_evolving_state_is_rejected_before_algebraic_solving(self):
        x = Real("position")
        for solver in ("yices", "z3", "cvc5"):
            with self.subTest(solver=solver):
                with self.assertRaisesRegex(NotSupportedError, "exact polynomial.*use dReal"):
                    validate_model_solver_support(solver, model(Ode([x], [x])))

    def test_native_dreal_does_not_use_polynomial_lowering(self):
        x = Real("position")
        with patch("stlmc.constraints.translation.polynomial_ode_solution",
                   side_effect=AssertionError("native ODE must not be lowered")) as lower:
            validate_model_solver_support("dreal", model(Ode([x], [x])))
            lower.assert_not_called()


if __name__ == "__main__":
    unittest.main()
