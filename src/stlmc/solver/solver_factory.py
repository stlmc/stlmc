import os
import shutil

from ..exceptions import SolverUnavailableError
from .availability import find_dreal


class SolverFactory:
    def generate_core_solver_factory(self):
        """Select the core backend independently of scenario enumeration."""
        return SolverFactory.generate_formula_solver_factory(self, role="core")

    def generate_formula_solver_factory(self, backend=None, role="scenario"):
        """Return the internal exact-theory solver adapter factory."""
        if role not in ("scenario", "core"):
            raise ValueError("unknown internal solver role: {}".format(role))
        backend = (backend or os.environ.get(
            "STLMC_{}_SOLVER".format(role.upper()), "z3"
        )).strip().lower()
        adapters = {
            "z3": ("z3", "Z3FormulaSolver"),
            "yices": ("yices", "YicesFormulaSolver"),
            "cvc5": ("cvc5", "CVC5FormulaSolver"),
        }
        if backend not in adapters:
            raise SolverUnavailableError(
                "unknown internal {} solver: {}".format(role, backend)
            )
        try:
            from importlib import import_module
            module, name = adapters[backend]
            return getattr(import_module(".{}".format(module), __package__), name)
        except Exception as error:
            raise SolverUnavailableError(
                "{} is unavailable for {} solving. Run: stlmc-install-solvers {}".format(
                    backend, role, backend
                )
            ) from error

    def generate_solver(self, config):
        common_section = config.get_section("common")
        solver_type = common_section.get_value("solver")
        if solver_type == 'z3':
            try:
                from ..solver.z3 import Z3Solver
            except (ImportError, OSError) as error:
                raise SolverUnavailableError(
                    "Z3 is unavailable. Run: stlmc-install-solvers z3"
                ) from error
            return Z3Solver(config)
        elif solver_type == 'dreal':
            dreal_section = config.get_section("dreal")
            executable = dreal_section.get_value("executable-path")
            if executable == "dReal":
                executable = find_dreal() or executable
            elif not os.path.dirname(executable):
                executable = shutil.which(executable) or executable
            if not os.path.isfile(executable) or not os.access(executable, os.X_OK):
                raise SolverUnavailableError(
                    "dReal executable was not found or is not executable: {}. "
                    "Run: stlmc-install-solvers dreal, or pass "
                    "-executable-path /path/to/dReal".format(executable)
                )
            dreal_section.set_value("executable-path", executable)
            from ..solver.dreal import dRealSolver
            return dRealSolver(config)
        elif solver_type == 'yices':
            try:
                from ..solver.yices import YicesSolver
            except Exception as error:
                raise SolverUnavailableError(
                    "Yices is unavailable. Run: stlmc-install-solvers yices"
                ) from error
            return YicesSolver(config)
        elif solver_type == 'cvc5':
            try:
                from ..solver.cvc5 import CVC5Solver
            except (ImportError, OSError) as error:
                raise SolverUnavailableError(
                    "CVC5 is unavailable. Run: stlmc-install-solvers cvc5"
                ) from error
            return CVC5Solver(config)
        raise SolverUnavailableError(
            "unknown solver: {}".format(solver_type)
        )
