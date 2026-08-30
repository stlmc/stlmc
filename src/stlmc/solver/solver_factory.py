import os
import shutil

from ..exceptions import SolverUnavailableError
from .availability import find_dreal


class SolverFactory:
    def generate_formula_solver_factory(self):
        """Return the internal exact-theory solver adapter factory."""
        try:
            from ..solver.z3 import Z3FormulaSolver
        except (ImportError, OSError) as error:
            raise SolverUnavailableError(
                "Z3 is unavailable. Run: stlmc-install-solvers z3"
            ) from error
        return Z3FormulaSolver

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
