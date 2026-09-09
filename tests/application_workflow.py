import sys
import unittest
from pathlib import Path
from unittest import mock


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.application.result import AlgorithmResult, SearchStatus
from stlmc.application.workflow import GoalExecutor, PreparedRun, VerificationWorkflow
from stlmc.constraints.constraints import Bool
from stlmc.exceptions import ParsingError
from stlmc.objects.goal import StlGoal


class FakeModel:
    def __init__(self):
        self.clear_count = 0

    def clear(self):
        self.clear_count += 1


class FakeAlgorithm:
    def __init__(self, results):
        self.results = iter(results)
        self.debug_names = []
        self.runner = None

    def set_debug(self, name):
        self.debug_names.append(name)

    def run(self, *args):
        result = next(self.results)
        if isinstance(result, BaseException):
            raise result
        return result


class FakePrinter:
    def __init__(self):
        self.verbose = False
        self.started = []
        self.finished = []
        self.progress_cleared = False

    def run_started(self, *args):
        self.started.append(args)

    def run_finished(self, *args):
        self.finished.append(args)

    def clear_progress(self):
        self.progress_cleared = True


class FakeRunner:
    def __init__(self):
        self.killed = False

    def kill_all(self):
        self.killed = True


class Options:
    solver = "z3"
    goal_labels = ()
    verbose = False
    reach = False
    two_step = False
    parallel = False
    parallel_core = 1
    bound = 2
    time_bound = 10.0
    threshold = 0.01
    visualize = False


def prepared_run(algorithm, goals):
    labels = {goal.get_formula(): "g{}".format(i) for i, goal in enumerate(goals)}
    return PreparedRun(
        "model.stlmc", object(), Options(), FakeModel(), {}, tuple(goals),
        labels, object(), algorithm,
    )


class GoalExecutorTest(unittest.TestCase):
    @mock.patch("stlmc.application.workflow.validate_formula_solver_support")
    def test_each_goal_gets_clean_model_state(self, validate):
        goals = [StlGoal(Bool("p")), StlGoal(Bool("q"))]
        algorithm = FakeAlgorithm([
            AlgorithmResult(SearchStatus.EXHAUSTED, 0.1, 1, legacy_status="True"),
            AlgorithmResult(SearchStatus.EXHAUSTED, 0.1, 2, legacy_status="True"),
        ])
        prepared = prepared_run(algorithm, goals)
        printer = FakePrinter()

        GoalExecutor().execute(prepared, printer)

        self.assertEqual(prepared.model.clear_count, 2)
        self.assertEqual(len(printer.finished), 2)
        self.assertEqual([item[0] for item in printer.finished], ["satisfied", "satisfied"])

    @mock.patch("stlmc.application.workflow.validate_formula_solver_support")
    def test_failed_goal_still_clears_model_state(self, validate):
        goal = StlGoal(Bool("p"))
        algorithm = FakeAlgorithm([RuntimeError("failed")])
        algorithm.runner = FakeRunner()
        prepared = prepared_run(algorithm, [goal])
        printer = FakePrinter()

        with self.assertRaisesRegex(RuntimeError, "failed"):
            GoalExecutor().execute(prepared, printer)

        self.assertEqual(prepared.model.clear_count, 1)
        self.assertTrue(printer.progress_cleared)
        self.assertTrue(algorithm.runner.killed)

    @mock.patch("stlmc.application.workflow.validate_formula_solver_support")
    def test_only_selected_goal_is_executed(self, validate):
        goals = [StlGoal(Bool("p")), StlGoal(Bool("q"))]
        algorithm = FakeAlgorithm([
            AlgorithmResult(SearchStatus.EXHAUSTED, 0.1, 2, legacy_status="True")
        ])
        prepared = prepared_run(algorithm, goals)
        prepared.options.goal_labels = ("g1",)
        printer = FakePrinter()

        GoalExecutor().execute(prepared, printer)

        self.assertEqual(len(printer.finished), 1)
        self.assertEqual(prepared.model.clear_count, 1)


class WorkflowErrorBoundaryTest(unittest.TestCase):
    def test_parser_syntax_error_becomes_application_parsing_error(self):
        command = mock.Mock()
        command.parse.side_effect = SyntaxError("bad model")
        workflow = VerificationWorkflow(preparer=mock.Mock(), executor=mock.Mock())

        with self.assertRaisesRegex(ParsingError, "bad model"):
            workflow.run(command, FakePrinter())


if __name__ == "__main__":
    unittest.main()
