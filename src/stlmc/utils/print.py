import sys
import time
from importlib.metadata import PackageNotFoundError, version


def _installed_version():
    try:
        return version("stlmc")
    except PackageNotFoundError:
        return "development"


class BasePrinter:
    def __init__(self):
        self.verbose = False
        self.debug = False
        self._bound_header_printed = False
        self._progress_active = False
        self._last_progress_update = None

    def print_normal(self, text: str):
        print(text, flush=True)

    def print_normal_dark(self, text: str):
        print(text, flush=True)

    def print_verbose(self, text: str):
        if self.verbose:
            print(text, flush=True)

    def print_debug(self, text: str):
        if self.debug:
            print(text, flush=True)

    def print_line(self):
        print("======================================", flush=True)

    def run_started(self, model, goal, solver, algorithm, parallel, workers,
                    max_bound, bound_kind, time_bound, threshold, query_kind):
        self._bound_header_printed = False
        self.clear_progress()
        self._last_progress_update = None
        execution = "parallel ({} workers)".format(workers) if parallel else "sequential"
        lines = [
            "STLMC v{}".format(_installed_version()),
            "Signal Temporal Logic Model Checker",
            "",
            "Configuration",
            "  model       : {}".format(model),
            "  goal        : {}".format(goal),
            "  solver      : {}".format(solver),
            "  algorithm   : {}".format(algorithm),
            "  execution   : {}".format(execution),
            "  max bound   : {}".format(max_bound),
            "  bound kind  : {}".format(bound_kind),
            "  time bound  : {}".format(time_bound),
            "  threshold   : {}".format(threshold),
            "  query       : {}".format(query_kind),
            "",
        ]
        self.print_normal("\n".join(lines))

    def bound_finished(self, bound, result, elapsed, scenarios=None,
                       constraint_size=None, found_scenario=None,
                       witness_label="counterexample"):
        self.clear_progress()
        self._last_progress_update = None
        if not self._bound_header_printed:
            self.print_normal("Bound checks")
            self._bound_header_printed = True

        prefix = "bound={:<6}".format(bound)
        query_field = "query={:<7}".format(result)
        fields = [prefix]
        if scenarios is not None:
            scenario_field = "scenarios={:<10}".format(scenarios)
            fields.append(scenario_field)
        fields.append(query_field)
        if self.verbose and constraint_size is not None:
            fields.append("const-size={:<10}".format(constraint_size))
        fields.append("time={:.3f}s".format(elapsed))
        if found_scenario is not None:
            fields.append(
                "{}=scenario {}".format(witness_label, found_scenario)
            )
        line = "  {}".format("\t".join(fields))
        self.print_normal(line)

    def scenario_progress(self, bound, generated, submitted, completed, pending,
                          submitted_jobs, completed_jobs, active_workers):
        if not sys.stdout.isatty():
            return
        if not self._bound_header_printed:
            self.print_normal("Bound checks")
            self._bound_header_printed = True
        now = time.monotonic()
        if (
            self._last_progress_update is not None
            and now - self._last_progress_update < 0.1
        ):
            return
        self._last_progress_update = now
        text = (
            "  bound={}\tgenerated={}\tsubmitted={}\tcompleted={}\t"
            "pending={}\tjobs={}/{}\tactive={}".format(
                bound, generated, submitted, completed, pending,
                completed_jobs, submitted_jobs, active_workers,
            )
        )
        print("\r\033[2K{}".format(text), end="", flush=True)
        self._progress_active = True

    def clear_progress(self):
        if self._progress_active:
            print("\r\033[2K", end="", flush=True)
            self._progress_active = False

    def run_finished(self, status, bound, elapsed, formula, scope,
                     counterexample=None, visual_config=None):
        self.clear_progress()
        lines = [
            "",
            "Result",
            "  status      : {} {}".format(status, scope),
            "  time        : {:.3f}s".format(elapsed),
            "  formula     : {}".format(formula),
        ]
        if counterexample is not None:
            lines.append("  artifacts   : {}".format(counterexample))
        if visual_config is not None:
            lines.append("                {}".format(visual_config))
        lines.append("")
        self.print_normal_dark("\n".join(lines))


class Printer(BasePrinter):
    def __init__(self):
        super().__init__()

class ExceptionPrinter(BasePrinter):
    def __init__(self):
        super().__init__()
