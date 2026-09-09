# Architecture

STLmc separates transport, application orchestration, domain encoding, and
solver infrastructure. Dependencies point inward from the CLI and adapters to
the application workflow; encoding code does not parse command-line options or
format final user output.

```text
CLI
  CliCommand ── layered configuration loading
      │
      ▼
Application
  VerificationWorkflow
      ├── RunPreparer ── model loading, validation, solver/algorithm selection
      └── GoalExecutor ── goal execution, outcome reporting, artifacts
              │
              ▼
Domain and encoding
  Model / Goal / Formula AST
  OneStepAlgorithm / TwoStepAlgorithm / PathProvider
              │
              ▼
Infrastructure
  JobSolver / SolverJob / sequential and parallel runners
  ProgressTracker / worker cleanup policy
  CVC5 / Z3 / Yices / dReal adapters
```

## Boundary types

`RunOptions` is the immutable, typed view of the parser's layered
`Configuration`. Parsing and backward-compatible string storage stop at this
boundary. Algorithms consume typed bounds, thresholds, flags, and worker
counts. The hidden development flag `use_unary_bounded_temporal_form` defaults
to `True`: after the paper's `not(phi^+epsilon)` robust-to-Boolean reduction,
the counterexample formula is converted to an equivalent form whose bounded
temporal operators are unary before it enters the
fully-stable encoding. Setting it to `False` supplies the direct binary-temporal
form instead. This input-form
selection is the only branch; subformula collection, partition construction,
STL/model encoding, solving, and counterexample reporting remain shared. Both
forms describe the same continuous-time counterexample set, but they need not
find a witness at the same fully-stable partition bound, and an SMT solver may
select different trajectories from that set.

`SolverStatus` represents `SAT`, `UNSAT`, and `UNKNOWN`. Solver adapters retain
their historical `SolveResult.result` string for external compatibility, while
internal execution uses `SolveResult.status`.

`SearchStatus` represents the result of bounded exploration without conflating
it with property truth: a witness was found, the bounded space was exhausted,
or the search was inconclusive. `VerificationOutcome` translates that result
to `violated`/`satisfied` or `reachable`/`unreachable` at the presentation
boundary.

Execution progress and worker lifecycle are separate from result evaluation.
`ProgressTracker` accounts for scenarios and jobs in their respective units,
while `execution.cleanup` owns graceful termination, the shared cleanup
deadline, forced termination, and worker reaping.

## Compatibility

The old driver classes and import facades remain adapters only. The executable
uses `CliCommand` and `VerificationWorkflow` directly. New application code
should depend on `stlmc.application`, not `stlmc.driver` or compatibility
modules under `stlmc.objects` and `stlmc.encoding`.
