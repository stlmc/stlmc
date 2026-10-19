# Tests

Start with the setup and Make targets below. Detailed
[suite coverage](#suite-coverage) follows the execution instructions.

## Make targets

Before installing the checkout, prepare the Ruby, Bundler, and locked Jekyll
gems described in [frontend development](../docs/architecture.md#workspace-frontend-development).

Install the current checkout in editable mode before running the tests. This
ensures that the `stlmc` command used by the benchmark runner points to the
code being tested:

```sh
python -m pip install -e .
stlmc-installer install --solver z3 cvc5 yices dreal --visualize html pdf --ui
stlmc-installer check --solver z3 cvc5 yices dreal --visualize html pdf --ui
python -m pip install httpx==0.28.1
```

The full workflow requires cvc5, Z3, the Yices binding/native library, dReal,
and optional UI dependencies. HTTPX is a test-only dependency for the UI API
tests, not an STLmc runtime requirement. UI API tests are skipped when their
optional test dependencies are unavailable. Unit/integration tests use real
SMT libraries; they are not a solver-free installation check.

Standalone solver smoke tests additionally require the `z3` and `yices-smt2`
executables in `PATH`. Python bindings alone do not provide this contract:
the installer does not add managed native executable directories to `PATH`.
Use the command-line tools from your solver installation and verify them before
running smoke tests:

```sh
command -v z3
command -v yices-smt2
z3 --version
yices-smt2 --version
```

Add your solver installation's `bin` directory to `PATH` if necessary. Its
native dependencies must also be discoverable by the operating-system loader;
the managed Yices Python loader's private CUDD preload does not configure an
independently launched `yices-smt2`. See [installation](../docs/installation.md)
for native dependency requirements.

The smoke and benchmark runners use `3rd_party/dReal3/dReal` by default,
not the CLI's automatic solver discovery. To use the installed managed dReal:

```sh
export STLMC_DREAL="$(python -c 'from stlmc.solver.availability import find_dreal; print(find_dreal() or "")')"
```

Check that this points to an executable before running the tests.
Parallel final-Yices cases require a native library verified as thread-safe;
see [Yices source builds](../docs/installation.md#yices-source-builds).

Run every discovered unit/integration suite without the standalone smoke
programs or benchmarks:

```sh
make test-unit
```

This uses `unittest discover` with `*.py`, including flow validation, SymPy
differentiation, and documentation checks. To run those two validation suites
separately, use `make test-flow-warnings` and `make test-sympy-differentiation`.

Run unit/integration tests, solver smoke tests, all annotated benchmarks, and
the CVC5/Z3/Yices benchmark comparison:

```sh
make test
```

The full research benchmark set includes difficult cases that may time out.
The runner checks the recorded logical expectations and reports timeouts and
mismatches as failures; it does not silently skip or relabel them.
`make test` is therefore not currently an all-green release gate.

Select the cases marked `@benchmark.fast` while retaining all unit/integration
and smoke tests:

```sh
make test FAST=1
```

`FAST=1` changes selection, concurrency, and timeouts, not expected outcomes.
Its annotations include research cases too, so it is not a guaranteed-passing
alternative.

Run the release workflow selection: all unit/integration and smoke checks,
cases marked `@benchmark.quick`, and a CVC5/Z3/Yices comparison sample.
Quick benchmarks run four at a time with a 200-second timeout per case;
the comparison sample uses 120 seconds per case. The current quick selection
contains 23 cases. It excludes the polynomial battery and both bouncing-ball
fixtures, plus `tank-bounded-ode/f1`; their full/fast cases remain available.
Selection follows the current model annotations:

```sh
make test-quick SMOKE_ARGS=--allow-known-dreal-bugs
```

Override quick benchmark concurrency or output location when needed:

```sh
make test-quick QUICK_JOBS=2 QUICK_OUTPUT=/tmp/stlmc-quick-logs
```

Run only the SMT solver smoke tests:

```sh
make test-smoke
```

Smoke checks are strict by default. Release CI explicitly uses
`make test-quick SMOKE_ARGS=--allow-known-dreal-bugs` to observe the official
dReal 3.16.06.02 zero-derivative invariant defect as a separate `XFAIL`, not
a correctness pass. This exception requires the exact pinned fixture,
arguments, expected-result hashes, official version, and known faulty output.
Other versions, changed inputs, unexpected outputs, errors, and timeouts do
not receive an exception. A correct result is reported as successful `XPASS`.
`smoke_policy.py` tests this narrowly scoped policy without native solvers.

Run the standalone CVC5 adapter test:

```sh
make test-cvc5-solver
```

Run the solver installer and executable-discovery tests without downloading or
installing external software:

```sh
make test-install-solvers
```

Run only the solver formula capability tests:

```sh
make test-capabilities
```

Run only the STL robustness transformation tests:

```sh
make test-robustness
```

Run only the bounded temporal reduction tests:

```sh
make test-temporal-reduction
```

Run only the scenario minimization and literal-polarity tests:

```sh
make test-scenario-minimization
```

Run only the CLI schema, default-value, and lazy-help tests for `stlmc` and
`stlmc-vis`:

```sh
make test-cli-help
```

Run only the parallel solver process cleanup tests:

```sh
make test-process-cleanup
```

Run only the reachability semantics tests:

```sh
make test-reachability
```

Compare CVC5 and Z3 with the existing Yices benchmark logs for every Yices
model case:

```sh
make test-solver-equivalence
```

With `FAST=1`, the comparison includes every Yices case marked with
`@benchmark.fast` except cases marked with `@benchmark.z3-slow`; without it,
all Yices benchmark cases are compared. Outputs are stored beside the normal
logs with `.cvc5.log` and `.z3.log` suffixes. Any unexpected timeout is a test
failure. The full run uses the longer
default timeout and includes all `z3-slow` cases.

Run `make benchmark` first if the matching Yices logs do not exist. `make test`
does this automatically before starting the solver comparison. The comparison
runner verifies the accompanying manifest and rejects logs generated from a
different commit, model, or configuration.

Run only benchmarks:

```sh
make benchmark
```

Run only the quick release benchmark cases with their fixed 200-second
per-case timeout:

```sh
make benchmark-quick
```

Run one formula from one model, with a per-case timeout and solver candidate
batch size:

```sh
make benchmark MODEL=space-ode/space FORMULA=f3 TIMEOUT=60 BATCH=8
```

`MODEL` is relative to `tests/benchmarks` and omits the `.model` suffix.
`FORMULA` is the goal-specific configuration suffix, such as `f1`, `f2`, or
`f3`. `BATCH` is passed to STLMC as `-solver-batch-size` and controls how many
candidate refinements are combined in one solver OR query. It is not specific
to dReal.

## Benchmark options

Make variables can be combined on the command line:

- `FAST=1`: selects all cases marked with `@benchmark.fast`, a 300-second
  timeout, and four concurrent jobs unless those values are explicitly
  overridden. Selection follows annotations, not a promise that every case
  succeeds on every platform or solver version.
- `ARTIFACT_SCOPE=<directory>`: runs only a model directory below
  `tests/benchmarks`; the default is `.` for every model.
- `ARTIFACT_JOBS=<count>`: number of benchmark cases executed concurrently;
  the default is `1` (`4` with `FAST=1`).
- `ARTIFACT_TIMEOUT=<seconds>`: timeout applied separately to each benchmark
  and Z3 comparison case; the default is `3600` (`300` with `FAST=1`).
- `ARTIFACT_OUTPUT=<directory>`: output log directory; the default is
  `artifact-logs`.
- `QUICK_JOBS=<count>`: concurrency for `benchmark-quick` and the benchmark
  portion of `test-quick`; the default is `4`.
- `QUICK_OUTPUT=<directory>`: output directory for `benchmark-quick`; it falls
  back to `ARTIFACT_OUTPUT` and then `artifact-logs`.
- `MODEL=<directory/model>`: runs only the named model below
  `tests/benchmarks`, without the `.model` suffix. This option applies to the
  `benchmark` target.
- `FORMULA=<name>`: runs only one goal-specific configuration for `MODEL`,
  such as `f3`. `MODEL` is required when this option is used.
- `BATCH=<count>`: passes the solver candidate batch size to STLMC. The value
  must be at least `1`.
- `SCOPE=<directory>`, `TIMEOUT=<seconds>`, and `OUTPUT=<directory>`: concise
  aliases for `ARTIFACT_SCOPE`, `ARTIFACT_TIMEOUT`, and `ARTIFACT_OUTPUT` when
  using the `benchmark` target.
- `PYTHON=<executable>`: Python interpreter used to run the test scripts; the
  default is `python3`.

Examples:

```sh
make test ARTIFACT_JOBS=2 ARTIFACT_TIMEOUT=1800
make benchmark ARTIFACT_SCOPE=car-linear ARTIFACT_JOBS=3
make test FAST=1 ARTIFACT_SCOPE=wat-linear ARTIFACT_JOBS=2
make benchmark ARTIFACT_OUTPUT=/tmp/stlmc-logs
make benchmark SCOPE=rail-poly TIMEOUT=300 BATCH=8
make benchmark MODEL=space-ode/space FORMULA=f3 TIMEOUT=60 BATCH=8
```

The benchmark runner uses the installed `stlmc` command. Set `STLMC` to use a
specific executable. Both the smoke and benchmark runners use
`3rd_party/dReal3/dReal` by default; set `STLMC_DREAL` to override the dReal
executable path for both runners.

Pressing `Ctrl+C` in either benchmark runner cancels pending cases, terminates
active `stlmc` and solver processes, and exits with status `130`. Additional
interrupts are ignored while cleanup is in progress. Processes that do not
stop within five seconds are killed.

## Benchmark directory convention

See the [benchmark directory convention](benchmarks/README.md) when adding
fixtures. Directories without goal-specific configurations are not included
in automated benchmark runs.

## Benchmark results
The [benchmark conventions](benchmarks/README.md) define expectation
annotations, goal-specific configuration names, and fixture layout. STL cases
use `satisfied` and `violated`; reachability cases use `reachable` and
`unreachable`.
A `satisfied` expectation means that no counterexample was found within the
configured time window and discrete bound at the configured threshold. It is
not a proof for unbounded time or arbitrarily many partition points.

Some artifact goals have shorter temporal/global windows or revised predicates
and operators for regression testing. Their results cover the current fixture,
not the original artifact's verification scope; see the
[benchmark scope notes](benchmarks/README.md). Quick/fast membership is unchanged
by these goal revisions. Passing the revised cases alone is not a full-suite
validation claim.

For reachability cases, the expected bound is the number of jumps and
starts at zero. For STL cases, it also includes STL variable points. Bound
zero represents one continuous segment with no jump. Both one-step and
two-step algorithms use this convention.

Execution logs are written to `artifact-logs/` by default. Violated cases also
generate their `.counterexample` and visualization `.cfg` files beside the
corresponding log. Each benchmark model has a separate output directory, so
cases running in parallel cannot overwrite one another's artifacts.

Numerically reconstruct and check generated counterexamples with:

```sh
python tests/validate_artifacts.py artifact-logs
```

This evaluates sampled robustness against `rho(phi, 0) <= epsilon` and checks
that stored dReal midpoints lie inside their interval boxes. It does not
certify every initial, jump, invariant, and flow constraint or an exact ODE
trajectory. See [Result semantics](../docs/result-semantics.md). New artifacts
use versioned gzip-compressed JSON. Legacy pickle files are outdated and
unsupported; regenerate them by rerunning model checking with current STLmc.

## Suite coverage

The unit/integration suites and standalone benchmark tools cover:

- `application_boundaries.py` checks typed run options, property-independent
  bounded-search results, legacy tuple compatibility, and typed solver status.
- `application_workflow.py` checks parser-error translation, per-goal model
  state isolation, and cleanup when an algorithm fails.
- `parser_inputs.py` parses benchmark models and configurations through the
  public Lark parser APIs and checks the visualization configuration format.
  Invalid closed-form fixtures are checked for explicit input-validation
  errors rather than a verification result.
  Jump encoding checks preserve single, conjunctive, and disjunctive resets,
  and retain STL variable-point transitions when an explicit jump is disabled.
- `solution_functions.py` checks the manual's `x(t) = e(t, x(0))` semantics,
  rejects incomplete or undeclared closed-form flows, and verifies endpoint
  and invariant encodings for CVC5, Z3, Yices, and dReal. Yices SMT2 export
  is independently replayed to check lowered-variable declarations and
  quoted internal symbol names.
- `flow_warnings.py` checks polynomial flow diagnostics: nonzero constant
  initial offsets are errors; state-dependent initial differences and restart
  inconsistencies remain advisory. It covers source locations, valid coupled
  flows, and unchanged input models. Unsupported or oversized expressions are
  skipped; absence of a diagnostic is not a validity certificate.
- `sympy_differentiation.py` checks structural arithmetic conversion, exact
  rational constants, typed symbols, explicit clock selection, unsupported
  domains, and 300 generated derivative comparisons against analytic
  coefficients using independent Z3 equivalence checks.
- `cvc5_solver.py` checks CVC5 factory selection, SAT assignments, and UNSAT
  results through the STLmc solver adapter.
- `dreal_assignment.py` checks preservation of dReal interval boxes and
  consistency of their visualization midpoints.
- `smoke_solvers.py` runs small SMT2 inputs against Yices, Z3, and dReal and
  compares their standard output with the corresponding `.expected` files.
  The independent dReal `smt2/dreal/interior-peak.smt2` smoke case checks an
  interior-peak violation under a universal constraint, expecting `unsat` with
  precision `0.000001` and ODE step `0.01` supplied by its `.args` file.
- `solver_capabilities.py` verifies solver-specific arithmetic validation and
  dReal inverse-trigonometric translations. It also checks 300 generated
  Boolean propagation equivalences, branch-local assignment isolation, and
  preservation of flow atoms and original dReal variable declarations.
  Z3/Yices/CVC5 final solver jobs are checked for SAT/UNSAT and retained
  Boolean/numeric assignments.
  Only dReal final verification jobs propagate unconditional Boolean
  assignments before translation; Z3/Yices/CVC5 retain their original inputs.
  This does not change scenario/core solver assertions or rewrite arithmetic,
  ODE, or quantified-flow bodies.
- `ode_translation.py` checks exact polynomial ODE solutions independently
  with SymPy, including coupled acceleration, endpoint terms, indexed names,
  and rejection of unsupported cycles or elapsed-time collisions.
- `ode_capabilities.py` checks that algebraic backends accept supported exact
  ODE translations and reject unsupported evolving-state systems before
  solving; native dReal does not use this polynomial lowering.
- `invariant_names.py` checks distinct module/atom/bound namespaces, including
  multi-digit indices, and that later bounds cannot disable earlier invariant
  constraints in Z3/Yices queries.
- `numeric_mode_matching.py` checks that numeric mode identifiers retain
  their declared types and mode indices in proposition matching and interval
  refinements, without phantom continuous-state endpoint variables.
- `visualize_numeric.py` checks safe numeric parsing and sampled robustness,
  including Real/Int mode arithmetic, equality, and expressions mixing
  discrete modes with continuous state variables.
- `incremental_core_backends.py` checks the common Z3/Yices/CVC5 incremental
  solver contract: exact model values, tracked core replay, nested scopes,
  independent forks, private guards, and cancellation and unknown results.
  It also checks independent internal backend selection and clear errors for
  unavailable backends. Optional native backends are skipped when unavailable.
- `robustness_operations.py` checks STL weakening, strengthening, negation,
  and implication polarity transformations.
- `temporal_reduction.py` checks the fully-stable temporal encoding, including
  shared one-step/two-step components, partition obligations, strict interval
  endpoints, bounded Until/Release recurrence semantics, and deterministic
  solver input order across processes.
- `time_horizon.py` checks common segment-duration bounds, backend-independent
  one-step/two-step behavior, reachability, and preservation of duration limits
  in final refinements after scenario generalization.
- `formula_formatting.py` checks display-only Boolean flattening without
  changing encoding trees, hashes, or structural identifiers.
- `auto_solver.py` checks availability-aware automatic selection, isolated
  runtime probes, selected-goal filtering, and candidate configuration overrides.
- `dreal_runtime.py` checks bounded native capability probes, invalid-runtime
  rejection, and the narrowly identified official-release exception for
  ignored universal conditions on zero-derivative variables. The exception is
  recorded as a known limitation, not evidence of ODE correctness.
- `scenario_minimization.py` checks that Boolean and arithmetic scenario
  literals retain their true/false polarity, concrete scenarios preserve
  arithmetic clauses, and repeated core minimization never selects a larger
  core.
- `scenario_core_integration.py` replays extracted cores against the full
  negated encoding and compares one-step/two-step results across path,
  preprocessing, and batching options. It checks that refinement and blocking
  retain the conditions needed for core validity, and that proposition
  matching preserves both truth polarities.
- `cli_help.py` checks that the CLI schema, `default.cfg`, and generated help
  remain synchronized and that importing the visualization CLI does not load
  Bokeh or the full visualizer. Cancellation tests cover signals during native
  argument conversion and partially initialized Z3 objects without unraisable
  destructor exceptions. Documentation tests run the README quick-start model
  and check public links and test entry points.
- `install_solvers.py` checks solver selection and status behavior, platform
  installation commands, dReal installation permissions and locations, and
  executable discovery precedence without accessing the network.
- `installer_components.py` checks Yices source-build activation and
  format-specific visualization dependencies with mocked downloads and OS
  commands. Bokeh is an optional HTML dependency; PDF uses optional Matplotlib.
  Neither renderer is needed for text output. Installer actions require an
  explicit action; installation and removal require component selectors.
  `installer_ui.py` covers optional UI selection, version pins, and conservative
  removal. `ui_bridge.py` covers authenticated API access, loopback serving,
  safe artifact access, and the package-local worker.
- `solver_runtime.py` checks solver-free help, missing-backend installation
  hints, managed Yices library discovery, and native thread-safety/MCSAT guards.
  Capability-policy tests do not execute unsafe native calls under mocked
  thread-safety flags.
- `process_cleanup.py` verifies that parallel solver workers share one bounded
  cleanup deadline and are forcefully reaped when graceful termination stalls.
  It also checks that completed batches update scenario and job progress in
  their respective units, including batches containing multiple scenarios.
  Sequential solver waits poll cancellation requests and reap their workers;
  a real CLI SIGTERM test checks exit 130 without an orphan process.
- `reachability.py` checks zero-jump reachability, unreachable results,
  threshold relaxation, symbolic/explicit path strategies with one-step and
  two-step solving, CVC5/Z3/Yices/dReal agreement, temporal-target validation, and
  witness generation.
- `compare_solvers.py` reruns every Yices benchmark case with CVC5 and Z3, then
  checks that all three solvers produce the same status and finishing bound. It reuses the
  Yices logs from the preceding benchmark run instead of running Yices twice.
- `run_artifact_benchmarks.py` runs the model cases under `benchmarks/` and
  compares each result and finishing bound with the annotation in its model.
  The [bouncing-ball benchmark](benchmarks/bouncing-ball-ode/README.md) uses
  this same model/configuration-to-result/bound comparison. All six goals have
  registered expectations and are included in the full and fast selections,
  but not quick release checks.
  Shorter one-second windows keep `f1`, `f2`, `f4`, and `f5` checks fast;
  `f3` and `rebound` retain three-second windows containing the first bounce.
  Each log has a JSON manifest containing the git commit, input hashes,
  command, timeout, and result, so solver comparisons reject stale logs.
  The `tank-ode/tank-f2` case covers bound-zero STL checking of a jump-free
  ODE model, ensuring that its initial continuous segment is not skipped.
  Separate fixtures cover the [bounded tank ODE](benchmarks/tank-bounded-ode/README.md),
  [triangular-wave ODE](benchmarks/triangular-wave-ode/README.md), and
  [bouncing-ball polynomial model](benchmarks/bouncing-ball-poly/README.md).
  Their original dynamics and goals are retained; goal-specific finite windows
  and bounds define the fast regression scope. These fixtures use the same
  result/bound comparison and keep the independent native solver smoke separate.

## Dependency updates

Base Python dependencies are pinned in `pyproject.toml`. Managed solver and
renderer versions are defined in `src/stlmc/cli/dependency_policy.py`, with
Python transitive pins in `src/stlmc/cli/dependency-constraints.txt`.
Update one pin at a time and
run `make test-unit`, the selected release checks, and relevant benchmark
comparisons. Solver APIs, model values, performance, and witness selection can
change between releases. Investigate full-suite failures and record limits
explicitly; do not change benchmark expectations solely to make a test pass.
