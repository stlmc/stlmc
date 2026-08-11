# Tests

The test suite has five parts:

- `smoke_solvers.py` runs small SMT2 inputs against Yices, Z3, and dReal and
  compares their standard output with the corresponding `.expected` files.
- `solver_capabilities.py` verifies solver-specific arithmetic validation and
  dReal inverse-trigonometric translations.
- `reachability.py` checks zero-jump reachability, unreachable results,
  threshold relaxation, one-step/two-step agreement, Z3/Yices/dReal
  agreement, temporal-target validation, and witness generation.
- `compare_solvers.py` reruns every Yices benchmark case with Z3, then checks
  that both solvers produce the same status and finishing bound. It reuses the
  Yices logs from the preceding benchmark run instead of running Yices twice.
- `run_artifact_benchmarks.py` runs the model cases under `benchmarks/` and
  compares each result and finishing bound with the annotation in its model.

Benchmark expectations use this format:

```text
# @benchmark.expected(f1=violated:5, f2=satisfied:10, f3=violated:4)
```

The expected bound is the number of discrete jumps and starts at zero. Bound
zero represents one continuous segment with no jump. Both one-step and
two-step algorithms use this convention.

Execution logs are written to `artifact-logs/` by default. Violated cases also
generate their `.counterexample` and visualization `.cfg` files beside the
corresponding log. Each benchmark model has a separate output directory, so
cases running in parallel cannot overwrite one another's artifacts.

## Make targets

Install the current checkout in editable mode before running the tests. This
ensures that the `stlmc` command used by the benchmark runner points to the
code being tested:

```sh
python -m pip install -e .
```

Run all five test parts in order: solver smoke tests, formula capability tests,
reachability tests, every annotated benchmark, and the Z3/Yices comparison:

```sh
make test
```

Run the fast selection of all five test parts. This currently runs the smoke,
capability, and reachability tests, 30 FAST benchmark cases, and 20 Z3/Yices
comparisons:

```sh
make test FAST=1
```

Run only the SMT solver smoke tests:

```sh
make test-smoke
```

Run only the solver formula capability tests:

```sh
make test-capabilities
```

Run only the reachability semantics tests:

```sh
make test-reachability
```

Compare Z3 with the existing Yices benchmark logs for every Yices model case:

```sh
make test-solver-equivalence
```

With `FAST=1`, the comparison includes every Yices case marked with
`@benchmark.fast` except cases marked with `@benchmark.z3-slow`; without it,
all Yices benchmark cases are compared. The current fast comparison contains
20 cases. Z3 outputs are stored beside the normal logs with a `.z3.log`
suffix. Any unexpected timeout is a test failure. The full run uses the longer
default timeout and includes all `z3-slow` cases.

Run `make benchmark` first if the matching Yices logs do not exist. `make test`
does this automatically before starting the solver comparison. The comparison
runner does not check whether an existing Yices log is stale, so regenerate
the benchmark logs after changing a model, configuration, or STLMC code.

Run only benchmarks:

```sh
make benchmark
```

Run one formula from one model, with a per-case timeout and two-step scenario
batch size:

```sh
make benchmark MODEL=space-ode/space FORMULA=f3 TIMEOUT=60 BATCH=8
```

`MODEL` is relative to `tests/benchmarks` and omits the `.model` suffix.
`FORMULA` is the goal-specific configuration suffix, such as `f1`, `f2`, or
`f3`. `BATCH` is passed to STLMC as `-scenario-batch-size` and affects the
scenario enumeration performed by the two-step algorithm; it is not specific
to dReal.

## Benchmark options

Make variables can be combined on the command line:

- `FAST=1`: selects all cases marked with `@benchmark.fast`, a 120-second
  timeout, and four concurrent jobs unless those values are explicitly
  overridden. The current fast set contains 30 cases. Cases that timed out or
  had unstable runtimes during parallel execution are not marked as fast, but
  remain part of the full benchmark run without `FAST=1`. Currently these are
  all `bat-ode` cases, `car-ode/f3`, `rail-ode/f1`, `space-ode/f2`, and
  `wat-ode/f1`.
- `ARTIFACT_SCOPE=<directory>`: runs only a model directory below
  `tests/benchmarks`; the default is `.` for every model.
- `ARTIFACT_JOBS=<count>`: number of benchmark cases executed concurrently;
  the default is `1` (`4` with `FAST=1`).
- `ARTIFACT_TIMEOUT=<seconds>`: timeout applied separately to each benchmark
  and Z3 comparison case; the default is `3600` (`120` with `FAST=1`).
- `ARTIFACT_OUTPUT=<directory>`: output log directory; the default is
  `artifact-logs`.
- `MODEL=<directory/model>`: runs only the named model below
  `tests/benchmarks`, without the `.model` suffix. This option applies to the
  `benchmark` target.
- `FORMULA=<name>`: runs only one goal-specific configuration for `MODEL`,
  such as `f3`. `MODEL` is required when this option is used.
- `BATCH=<count>`: passes the two-step scenario batch size to STLMC. The value
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

Each runnable benchmark directory contains one model configuration and one or
more goal-specific configurations:

```text
tests/benchmarks/rail-poly/
  rail.model
  rail.cfg
  rail-f1.cfg
  rail-f2.cfg
  rail-f3.cfg
```

Directories without goal-specific `*-fN.cfg` files are retained as example
models and are not included in automated benchmark runs.
