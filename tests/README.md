# Tests

The test suite has two independent parts:

- `smoke_solvers.py` runs small SMT2 inputs against Yices, Z3, and dReal and
  compares their standard output with the corresponding `.expected` files.
- `run_artifact_benchmarks.py` runs the model cases under `benchmarks/` and
  compares each result and finishing bound with the annotation in its model.

Benchmark expectations use this format:

```text
# @benchmark.expected(f1=violated:5, f2=satisfied:10, f3=violated:4)
```

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

Run the solver smoke tests followed by every annotated benchmark:

```sh
make test
```

Run a fast test consisting of the solver smoke tests and every benchmark case
marked with `@benchmark.fast`:

```sh
make test FAST=1
```

Run only the SMT solver smoke tests:

```sh
make test-smoke
```

Run only benchmarks:

```sh
make benchmark
```

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
- `ARTIFACT_TIMEOUT=<seconds>`: timeout applied separately to each case; the
  default is `3600` (`120` with `FAST=1`).
- `ARTIFACT_OUTPUT=<directory>`: output log directory; the default is
  `artifact-logs`.
- `PYTHON=<executable>`: Python interpreter used to run the test scripts; the
  default is `python3`.

Examples:

```sh
make test ARTIFACT_JOBS=2 ARTIFACT_TIMEOUT=1800
make benchmark ARTIFACT_SCOPE=car-linear ARTIFACT_JOBS=3
make test FAST=1 ARTIFACT_SCOPE=wat-linear ARTIFACT_JOBS=2
make benchmark ARTIFACT_OUTPUT=/tmp/stlmc-logs
```

The benchmark runner uses the installed `stlmc` command. Set `STLMC` to use a
specific executable. Both the smoke and benchmark runners use
`3rd_party/dReal3/dReal` by default; set `STLMC_DREAL` to override the dReal
executable path for both runners.

Pressing `Ctrl+C` cancels pending benchmark cases, terminates active `stlmc`
and solver processes, and exits with status `130`. Processes that do not stop
within five seconds are killed.

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
