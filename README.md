# STLmc

STLmc is an SMT-based bounded model checker for signal temporal logic (STL)
properties of hybrid systems. It supports linear, polynomial, and ODE dynamics
using cvc5, Z3, Yices2, or dReal 3, subject to each solver's
[formula capabilities](https://github.com/stlmc/stlmc/blob/main/docs/solver-formula-support.md).

For the project website, publications, and user manual, visit
[stlmc.github.io](https://stlmc.github.io/).

## Features

- Robust bounded model checking of STL properties
- [Bounded reachability checking](https://github.com/stlmc/stlmc/blob/main/docs/reachability.md)
- One-step and abstraction-based two-step solving
- Symbolic and explicit transition-path exploration
- Sequential, batched, and parallel continuous refinement checks
- Counterexample and reachability-witness generation
- Counterexample and robustness visualization with `stlmc-vis`

## Requirements and installation

STLmc supports CPython 3.8 through 3.14. The visualization installer's validated
dependency profile currently covers only CPython 3.10; its visualization checks
and installs report an error on other Python versions. A virtual environment is recommended:

```sh
python -m venv .venv
# Linux/macOS; on Windows use .venv\Scripts\activate
. .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install stlmc
```

To install from source instead:

```sh
git clone https://github.com/stlmc/stlmc.git
cd stlmc
python -m pip install .
```

The default package includes NumPy and SciPy but no SMT solver bindings,
native solvers, Bokeh, or Matplotlib. Install Z3 for the quick start and
STLmc's default internal reasoning:

```sh
stlmc-installer install --solver z3
stlmc-installer check --solver z3
```

The default internal backend still needs Z3 when CVC5, Yices, or dReal is
selected as the final solver. Install the additional backends your models
need, for example:

```sh
stlmc-installer install --solver cvc5
stlmc-installer install --solver yices
stlmc-installer install --solver dreal
```

`stlmc-installer install --solver z3 cvc5 yices` installs the supported missing
solver prerequisites. The installer manages Python bindings and the required
native libraries for these backends.
Choose the `install` or `check` action first; running the installer without an
action shows help. Select multiple backends with `--solver z3 cvc5 yices dreal`
or formats with `--visualize html pdf text`. `install --all` selects all
components, including the official dReal 3.16.06.02 binary on supported
platforms. `check` alone checks all components without installing anything.

General ODE and transcendental models require a compatible dReal 3 build.
The default dReal download is the official 3.16.06.02 release, which has known
ODE bugs. Installation success checks its version and a basic algebraic query;
it does not establish ODE correctness. `check` and verification warn about this
official release's known invariant limitation and allow execution; unrelated
executable errors and failed capability checks remain errors. A successful
check does not certify ODE correctness. An alternative executable can be
selected with `-executable-path /path/to/dReal`. The advanced
[experimental source-build route](https://github.com/stlmc/stlmc/blob/main/docs/installation.md#dreal-source-builds)
requires explicit `--experimental-build` and is separate from the official binary.
See
[Installation and troubleshooting](https://github.com/stlmc/stlmc/blob/main/docs/installation.md)
for platform restrictions, Homebrew setup, solver locations, and offline use.

Confirm the installation and inspect the supported command-line options with:

```sh
stlmc -h
stlmc-vis -h
```

## Quick start

Save this complete model as `quickstart.model`. The state follows `x(t) = t`
from `x(0) = 0`, so the safety property is violated within two time units.

```text
[0, 10] x;
{
    mode: true;
    inv: x <= 10;
    flow: x(t) = x(0) + t;
    jump:
}
init: x = 0;
proposition:
goal:
[safety]: [][0, 2] (x <= 1);
```

Run it using Z3, with no native Yices or dReal installation needed:

```sh
stlmc quickstart.model -goal safety -bound 2 -time-bound 2 -solver z3 -visualize
```

The expected status is `violated`. The bound counts STL variable points as
well as mode changes, even though this example has no physical jump.
With `-visualize`, the result also lists the generated artifact and its `.cfg`
file. Use those paths with `stlmc-vis` as shown below.

## Analysis configuration

An analysis requires a model, a discrete STL bound, and a global time bound.
For STL model checking, the discrete bound limits mode changes plus
variable points where an STL subformula changes truth value. For state
reachability it limits jumps. For every solver, `time-horizon` limits the duration
of each continuous segment separated by a mode change or STL variable
point; it defaults to the global `time-bound`. These are modeled time limits,
not wall-clock execution timeouts. Values may be supplied by
a model configuration file:

```sh
stlmc system.model -model-cfg system.cfg
```

or overridden on the command line:

```sh
stlmc system.model -bound 5 -time-bound 20 -solver dreal
```

The default `-solver auto` checks model and selected-goal support and probes
installed backends in the order Z3, CVC5, Yices, then dReal. General ODEs and
dReal-only arithmetic require dReal. A candidate must pass an isolated runtime
check, including any required native capabilities. If no candidate is usable,
STLmc reports the reasons and exits; it does not install dependencies or retry
after an inconclusive verification. An explicit choice such as `-solver z3`
never falls back to another backend. Internal scenario/core dependencies are
checked separately.

Use `-goal` to select a labeled goal:

```sh
stlmc system.model -goal safety -bound 5 -time-bound 20
```

For ordinary STL model checking, STLmc searches for a behavior satisfying the
relaxed negation of the property. A satisfiable query therefore produces a
counterexample and reports `violated`. For reachability, STLmc checks the
relaxed target formula without negating it; a satisfiable query produces a
witness and reports `reachable`.

A model may declare a `reach` goal directly, or an ordinary state goal can be
interpreted as a reachability target with:

```sh
stlmc system.model -goal target -reach
```

See [Bounded reachability](https://github.com/stlmc/stlmc/blob/main/docs/reachability.md)
for its precise semantics.

## Interpreting results

- `violated`: a counterexample to the configured robustness requirement was
  found. With a positive `threshold`, this need not be a Boolean violation:
  a trace can have positive STL robustness but still lie below the threshold.
- `satisfied up to bound k`: no counterexample was found within the checked
  bounds. This is not a proof over all partition bounds or infinite time.
  Operators using `inf` are still analyzed within the configured finite time
  bound. The result does not independently certify that the bounded model has
  a feasible execution; overly restrictive ranges or invariants can exclude
  the physical behavior of interest.
- `reachable` / `unreachable up to bound k`: the corresponding bounded
  reachability search found a witness / exhausted the checked bounds.
- `unknown`: a solver check was inconclusive; do not interpret it as success.

`threshold` specifies the STL robustness requirement. dReal's `precision`
controls its delta-decision tolerance and is a separate setting. dReal results
and saved trajectories require care when exact guarantees are needed; see
[Result semantics and limitations](https://github.com/stlmc/stlmc/blob/main/docs/result-semantics.md).

## Solving strategies

The default is symbolic one-step solving: one complete bounded encoding is
sent to the solver. To use two-step abstraction/refinement and concurrent
refinement checks, for example:

```sh
stlmc quickstart.model -goal safety -bound 2 -time-bound 2 -solver z3 \
    -two-step -parallel -parallel-core 4
```

`-path-strategy explicit` instead enumerates exact transition paths and can
be combined with either engine. `solver-batch-size` controls how many final
candidates are combined in one OR query; it defaults to `1`.

With `-two-step -parallel`, scenario generation and unsat-core minimization
remain sequential, while completed refinement batches are checked concurrently
by solver workers. `parallel-core` limits those workers and defaults to `auto`,
which uses all logical CPUs reported by the host. Batching and
parallelism therefore have different effects: a larger batch reduces the
number of solver jobs and can reduce available parallelism. Start with batch
size `1` when solver utilization is the priority, then try `2` or `4` to trade
some parallelism for fewer solver invocations.

Parallel refinement with Yices requires a thread-safe native Yices build,
even with one worker. Otherwise, use sequential execution. See
[Yices source builds](https://github.com/stlmc/stlmc/blob/main/docs/installation.md#yices-source-builds)
for installation and capability checks.

See [Solving strategies](https://github.com/stlmc/stlmc/blob/main/docs/solving-strategies.md)
for path exploration, batching, parallelism, and live progress fields.

Pressing `Ctrl+C` requests cancellation. STLmc stops at safe checkpoints and
cleans up solver workers; a long native solver call may delay cancellation.

## Visualization

Pass `-visualize` to write a `.counterexample` file for a violated STL property
or a `.witness` file for a reachable target, together with its visualization
configuration. Writing these artifacts does not require Bokeh. HTML rendering
uses optional Bokeh; install it with `stlmc-installer install --visualize html`.
Render an artifact with:

```sh
stlmc-vis result.counterexample -cfg result.cfg
stlmc-vis result.counterexample -cfg result.cfg -output text
```

The same command accepts `.witness` files. HTML is the default. Text output
does not need either renderer; PDF output uses optional Matplotlib with a
headless backend and does not need Bokeh or external plotting tools.
Graphs show reconstructed trajectories and sampled robustness. Text reports
list model information and per-segment endpoint data.
Check the PDF dependency with
`stlmc-installer check --visualize pdf`, or install it with
`stlmc-installer install --visualize pdf`.

`.counterexample` and `.witness` files contain versioned, gzip-compressed JSON;
their extensions stay unchanged. The reader validates the format and bounds
decompression size before decoding the stored expressions.

Legacy pickle artifacts are outdated and unsupported. Rerun model checking
with the current STLmc version to regenerate them; no conversion is provided.

## Development and tests

From a source checkout, install in editable mode and run unit/integration checks:

```sh
python -m pip install -e .
stlmc-installer install --solver z3 cvc5 yices
stlmc-installer check --solver dreal
make test-unit
```

To also run solver smoke checks and a selected benchmark/comparison sample:

```sh
make test-quick
```

The full benchmark workflow is `make test`; it can take hours. See the testing
guide for prerequisites and known limitations.

See [Testing and benchmarks](https://github.com/stlmc/stlmc/blob/main/tests/README.md)
for prerequisites, test targets, selections, and output locations, and
[Architecture](https://github.com/stlmc/stlmc/blob/main/docs/architecture.md)
for contributor-facing implementation details.

## Support and citation

Report issues through [GitHub Issues](https://github.com/stlmc/stlmc/issues).
Include the STLmc version, OS/Python/solver versions, exact command, minimal
model and configuration, and relevant text logs. Remove sensitive model data
and do not attach secrets.

If you use STLmc in research, please cite Geunyeol Yu, Jia Lee, and Kyungmin
Bae, *STLmc: Robust STL Model Checking of Hybrid Systems Using SMT*, CAV 2022,
pp. 524–537. [DOI: 10.1007/978-3-031-13185-1_26](https://doi.org/10.1007/978-3-031-13185-1_26).

## License

STLmc is distributed under [GPLv3](https://github.com/stlmc/stlmc/blob/main/LICENSE).
