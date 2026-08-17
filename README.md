# STLmc

STLmc is an SMT-based bounded model checker for signal temporal logic (STL)
properties of hybrid systems. It supports linear, polynomial, and ODE dynamics
through Z3, Yices2, and dReal.

For the project website, publications, and full manual, visit
[stlmc.github.io](https://stlmc.github.io/).

## Features

- Robust bounded model checking of STL properties
- [Bounded reachability checking](docs/reachability.md)
- Direct one-step and abstraction-based two-step solving
- Symbolic and explicit transition-path exploration
- Sequential, batched, and parallel continuous refinement checks
- Counterexample and reachability-witness generation
- Counterexample and robustness visualization with `stlmc-vis`

## Requirements and installation

STLmc requires Python 3.8 or later. Install the released package with:

```sh
python -m pip install stlmc
```

Install the current checkout with:

```sh
python -m pip install .
```

For development, use an editable installation:

```sh
python -m pip install -e .
```

STLMC installs the Python interfaces for Z3 and Yices by default. Check all
solver prerequisites after installation with:

```sh
stlmc-install-solvers --check
```

Install all missing solver prerequisites where supported with:

```sh
stlmc-install-solvers
```

The default target is `all`; an individual solver can be selected with `z3`,
`yices`, or `dreal`, for example:

```sh
stlmc-install-solvers dreal
stlmc-install-solvers yices
```

Yices additionally requires its native library. Automatic Yices installation
uses the SRI package repository on Ubuntu/Debian and Homebrew on macOS, and may
request administrator privileges. On other Linux distributions, install the
Yices native library with the system package manager before running `--check`.

The installer downloads the dReal 3 executable to:

- macOS: `~/Library/Application Support/stlmc/solvers/dReal3/dReal`
- Linux: `$XDG_DATA_HOME/stlmc/solvers/dReal3/dReal` when `XDG_DATA_HOME` is
  set, otherwise `~/.local/share/stlmc/solvers/dReal3/dReal`

Automatic dReal installation supports macOS and x86-64 Linux. At runtime STLMC
searches for an executable named `dReal` in `PATH` first and then checks the
user solver directory above. A differently named or separately installed
executable can be selected with `-executable-path /path/to/dReal`.

If a solver required by the selected analysis is unavailable, STLMC reports
the corresponding installer command instead of failing with an import or
process traceback.

Confirm the installation and inspect every available option with:

```sh
stlmc -h
stlmc-vis -h
```

## Basic usage

An analysis requires a model, a discrete STL bound, and a global time bound.
For STL model checking, the discrete bound limits mode changes plus
variable points where an STL subformula changes truth value. For state
reachability it limits jumps. `time-horizon` limits the duration
of each continuous segment separated by a mode change or STL variable
point; it defaults to the global `time-bound`. These values may be supplied by
a model configuration file:

```sh
stlmc system.model -model-cfg system.cfg
```

or overridden on the command line:

```sh
stlmc system.model -bound 5 -time-bound 20 -solver dreal
```

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

See [Bounded reachability](docs/reachability.md) for its precise semantics.

## Solving strategies

One-step and two-step solving are independent of discrete path exploration.
The four supported combinations are:

```sh
# Complete symbolic encoding, solved directly
stlmc system.model -path-strategy symbolic

# Symbolic paths with abstraction/refinement
stlmc system.model -path-strategy symbolic -two-step

# Enumerate exact transition paths and solve each directly
stlmc system.model -path-strategy explicit

# Enumerate exact paths and apply two-step solving inside each path
stlmc system.model -path-strategy explicit -two-step
```

The default is symbolic one-step solving. `solver-batch-size` controls the
maximum number of final candidates combined in one solver OR query:

```sh
stlmc system.model -two-step -solver-batch-size 8
```

See [Solving strategies](docs/solving-strategies.md) for the abstraction, path,
batching, and parallelism relationships.

## Visualization

Pass `-visualize` to write a `.counterexample` file for a violated STL property
or a `.witness` file for a reachable target, together with its visualization
configuration. Render an artifact with:

```sh
stlmc-vis result.counterexample -cfg result.cfg
```

## Tests and benchmarks

Run the complete test and benchmark workflow with:

```sh
make test
```

For a faster development check:

```sh
make test FAST=1
```

See [tests/README.md](tests/README.md) for individual test targets, running one
benchmark formula, timeouts, batching, and benchmark output locations.

## License

STLmc is distributed under GPLv3.
