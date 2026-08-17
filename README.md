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

STLmc requires Python 3.8 or later. Install the current checkout with:

```sh
python -m pip install .
```

For development, use an editable installation:

```sh
python -m pip install -e .
```

Confirm the installation and inspect every available option with:

```sh
stlmc -h
stlmc-vis -h
```

## Basic usage

An analysis requires a model, a maximum discrete-jump bound, and a global time
bound. These values may be supplied by a model configuration file:

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
