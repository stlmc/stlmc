# Reachability

STLMC treats a reachability bound as the maximum number of jumps.
Bound zero therefore checks the initial continuous segment, and bound `k`
checks paths containing at most `k` jumps. The search stops at the first bound
that contains a witness.

`time-horizon` limits the duration of each continuous segment. Reachability
segments are separated by jumps.

## Writing a query

A model can declare a reach target directly:

```text
goal:
    reach (and (temperature >= 70) (alarm = true));
```

Alternatively, `-reach` interprets a selected ordinary state goal as a reach
target:

```sh
stlmc system.model -goal f1 -reach
```

A reach target must be a state formula. STL temporal operators such as `<>`,
`[]`, `U`, and `R` are rejected because they describe traces rather than a
set of target states.

## Semantics

For every bound, STLMC asks whether a valid hybrid execution contains a state
that satisfies the target. A state may occur at the beginning or end of any
continuous segment. Segment durations are symbolic, so an endpoint can be
placed at an interior time of a flow; the target is not restricted to a fixed
sampling grid.

The configured `threshold` is applied to the reach target as a delta
relaxation. For example, with threshold `0.1`, `x >= 5` is checked as
`x >= 4.9`. This is the same robust relaxation convention used during normal
model checking.

Reachability uses the regular one-step or two-step BMC engine selected by
`two-step`. It supports Z3, Yices, and dReal subject to each solver's formula
capabilities described in [Solver formula support](solver-formula-support.md).

The `path-strategy` option is independent of `two-step`. `symbolic` keeps all
mode and jump choices in the encoding, while `explicit` enumerates exact
transition paths first. Either path strategy can use direct one-step solving or
the two-step abstraction/refinement algorithm.

## Results and witnesses

The final status is one of:

- `reachable at bound k`: a witness was found with `k` jumps;
- `unreachable up to bound k`: no witness exists within the checked bounds;
- `unknown up to bound k`: a solver could not decide one of the checks.

With result generation enabled (`visualize = "true"` or `-visualize`), a
reachable query writes a `.witness` assignment and its visualization `.cfg`.
Normal model checking continues to use the `.counterexample` suffix.
