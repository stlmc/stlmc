# STLmc artifact benchmarks

This directory contains the benchmark models and configuration files from the
CAV 2022 STLmc artifact, together with additional regression cases. Each model
directory is placed directly below this directory:

```text
benchmarks/
  <model>-<dynamics>/
    <model>.model
    <model>.cfg
    <model>-f1.cfg
    <model>-f2.cfg
    <model>-f3.cfg
```

Configuration filenames share the `.model` basename, not necessarily the
directory name: for example, `bouncing-ball-ode/ball.model` uses `ball.cfg`
and `ball-f1.cfg`. Expected results are stored in each model file using this annotation:

```text
# @benchmark.expected(f1=violated:5, f2=satisfied:10, f3=violated:4)
# @benchmark.expected(f1=satisfied:0, reach=reachable:0)
# @benchmark.fast(f1, f2, f3)
# @benchmark.quick(f1, f2)
```

The annotation label matches the suffix of its goal-specific configuration
file, named `<model>-<goal>.cfg`. The goal can be `f1`, `f2`, or another label
such as `rebound`. Directories without goal-specific configurations are not
included in automated benchmark runs. Reachability cases use `reachable` or
`unreachable` as their status.

Selected artifact goals have been revised for short, bounded regression runs.
Their temporal intervals, and in some cases predicates or operator structure,
differ from the historical artifact. Results apply to the current `.model`
and goal-specific `.cfg`, not to the original verification scope. The table
summarizes these revised goals (`F` = eventually, `G` = always):

| Cases | Global `time-bound` | Current temporal scope |
| --- | --- | --- |
| `bat-ode/f3` | 10 | `G[0,1] F[0,0.2]` |
| `space-ode/f2` | 5 | `F[0,0.5] G[0,0.5]` |
| `bat-poly/f1,f2,f3` | 2 | G/F/U nesting retained; each local interval is `[0,1]` |
| `bat-linear/f1` | 1.5 | `F[0.5,1]` with `G[0,0.5]` |
| `bat-linear/f3` | 1 | `G[0,0.5]` with `F[0,0.5]` |
| `car-poly/f1` | 1 | `G[0,0.5]` with `F[0,0.5]` |
| `rail-poly/f1` | 2 | `F[0,1]` with `U[0,1]` |
| `rail-poly/f3` | 1 | `G[0,0.5]` with `U[0,0.5]` |
| `wat-poly/f2` | 4 | `F[2,3]` with `G[0,1]` |
| `nav-ode/f1,f3` | 1 | Nested F/G or F/R with `[0,0.25]` intervals |
| `nav-ode/f2` | 2 | `F[0.2,0.5] G[0.2,0.5]` |
| `oscil-ode/f1,f2,f3` | 1 | f1: F/R over `[0,0.25]`; f2: `G[0.5,1]`; f3: `G[0,1]` |
| `rail-ode/f2` | 1 | F/R over `[0,0.25]` |
| `thm-ode/f1` | 2 | `F[0,1]` with `U[0,1]` |
| `thm-ode/f2` | 1 | G/F over `[0,0.25]` |
| `thm-ode/f3` | 2 | `G[0.2,0.5]` with `R[0,0.5]` |
| `wat-ode/f3` | 1 | F/R over `[0,0.25]` |

Predicate revisions are explicit: `bat-linear/f1` changes its antecedent
from `d2 >= 4` to `d2 >= 0`; `nav-ode/f1` changes the consequent to
`y >= 90`, `nav-ode/f3` uses `x <= 20`, `oscil-ode/f1` uses `y <= -1`,
`rail-ode/f2` uses `vb <= 3`, and the right operand of `wat-ode/f3` is now
`x >= 5`. The oscillator f2/f3 goals are single-G regressions over `x2 >= 2`
and `x3 < 0.25`, respectively, rather than the original nested formulas.
Other predicates and physical dynamics are retained, except for the polynomial
battery correction below. The 11 revised ODE goals in navigation, oscillator,
rail f2, thermostat, and water f3 use `time-horizon = time-bound` and maximum
bound 5. This segment-limit setting also applies to `car-poly/f1`,
`rail-poly/f1`, and `rail-poly/f3` (violations at bounds 0, 1, and 0), and
`bat-linear/f1,f3` (violations at bound 0).

The current runner discovers 71 cases. Passing short-window cases is not
evidence that the original long-window goals hold. Polynomial flow-subdivision
warnings remain enabled.

`car-linear/f2` keeps its original model, formula, time window, and threshold,
but checks maximum bound 8, not the historical bound 20. Its `satisfied:8`
expectation includes the complete STL partition and proposition matching at
that reduced bound.

`car-linear/f3` retains its goal and global time window. Its expected
violation is now at bound 11 after correcting invariant identifiers across
multi-digit bounds; this counts STL partition points as well as mode changes.

For STL, the expected bound counts both mode changes and STL partition points,
not just physical jumps. Propositions must retain their assigned truth value
throughout each open flow interval, and temporal changes must align with the
partition. A valid physical trace may therefore require additional partition
points before it is representable at a bounded query.

The polynomial battery fixtures use a corrected model: the published
polynomials are interpreted as rates and integrated into cubic closed-form
flows. A mode-local clock resets on physical jumps and is preserved at STL
partition points. This avoids inconsistent initial offsets and dependence on
how a flow interval is subdivided. The corrected dynamics are not equivalent
to the historical model, and the main battery fixture's temporal windows are
also shortened for regression testing.

An expected bound must only be changed after checking the lower-bound UNSAT
results, the new SAT result, and the saved witness. A timeout is not an expected
logical result. For dReal, distinguish delta-SAT from an independently verified
exact trajectory; a failed strict witness check must not be hidden by changing
an expected status. The crossing regression in `scenario_core_integration.py`
and the shifted-endpoint regression in `temporal_reduction.py` protect these
partition requirements.

The `quick` selection currently contains 23 cases and follows
`@benchmark.quick` annotations; release checks give each selected case a
200-second timeout. Both bouncing-ball fixtures and `tank-bounded-ode/f1`
remain in full/fast selections but are excluded from quick checks. `fast` and `quick` are distinct
selections and neither changes the expected logical result. The full and
fast sets include research cases that may exceed the configured timeout;
timeouts remain failures, not logical results. Parser tests separately reject
invalid flow equations. See [Testing](../README.md) for prerequisites and
selections.

Run every benchmark with `make benchmark`. Select one model with, for example,
`make benchmark ARTIFACT_SCOPE=rail-poly`.
