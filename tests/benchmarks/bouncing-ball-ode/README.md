# Bouncing-ball ODE benchmark

This fixture uses the reported ODE (`g=9.81`, restitution `0.75`, initial
height `10`, initial velocity `1`). The velocity range allows both signs.
The same `ball.model` contains the report's original STL formulas `f1` through
`f5` and the additional `rebound` reachability target.

The common `ball.cfg` selects a three-second window, discrete bound `4`,
threshold `0.01`, dReal precision `0.000001`, and ODE step `0.01`, with
two-step solving and parallel execution enabled. The three-second window
contains the first bounce and ends before the next impact, using the original
gravity and initial state.
Even the formulas with infinite temporal intervals are checked within this
finite analysis window; these runs do not establish their truth over unbounded
time. For STL, the discrete bound counts both mode changes and STL partition
points.

Each goal has a separate configuration. The fast regression settings and
registered expectations are:

| Goal | Time window | Discrete bound | Expected result and finishing bound |
| --- | --- | --- | --- |
| `f1` | 1 second | 1 | `satisfied:1` |
| `f2` | 1 second | 1 | `violated:1` |
| `f3` | 3 seconds | 4 | `violated:3` |
| `f4` | 1 second | 2 | `violated:2` |
| `f5` | 1 second | 0 | `violated:0` |
| `rebound` | 3 seconds | 1 | `reachable:1` |

All six goals are included in the quick and fast benchmark selections.
`f1`, `f2`, `f4`, and `f5` use shorter windows for fast regression checks;
`f3` and `rebound` retain the three-second window containing the first bounce.
`f5` is already violated by the initial height `x = 10`, so its regression
does not require a bounce.
The `rebound` configuration also sets threshold `0` and enables reachability
checking. The `f1` result means no counterexample was found within its
one-second window and discrete bound `1` at threshold `0.01`; it does not
establish the formula over unbounded time or all discrete bounds.

The `rebound` reachability target is `x >= 1 and v >= 5`, within three seconds.
Like the other benchmarks, these cases use the standard runner to compare
the reported result and finishing bound with the model's expected annotations.

From the repository root:

```sh
python tests/run_artifact_benchmarks.py --scope bouncing-ball-ode --quick --timeout 60 --parallel-core 4
```

To run one goal directly from the repository root, select its configuration:

```sh
stlmc tests/benchmarks/bouncing-ball-ode/ball.model -model-cfg tests/benchmarks/bouncing-ball-ode/ball.cfg -model-specific-cfg tests/benchmarks/bouncing-ball-ode/ball-f1.cfg
```

Replace `ball-f1.cfg` with `ball-f2.cfg`, `ball-f3.cfg`, `ball-f4.cfg`,
`ball-f5.cfg`, or `ball-rebound.cfg` for another goal. Each configuration
selects its goal and the settings in the table above.

For the benchmark runner, set `STLMC_DREAL=/path/to/dReal` when the executable
is outside its default test location. This is a test-runner setting, not a
general STLmc executable override. For a direct `stlmc` invocation, use normal
solver discovery or pass `-executable-path /path/to/dReal`.
