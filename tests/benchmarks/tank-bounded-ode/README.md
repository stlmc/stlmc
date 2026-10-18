# Bounded tank ODE benchmark

This independent fixture retains the reported tank ODE, initial set, and
two original formulas with temporal intervals `[0, 400]`. The existing
`tank-ode` benchmark is a separate fixture.

The state bounds are `[1.8, 3.5]` for both water levels. They contain the
original initial set `[1.8, 2.2]` for each level. Write
`a = 0.015 * sqrt(2 * 9.81)`, so `a² = 0.0044145`. At `x1 = 1.8`, its
derivative is at least `0.105 - a * sqrt(1.8) > 0`, since
`0.105² = 0.011025 > a² * 1.8 = 0.0079461`. At `x1 = 3.5`, it is at most
`0.122 - a * sqrt(3.5) < 0`, since
`0.122² = 0.014884 < a² * 3.5 = 0.01545075`.
On the `x2` boundaries, `sqrt(x1) - sqrt(x2)` has the inward sign.
Thus these state bounds preserve the original trajectories from that initial
set rather than clipping them.

The common configuration uses a 400-second window, discrete bound `1`,
threshold `0.0001`, and two-step dReal solving with precision `0.000001`.
It uses dReal's default ODE step control; it does not inherit the explicit
`0.01` step from `bouncing-ball-ode`.
dReal's delta-SAT result and numerical trajectory checks do not constitute an
exact trajectory certificate.

| Goal | Time window | Discrete bound | Registered result and finishing bound |
| --- | --- | --- | --- |
| `f1` | 400 seconds | 1 | `violated:1` |
| `f2` | 1 second | 0 | `violated:0` |

`f2` retains its original formula but uses a shorter analysis window for the
fast regression. Its result describes that finite query, not a claim that
the tank never reaches the target during the original 400-second interval.
Both goals are included in quick and fast selections. As with other
benchmarks, the standard runner compares the result and bound with annotations:

```sh
python tests/run_artifact_benchmarks.py --scope tank-bounded-ode --quick --timeout 60 --parallel-core 8
```
