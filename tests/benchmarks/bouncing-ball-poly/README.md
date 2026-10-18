# Bouncing-ball polynomial benchmark

This fixture retains the response model's closed-form dynamics, initial state,
and five STL goals. It uses gravity `1`, initial height `10`, initial velocity
`0`, and restitution `0.75`. It is distinct from the gravity `9.81`, initial
velocity `1` model in `bouncing-ball-ode`.

The fast configuration uses a one-second analysis window, threshold `0.01`,
and two-step dReal solving with precision `0.000001`. This window ends before
the first impact, so it does not exercise a bounce. Infinite temporal intervals
in the original formulas are still checked only within the finite analysis
window.

| Goal | Discrete bound | Registered result and finishing bound |
| --- | --- | --- |
| `f1` | 1 | `satisfied:1` |
| `f2` | 1 | `violated:1` |
| `f3` | 0 | `violated:0` |
| `f4` | 1 | `violated:1` |
| `f5` | 0 | `violated:0` |

All five goals are included in quick and fast selections. `satisfied:1`
records the absence of a counterexample within this time window, discrete
bound, and threshold; it is not an unbounded proof. Results use the configured
threshold semantics, including strengthening `x >= 10` to `x >= 10.01`.
The listed finishing bounds are observed encoding results.

```sh
python tests/run_artifact_benchmarks.py --scope bouncing-ball-poly --quick --timeout 60 --parallel-core 8
```
