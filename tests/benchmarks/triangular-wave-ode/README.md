# Triangular-wave ODE benchmark

This fixture retains the reported two-mode ODE, initial set, and goal
`[][0, 10] (x > 2)`. The configuration retains a 60-second analysis window,
discrete bound `16`, threshold `0`, and one-step Yices solving with `QF_NRA`.
The registered result is `f1=violated:14`, included in quick and fast
selections. The finishing bound is the observed encoding bound, which counts
STL partition points as well as mode changes; it is not a physical jump count.

This is a finite-window regression using the standard model/configuration
to result/bound comparison. It does not establish unbounded behavior.

```sh
python tests/run_artifact_benchmarks.py --scope triangular-wave-ode --quick --timeout 60
```
