# STLmc artifact benchmarks

This directory contains the benchmark models and configuration files from the
CAV 2022 STLmc artifact. Each model directory is placed directly below this
directory:

```text
benchmarks/
  <model>-<dynamics>/
    <model>.model
    <model>.cfg
    <model>-f1.cfg
    <model>-f2.cfg
    <model>-f3.cfg
```

The model basename matches the model prefix in the directory name. Expected
results are stored in each model file using this annotation:

```text
# @benchmark.expected(f1=violated:5, f2=satisfied:10, f3=violated:4)
# @benchmark.expected(f1=satisfied:0, reach=reachable:0)
# @benchmark.fast(f1, f2, f3)
# @benchmark.quick(f1, f2)
```

The annotation label matches the suffix of its goal-specific configuration
file. Reachability cases use `reachable` or `unreachable` as their status.

For STL, the expected bound is the first bound found by the current direct
encoding with fully stable partitions. It counts both mode changes and STL
partition points, not just physical jumps. Requiring a proposition to be true
or false throughout each open flow interval can require extra partition
points compared with older encodings. `Psi_PAR` also requires shifted temporal
change points to be partition endpoints. Equivalent-form rewriting is an
internal alternative and is not required to preserve the same bounded
partition size.

An expected bound must only be changed after checking the lower-bound UNSAT
results, the new SAT result, and the saved witness. A timeout is not an expected
logical result. For dReal, distinguish delta-SAT from an independently verified
exact trajectory; a failed strict witness check must not be hidden by changing
an expected status. The crossing regression in `scenario_core_integration.py`
and the shifted-endpoint regression in `temporal_reduction.py` protect these
partition requirements.

The `quick` selection records chosen cases whose reference
`logs/artifact-logs` run completed within 50 seconds, excluding `car-ode` and
`bat-poly`, and `car-poly`; release CI gives each one a 200-second timeout.

Run every benchmark with `make benchmark`. Select one model with, for example,
`make benchmark ARTIFACT_SCOPE=rail-poly`.
