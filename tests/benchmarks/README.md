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

For STL, the expected bound counts both mode changes and STL partition points,
not just physical jumps. Propositions must retain their assigned truth value
throughout each open flow interval, and temporal changes must align with the
partition. A valid physical trace may therefore require additional partition
points before it is representable at a bounded query.

An expected bound must only be changed after checking the lower-bound UNSAT
results, the new SAT result, and the saved witness. A timeout is not an expected
logical result. For dReal, distinguish delta-SAT from an independently verified
exact trajectory; a failed strict witness check must not be hidden by changing
an expected status. The crossing regression in `scenario_core_integration.py`
and the shifted-endpoint regression in `temporal_reduction.py` protect these
partition requirements.

The `quick` selection follows `@benchmark.quick` annotations; release checks
give each selected case a 200-second timeout. `fast` and `quick` are distinct
selections and neither changes the expected logical result. The full and
fast sets currently retain invalid historical `bat-poly` inputs, which are
rejected by flow validation and reported as benchmark failures. Parser tests
separately verify the expected validation error. Quick release checks exclude
these inputs. See [Testing](../README.md) for prerequisites and selections.

Run every benchmark with `make benchmark`. Select one model with, for example,
`make benchmark ARTIFACT_SCOPE=rail-poly`.
