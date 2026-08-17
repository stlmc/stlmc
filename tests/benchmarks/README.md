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
The `quick` selection records chosen cases whose reference
`logs/artifact-logs` run completed within 50 seconds, excluding `car-ode` and
`bat-poly`, and `car-poly`; release CI gives each one a 200-second timeout.

Run every benchmark with `make benchmark`. Select one model with, for example,
`make benchmark ARTIFACT_SCOPE=rail-poly`.
