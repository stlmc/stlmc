# Result semantics and limitations

## Bounds are part of the question

STLmc performs bounded exploration. For STL queries, `bound` counts mode
changes and STL variable points, not just physical jumps. A variable point
splits a flow to represent a change in a temporal subformula's truth value.
An otherwise valid physical trace may require a larger partition bound before
the encoding can represent it. Reachability bounds count jumps instead.

`time-bound` is the modeled global time limit. `time-horizon` limits each
continuous segment and defaults to `time-bound`. Neither is a wall-clock
timeout. Unbounded temporal intervals such as `[0, inf)` are evaluated within
the configured finite analysis window, not over an infinite execution.

## Robustness versus Boolean truth

The normal STL query searches for the relaxed negation of the selected
property, using the configured `threshold`. Thus a reported `violated` result
is a counterexample to the requested robustness requirement. With a positive
threshold, it need not be a Boolean violation: positive robustness can still
be below the required margin.

For example, a trace with robustness `0.2` can meet the Boolean property but
fail a requested robustness threshold of `1`. Specify and report the threshold
when interpreting or comparing results. Numerical artifact inspection uses
the condition `rho(phi, 0) <= threshold`; it is not an independent exact proof
of that inequality for an ODE execution.

`satisfied up to bound k` means the bounded counterexample search was exhausted.
It is not an unbounded safety proof. The precise guarantee is conditional on
the encoded model, bounds, solver semantics, and robustness relaxation; do not
infer a strict robustness inequality exactly at a relaxation boundary.

For a state reachability query, `reachable` means a witness to the relaxed
target was found; `unreachable up to bound k` means no witness was found within
the checked bounds. See [Reachability](reachability.md).

`unknown` is inconclusive. An externally cancelled or timed-out run is also
inconclusive and must not be treated as `satisfied` or `unreachable`.

## Model validity and feasibility

All results refer to the model supplied, including variable ranges, initial
conditions, invariants, and resets. A no-counterexample result does not
independently prove that a relevant physical execution exists. For example,
excluding negative velocity from a falling-object model can eliminate its
descending behavior rather than verify a physical safety claim.

Closed-form flows use local elapsed time and the segment's initial state.
They must describe the intended dynamics when a flow is split at STL variable
points. In particular, check `F(0,x)=x` and consistency under restarting a
flow. The parser rejects detected constant initial-value contradictions and
warns about some restart inconsistencies. Unsupported expressions may not be
diagnosed; absence of a warning is not a certificate of model correctness.
An approximation to an ODE is not automatically equivalent to the original
ODE and needs its own validity horizon and error justification.

## dReal results and saved artifacts

`threshold` is an STL robustness parameter. dReal's `precision` is a separate
delta-decision tolerance used by the backend. Reducing one does not change
the other, and delta-SAT is not a certificate that the exact, unrelaxed
constraints have a solution.

STLmc preserves dReal variable intervals and exposes their midpoints for
visualization. Choosing the midpoint independently for each variable does not
guarantee an exact trajectory: ODE consistency, initialization, resets, or
invariants can fail even when each coordinate lies within its reported box.
A nearby valid execution does not certify the original midpoint or interval
box either.

`stlmc-vis` and `tests/validate_artifacts.py` support inspection. The latter
checks that stored midpoints are inside their boxes and evaluates sampled
robustness. It does **not** certify every initial, jump, invariant, and flow
constraint, continuous-time robustness, or an exact solution inside the full
interval box. Independent exact or validated-numerical checking is needed
when a strict trajectory certificate is required.

Only load `.counterexample` and `.witness` files from trusted sources. They
are Python pickle data; loading an untrusted artifact can execute code.
