# Solving strategies

STLmc separates discrete path exploration from continuous solving. The two
choices are independent and are composed by the model-checking algorithm.

## One-step and two-step solving

One-step solving sends the complete bounded encoding, including flow and
invariant constraints, directly to the selected solver.

Two-step solving implements the abstraction/refinement algorithm described in
the STLmc paper:

1. Replace flow and invariant conditions with Boolean variables to obtain a
   discrete abstraction.
2. Find a satisfying scenario in the abstraction.
3. Optionally minimize the scenario using an unsatisfiable core.
4. Restore the continuous flow and invariant conditions.
5. Check the refinement with the selected solver.
6. Block an unsatisfiable scenario and continue until a witness is found or
   the abstraction is exhausted.

Enable two-step solving with `-two-step`. Without it, STLmc uses one-step
solving.

The `concrete` option controls scenario generalization, not whether abstraction
is used. With `concrete = "false"` (the default), two-step solving minimizes
scenarios using unsatisfiable cores. With `-concrete`, it retains the complete
Boolean and discrete assignment.

## Symbolic and explicit paths

`path-strategy = "symbolic"` keeps mode and jump choices in the SMT encoding as
disjunctions. This is the default.

`path-strategy = "explicit"` enumerates exact hybrid-automaton transition paths
before continuous solving. A path records selected transitions, not only its
sequence of modes, so multiple jumps between the same modes remain distinct.
For normal STL model checking, explicit enumeration includes steady
transitions used for STL variable points. Reachability omits those steady
transitions.

Both path strategies support both solving engines:

| Path strategy | One-step | Two-step |
| --- | --- | --- |
| `symbolic` | Complete OR encoding | Abstract scenarios from the OR encoding |
| `explicit` | Directly check explicit paths | Abstract and refine within each explicit path |

The `reach` option changes query semantics only. It does not select a path or
continuous-solving strategy.

## Batching

`solver-batch-size` specifies the maximum number of final candidates combined
in one solver query. A batch is encoded as a disjunction. Identical common
constraints are factored when possible; otherwise STLmc preserves each complete
candidate branch.

For explicit one-step solving, candidates are transition paths. For two-step
solving, candidates are continuous refinements. A value of `1` checks candidates
individually.

```sh
stlmc system.model -path-strategy explicit -solver-batch-size 4
stlmc system.model -two-step -solver-batch-size 8
```

## Parallelism

`-parallel` runs two-step refinement checks concurrently. `parallel-core`
limits the number of solver workers. Parallelism controls simultaneous jobs,
whereas batching controls how many candidate branches are combined inside one
job.
