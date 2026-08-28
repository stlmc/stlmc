# Solving strategies

STLmc separates discrete path exploration from continuous solving. The two
choices are independent and are composed by the model-checking algorithm.

For STL model checking, `bound` limits the combined number of mode changes and
STL variable points. A variable point splits a continuous trajectory when a
subformula changes truth value. `time-horizon` limits the duration of every
continuous segment separated by a mode change or variable point. For a state
reachability query there are no STL variable points, so `bound` limits jumps.

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

If `N` candidates are generated and the batch size is `B`, STLmc creates at
most

```text
ceil(N / B)
```

solver jobs. The last job may contain fewer than `B` candidates. Increasing the
batch size reduces solver startup and repeated common constraints, but it also
reduces the number of jobs available for concurrent execution. Batch size does
not assign `B` candidates to each CPU core; it combines `B` candidates into one
query handled by one solver worker.

```sh
stlmc system.model -path-strategy explicit -solver-batch-size 4
stlmc system.model -two-step -solver-batch-size 8
```

## Parallelism

`-parallel` runs two-step refinement checks concurrently. `parallel-core`
limits the number of solver workers. Parallelism controls simultaneous jobs,
whereas batching controls how many candidate branches are combined inside one
job.

Parallel execution applies to the final solver-refinement stage of the
two-step algorithm. The current scenario producer remains sequential because
each new Z3 scenario is generated after adding a blocking clause for the
previous scenario. Unsat-core minimization is part of this sequential producer
stage. The execution pipeline is therefore:

```text
sequential Z3 scenario generation
    -> collect B candidates
    -> submit one OR query
    -> concurrent solver workers
```

For `N` generated candidates, batch size `B`, and `C` configured cores, the
theoretical worker limit is

```text
min(C, ceil(N / B)).
```

This is an upper bound, not a guaranteed utilization level. Batches are
submitted incrementally as scenarios are generated. If scenario generation is
slower than the final solver checks, workers may finish before the next batch
is ready and only one or two cores may be active. For example, 70 scenarios
with batch size 5 produce 14 solver jobs, so `parallel-core = 25` can use at
most 14 workers; it may use fewer when the scenario producer is the bottleneck.

Recommended starting points are:

- use batch size `1` when maximum solver parallelism is the priority;
- try `2` or `4` to reduce solver invocations while retaining several jobs;
- use larger batches when solver startup or duplicated common constraints cost
  more than the lost parallelism.

With `path-strategy = "explicit"`, STLmc waits for the batches belonging to one
explicit path before advancing to the next path. Batches within a path may run
concurrently, but different explicit paths are not currently produced in
parallel. One-step solving batches explicit paths but checks those batches
sequentially; `-parallel` affects two-step refinement checks.

## Live progress

When standard output is an interactive terminal, two-step solving updates one
temporary Bound checks line in place:

```text
bound=2  generated=4240  submitted=4235  completed=4210  pending=25  jobs=842/847  active=5
```

- `generated`: scenarios produced by the sequential Z3 stage;
- `submitted`: scenarios included in solver jobs;
- `completed`: scenarios in solver jobs that have finished;
- `pending`: submitted scenarios whose jobs have not finished;
- `jobs=completed/submitted`: completed and submitted solver-batch counts;
- `active`: solver workers currently running.

Scenario counts and job counts use separate units. For example, completion of
one full batch of size 5 increments `completed` by 5 and the completed job count
by 1. A partial final batch increments the scenario count by its actual size.

The live line is emitted only for a TTY and is overwritten as work progresses.
Redirected or captured output contains the final per-bound summary instead.
The final summary keeps the compact `bound`, `scenarios`, `query`, and `time`
fields; verbose mode additionally includes constraint size.
