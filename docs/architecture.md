# Architecture

STLmc separates transport, application orchestration, domain encoding, and
solver infrastructure. Dependencies point inward from the CLI and adapters to
the application workflow; encoding code does not parse command-line options or
format final user output.

```text
CLI
  CliCommand ── layered configuration loading
      │
      ▼
Application
  VerificationWorkflow
      ├── RunPreparer ── model loading, validation, solver/algorithm selection
      └── GoalExecutor ── goal execution, outcome reporting, artifacts
              │
              ▼
Domain and encoding
  Model / Goal / Formula AST
  OneStepAlgorithm / TwoStepAlgorithm / PathProvider
              │
              ▼
Infrastructure
  JobSolver / SolverJob / sequential and parallel runners
  ProgressTracker / worker cleanup policy
  CVC5 / Z3 / Yices / dReal adapters
```

## Boundary types

`RunOptions` is the immutable, typed view of the parser's layered
`Configuration`. Parsing and backward-compatible string storage stop at this
boundary. Algorithms consume typed bounds, thresholds, flags, and worker
counts. Direct encoding is the default: after the paper's
`not(phi^+epsilon)` robust-to-Boolean reduction, the counterexample formula
enters the fully-stable encoding without a unary-temporal rewrite. The hidden
development option `use_unary_bounded_temporal_form` defaults to `False`.
Setting it to `True` first converts bounded temporal operators to an equivalent
unary form. This input-form selection is the only branch; subformula
collection, partition construction,
STL/model encoding, solving, and counterexample reporting remain shared. Both
forms describe the same continuous-time counterexample set, but they need not
find a witness at the same fully-stable partition bound, and an SMT solver may
select different trajectories from that set.

`SolverStatus` represents `SAT`, `UNSAT`, and `UNKNOWN`. Solver adapters retain
their historical `SolveResult.result` string for external compatibility, while
internal execution uses `SolveResult.status`.

`SearchStatus` represents the result of bounded exploration without conflating
it with property truth: a witness was found, the bounded space was exhausted,
or the search was inconclusive. `VerificationOutcome` translates that result
to `violated`/`satisfied` or `reachable`/`unreachable` at the presentation
boundary.

Execution progress and worker lifecycle are separate from result evaluation.
`ProgressTracker` accounts for scenarios and jobs in their respective units,
while `execution.cleanup` owns graceful termination, the shared cleanup
deadline, forced termination, and worker reaping.

## Compatibility

The old driver classes and import facades remain adapters only. The executable
uses `CliCommand` and `VerificationWorkflow` directly. New application code
should depend on `stlmc.application`, not `stlmc.driver` or compatibility
modules under `stlmc.objects` and `stlmc.encoding`.

## Parser development

The model, configuration, and visualization languages use Lark grammars under
`src/stlmc/parser/grammars/`. There is no generated parser source or Java
build step. Install the checkout in editable mode when developing parsers,
and run `make test-parser` and `make test-unit` after changes.

## Workspace frontend development

The CLI and workspace share `application.configuration.load_configuration`;
default and model configuration precedence is not reimplemented in JavaScript.
The authenticated `/api/inspect` endpoint adapts the common inspection API to
the browser. Model/configuration text uses the same visitors and diagnostics
as file input. Forms display these parsed values and submit only explicit edits.

`src/stlmc/ui/frontend/` is the editable frontend source: Jekyll layouts and includes define
the panels, SCSS defines their styling, and native JavaScript modules handle
interaction with the authenticated local API. The homepage and local GUI use
the same generated assets.

The model and configuration editors use CodeMirror 6 (MIT). The pinned,
self-contained bundle is checked in at `frontend/js/codemirror.js`, including
dependency license notices. Only updating this bundle needs Node.js;
see [editor build instructions](../tools/ui-editor/README.md). Normal wheel
builds use the existing bundle. Syntax colors are presentation only; parser
diagnostics still come from STLmc through `/api/inspect`.

After installing the locked development gems with `bundle install` in
`src/stlmc/ui/frontend/`, run from the repository root:

```sh
python tools/build_ui.py
python tools/build_ui.py --check
```

Commit only the frontend sources. `src/stlmc/ui/static/` is generated and
ignored by Git; do not edit it directly. Wheel builds regenerate it with
Jekyll automatically. For editable development, run the command above before
starting the GUI. Building from source requires Ruby, Bundler, and the locked
gems. The release workflow publishes only a wheel, which contains the static
assets but excludes the Jekyll source directory.
End users need only the optional Python UI dependencies; Node.js is not
required for building or running this frontend.

The optional JavaScript development tests run with Node.js 24:

```sh
node --test tests/ui_frontend.mjs
```

## Native solver development

### dReal ARM64 porting

Native arm64 builds have not been validated for this package. The
[dReal 3 build configuration](https://github.com/dreal/dreal3/blob/v3.16.06.02/src/CMakeLists.txt#L32)
unconditionally enables x86 SSE compiler flags and uses interval-arithmetic
dependencies. Native support requires porting and interval-rounding regression
checks, not merely a CMake architecture option. dReal 4 is not a drop-in ODE
replacement: the [official download page](https://dreal.github.io/download/)
states that dReach support is available only in dReal 3.

The legacy CAPD dependency also needs changes: its
[architecture detection](https://github.com/dreal-deps/capdDynSys-4.0/blob/edc1d8c8edf68af4cac4911f448738bbb6ac9bd3/capdAux/include/capd/settings/archSetting.h#L68)
classifies Apple targets as PowerPC, selecting PowerPC rounding instructions
instead of an arm64 implementation. Removing the SSE flags alone is insufficient.

Current [CAPD ARM64 rounding code](https://github.com/CAPDGroup/CAPD/blob/37057e5899bccaa6cd5701057b7e6ea5e232ef8b/capdAlg/src/capd/rounding/DoubleRounding.cpp#L149)
provides a potential porting path. Updating CAPD or backporting its architecture
and rounding support still requires dReal integration tests and numerical
validation; neither is a validated native STLmc solver installation yet.

The supported installation route and user alternatives are described in
[dReal on Apple Silicon](installation.md#dreal-on-apple-silicon).
