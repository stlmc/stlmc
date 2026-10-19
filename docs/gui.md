# GUI user guide

`stlmc-gui` provides a browser-based interface for editing models and
configurations, running analyses, and inspecting results. The GUI and CLI
use the same model parser and configuration defaults.

## Start the GUI

With STLmc installed in an active virtual environment, install the GUI, Z3,
and HTML visualization, then start the workspace:

```sh
stlmc-installer install --solver z3 --visualize html --ui
stlmc-gui
```

The browser opens at `http://127.0.0.1:8766/`. Paste the session token printed
in the terminal into **Session token** and click **Connect**. Keep the terminal
open. The page uses port 8766; the bridge API uses port 8765 and is not a web
page. These defaults can be changed with `--ui-port` and `--port`.

The GUI supports Linux, macOS, and WSL. Installing a wheel does not require
Ruby, Jekyll, or Node.js. For other solvers, source builds, authentication
options, and storage locations, see [installation](installation.md#browser-workspace).

## Open and edit files

Choose a **Local model**, then click **Load model**. Load its configuration
separately using **Local configuration → Load configuration**; opening a
model does not automatically open a matching configuration.

**Open model file / Open configuration** reads a file from the browser's
computer into the editor. **Save model / Save configuration** writes the
current buffer to the GUI server's model folder. **Download** saves a copy
on the browser's computer. Uploaded or edited buffers are not automatically
saved as server files. Choose a new filename to preserve an original model.

**Editor layout** switches between model-only, configuration-only, and
side-by-side views. Parser errors appear beside the editor and are marked
in the text; click a message to move to its location.

While connected, the GUI checks for file changes every two seconds. Clean
buffers reload after external edits; unsaved local edits are preserved with
a notice. Save conflicts require reloading or saving under a new name.

## Configure and run an analysis

The GUI reads goal labels from the model and settings from the configuration.
Configuration edits are applied automatically; there is no separate Apply
button. Only fields explicitly changed in **Analysis settings** override the
configuration. Reloading or opening a configuration resets those overrides.
Changing a form field does not rewrite the configuration editor's text.

- **Goal** selects a labeled goal; **All goals** selects every goal.
- **Final solver** defaults to `auto`, which checks installed backends and
  model support. It does not install a solver automatically.
- **Bound** limits the discrete STL partition, not just physical jumps.
- **Global time bound** limits modeled time, not computation time.
- **Robustness threshold** sets the STL robustness requirement and is
  distinct from dReal precision.
- **Reachability target** interprets an ordinary state goal as a reachability
  query. Leave it off for ordinary STL model checking.
- **Advanced options** contains two-step solving, explicit paths, and the
  wall-clock timeout, which defaults to 120 seconds and accepts up to 3600.

Supply bound and global time bound in the configuration or form. Solver-specific
settings and options without form fields, such as `parallel`, `parallel-core`,
`logic`, `precision`, and `time-horizon`, remain in the configuration.
`time-horizon` limits each continuous segment and is distinct from the global
time bound and wall-clock timeout.

Click **Run analysis** to use the current buffers; saving first is not
required. Later edits do not affect an analysis already running. Use
**Stop active analysis** to request cancellation. Disconnecting or closing
the page does not cancel a running analysis.

For a complete Z3 example, use the [README quick start](../README.md#quick-start):
open `quickstart.model`, select `safety`, and set both bounds to 2. It produces
a `violated` result. ODE examples may require dReal rather than Z3.

## Inspect and keep results

**Results** shows completed bounds, query timings, verification outcomes, and
downloadable files. **Visualization** displays generated counterexamples or
reachability witnesses. **Execution log** contains the solver output and
diagnostics. Failures and timeouts also produce a visible failure summary.
The summary distinguishes the wall-clock time limit, a user stop request,
and GUI server shutdown. A solver exit code alone does not identify the cause.

`violated` means a counterexample to the configured robustness requirement was
found. `satisfied up to bound k` applies only within the configured bounded
search, not all bounds or infinite time. Process completion is separate from
property satisfaction. See [result semantics](result-semantics.md) for details,
including dReal limitations and reconstructed plots.

**Run history** reopens earlier results without restoring their input into
the editors. **Clear finished history** permanently removes the listed
finished runs and their artifacts, but keeps model/configuration files and
active analyses. Download anything needed before clearing history.

## Connect to a remote server

Ask the administrator for an SSH account, page/API ports, and session token.
For a server using the default ports, forward both ports from your computer:

```sh
ssh -N -o ExitOnForwardFailure=yes \
  -L 127.0.0.1:8766:127.0.0.1:8766 \
  -L 127.0.0.1:8765:127.0.0.1:8765 USER@SERVER
```

Open `http://127.0.0.1:8766/` and connect with the administrator's token.
Keep the SSH terminal open. Use the same local and remote port numbers to
match the bridge's Host/Origin checks; coordinate any port changes with the
administrator. Models and solver runs now reside on that server, while
downloads go to your computer.

A GUI instance is a shared, single-user workspace, not an isolated multi-user
service. Coordinate access to files, analyses, and history. Separate users
should use separate instances and storage folders when isolation is needed.
Never share a session token publicly or include it in a URL.
