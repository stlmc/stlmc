# Installation and troubleshooting

Install STLmc in a virtual environment with a current pip. The package
requires CPython 3.11 through 3.14 and provides `stlmc`, `stlmc-vis`,
`stlmc-installer`, and `stlmc-gui`.
The default installation includes NumPy and SciPy but no Bokeh, Matplotlib,
solver bindings, or native solvers.

```sh
python -m pip install stlmc
stlmc-installer install --solver z3
stlmc-installer check --solver z3
```

The default internal reasoning backend needs Z3 independently of the final
solver. Selecting CVC5, Yices, or dReal as the final solver does not remove
that default requirement. A missing required backend produces an installation
command instead of silently selecting a different solver.

Install additional backends as needed:

```sh
stlmc-installer install --solver cvc5
stlmc-installer install --solver yices
stlmc-installer install --solver dreal
stlmc-installer check --solver dreal
stlmc-installer check --solver z3 cvc5 yices dreal
```

Choose `install`, `check`, or `uninstall` before the component selectors. Both `--solver`
and `--visualize` accept multiple names, for example `install --solver z3 cvc5`
or `check --visualize html pdf text`. Running the installer without an action
shows help and does not install anything. `stlmc-installer install --all`
selects all components, including the official dReal binary on supported
platforms. `stlmc-installer check` checks all solvers, visualization formats,
and UI dependencies without installing. Use explicit selectors to check only
the components you need.
Managed downloads do not invoke an OS package manager or replace system
libraries. Python packages install into the current interpreter's environment.
Installing missing native dependencies or build tools separately may require
administrator privileges.

Package extras are not provided; use `stlmc-installer` for optional components.

## Visualization

The visualization installer targets CPython 3.11 through 3.14 with NumPy
2.3.5, SciPy 1.16.3, Bokeh 3.8.2, and Matplotlib 3.10.8. Visualization
`check` and `install` on other Python versions report an unsupported-profile
error (exit status 1).

Managed pip installs also apply the packaged
`stlmc/cli/dependency-constraints.txt` to pin Python transitive dependencies
for Linux/macOS. Constraints do not install unselected components and are
not a lock for system libraries, native build tools, or externally supplied
solver binaries. Existing environments are not globally rewritten.

Writing model-checker artifacts and rendering text do not require Bokeh.
HTML rendering requires optional Bokeh; PDF rendering uses optional Matplotlib
with a headless backend; it does not require Bokeh or an external plotting
executable. Saved artifacts can be
rendered without solver bindings. Select the format explicitly when checking
or installing its prerequisites:

```sh
stlmc-installer install --visualize html pdf
stlmc-installer check --visualize html pdf
stlmc-installer check --visualize text
```

Text and PDF checks require NumPy and SciPy but not Bokeh. Renderer
installation uses pip in the current Python environment and does not invoke
an OS package manager.

```sh
stlmc-vis result.counterexample -cfg result.cfg -output text
stlmc-vis result.counterexample -cfg result.cfg -output pdf
```

Result files use versioned, gzip-compressed JSON and retain the
`.counterexample` and `.witness` extensions. Legacy pickle files are outdated
and unsupported. Rerun model checking with the current STLmc version to
regenerate them; no conversion is provided.

## Browser workspace

The browser workspace and local bridge are included in STLmc; a separate
web-ui checkout is not required. The GUI supports Linux,
macOS, and WSL, not native Windows.

The GUI installed from a wheel does not require Ruby, Jekyll, or Node.js.
Building a wheel from source requires Ruby, Bundler, and the locked Jekyll
gems. For editable development, generate the UI with `python tools/build_ui.py`
before starting it; see [frontend development](architecture.md#workspace-frontend-development).

Install the optional server dependencies and start the GUI:

```sh
stlmc-installer install --ui
stlmc-installer check --ui
stlmc-gui
```

The local workspace detects the API address, including a custom `--port`.
Only the session token is required; the Bridge URL remains editable under
Advanced connection settings (also useful for the hosted Workspace).
Keep the terminal open and enter its session token in the workspace. By
default the page is served on `http://127.0.0.1:8766` and the authenticated API
on port 8765. Both bind only to loopback. Use `--no-browser` to avoid opening
a browser automatically, or `--allow-origin https://stlmc.github.io` to also
allow the homepage Workspace to connect. Do not share the token or allow an
untrusted origin. Browser local-network permissions may also be required.

Analysis form values override the loaded configuration for options shown in
the form. A blank Goal checks all goals, and unchecked Two-step and
Reachability controls explicitly disable those options. Options not exposed
in the form, such as dReal precision, remain controlled by the configuration.
Goals declared as reachability targets in the model retain that meaning.

Solvers and HTML/PDF renderers are installed separately. For example:

```sh
stlmc-installer install --solver z3 --visualize html
```

Models and results are stored outside the installed package, under
`$XDG_DATA_HOME/stlmc/ui/` on Linux (default `~/.local/share/stlmc/ui/`) or
`~/Library/Application Support/stlmc/ui/` on macOS, in `models/` and `runs/`.
Generated interactive plots load Bokeh JavaScript from `cdn.bokeh.org`, so
displaying them may require internet access even with a local workspace.
`stlmc-installer uninstall --ui` removes the optional
server packages, not saved models or results. `install --all` includes UI
dependencies. Use `stlmc-gui --help` for configurable ports.

## Platforms

`install --solver yices` downloads a SHA256-pinned archive from the official
Yices 2.7.0 release for Linux x86-64, macOS Intel, or macOS ARM64. It stages the
archive in a new user-owned directory and checks the shared library's version
and MCSAT support before activating it. Failure leaves the previous active
native installation unchanged. It does not run apt or Homebrew, modify system
libraries, or automatically build missing native dependencies.

On Linux x86-64 with glibc 2.29 or newer, the installer also obtains CUDD
3.0.0 from a SHA256-pinned [openSUSE Leap 15.6 binary RPM](https://download.opensuse.org/distribution/leap/15.6/repo/oss/x86_64/libcudd-3_0_0-0-3.0.0-bp156.4.4.x86_64.rpm). This dependency is an
openSUSE package, not an SRI-CSL Yices release artifact. Its shared library
is extracted into the managed user directory and loaded before Yices to
satisfy its `libcudd-3.0.0.so.0` dependency;
the RPM is not installed into the operating system. This route does not
compile CUDD, run package installation scripts, require sudo, or change
system libraries. The package's license is retained beside the managed library.
Other Linux architectures and older or non-glibc
systems are not covered by this managed dependency route.

The macOS archives require additional native dependencies; see
[Yices on macOS](#yices-on-macos) for minimum OS versions and CUDD requirements.
Unsupported platforms or failed native loading produce an error with alternatives;
source compilation remains an explicit `--build` option after installing its
prerequisites.

`install --solver dreal` downloads the official dReal **3** release
3.16.06.02 on Linux x86-64 and supported macOS systems. macOS uses the Intel
release; Apple Silicon requires Rosetta to be installed already. It verifies the pinned
archive hash, exact version, and a basic algebraic SAT query. These checks
establish installation, not ODE correctness: this release has known bugs,
including omitted invariants involving zero-derivative parameters.
`check --solver dreal` reports this official release's known invariant
limitation. A successful install or check does not certify ODE correctness.
Reinstalling the official release does not fix those bugs. An already
available compatible build is retained; an independently supplied dReal 3
build can be selected explicitly as described below. dReal 4 is not installed
as a replacement. Automatic native solver setup on Windows is not supported.
Python package support does not imply availability of every solver on every
OS/CPU combination. The release workflow covers Linux x86-64 and macOS Apple
Silicon; check its results for the release you intend to use.

### dReal on Apple Silicon

The managed download route uses the Intel dReal 3 release on both Intel Macs
and Apple Silicon. Apple Silicon requires an existing Rosetta installation;
the installer does not install Rosetta or other OS components automatically.
There is no native ARM64 release in this installation route.
[Apple documents general Rosetta availability through macOS 27](https://support.apple.com/en-us/102527);
starting with macOS 28, only a limited exception for certain older games remains.
See also [Apple's transition notice](https://developer.apple.com/news/?id=w5ngl9k2).
Rosetta is therefore not a long-term compatibility solution for this solver.

Native ARM64 dReal 3 builds are not supported by the installer. See
[dReal ARM64 porting](architecture.md#dreal-arm64-porting) for development
requirements. dReal 4 is not a drop-in ODE replacement: the
[official download page](https://dreal.github.io/download/) states that dReach
support is available only in dReal 3.

For ODE checking without a working Mac executable, run STLmc and its solver
together on Linux x86-64, then render the saved artifacts on the Mac. An amd64
Docker platform selection alone does not establish independence from Rosetta;
it is not a validated long-term workaround here.

## Yices on macOS

The official 2.7.0 ARM64 archive requires macOS 15.0 or newer; the Intel
archive requires macOS 12.0 or newer. They are not fully self-contained: both shared
libraries reference `/usr/local/lib/libcudd-3.0.0.0.dylib`. The same missing
dependency is reported for the ARM command-line executable in
[upstream issue #641](https://github.com/SRI-CSL/yices2/issues/641).
The `static-gmp` archive name does not mean that every dependency is static.
Automatic CUDD dependency installation is not provided on macOS.

Consequently, meeting the minimum OS version alone is insufficient. If the
required CUDD library is unavailable, the installer reports a native-load
failure rather than activating the download. Supply compatible dependencies
or use the explicit local-build route below. These archives have not been
validated across all macOS versions; a successful Python wheel installation
does not establish native solver compatibility.

An older system Yices installation can remain installed. A successfully
activated managed library takes precedence over ordinary system discovery;
an explicit `STLMC_YICES_LIBRARY` setting takes precedence over both.

## Yices source builds

The optional Linux/macOS source installer builds Yices 2.7.0 in a unique
user-owned prefix. It does not replace system libraries or install OS build
dependencies. Request native thread safety with:

```sh
stlmc-installer install --solver yices --build --thread-safe --jobs 4
stlmc-installer check --solver yices --thread-safe
```

`--jobs` controls compilation parallelism; `--thread-safe` requests a native
library that permits concurrent solver calls. They are separate settings.
Build tools include a C99 compiler, GNU make, gperf, sed, GMP development
headers/libraries, and autoconf when the source has no generated `configure`.
The default source build enables MCSAT and also needs libpoly and PIC CUDD
headers/libraries. Set `CPPFLAGS` and `LDFLAGS` for dependencies installed in
custom prefixes. Installing missing build tools through an OS package manager
may require administrator privileges; the source installer does not do this.

`--without-mcsat` explicitly requests an LRA/core-only build. It is unsuitable
for final `QF_NRA` queries. Pass that flag to the capability-check command too
when checking this profile; in check mode it removes the MCSAT requirement.
The installer probes the built library's version,
thread safety, and MCSAT support before activating it; requesting build flags
alone does not establish those capabilities. Failed builds retain the previous
active installation and report their build-log location.

Use `--prefix /path/to/user/builds` for a different build root, or
`--source /path/to/yices/source` to copy and build a local source tree.
Build-prefix paths must not contain whitespace. Successful builds are selected
through the user solver directory's `yices/active.json` manifest. An explicit
`STLMC_YICES_LIBRARY` absolute library path takes precedence, followed by the
active installation and then system discovery. An invalid explicit selection
is reported rather than silently replaced; restart a running Python process
to change an already loaded library.

The availability check reports native `thread_safe` and `mcsat` capabilities.
The managed installer requires Yices 2.7.0; an older native library is reported
as incompatible and the installer offers the pinned download or an explicit
local build.
When final Yices is selected with `parallel = "true"`, a library reporting
`thread_safe=False` is rejected before solving, even with one worker. Use a
verified thread-safe build or set `parallel = "false"` in the configuration.
Final `QF_NRA` queries also require MCSAT support. STLmc does not silently
disable parallel execution or change the requested arithmetic logic.

## dReal source builds

This experimental route is separate from the official-release baseline and is
never selected by ordinary installation or `--all`. It currently accepts
Linux x86-64 with GCC only. It builds the pinned
dReal 3.16.12 source snapshot at commit
`6fa469fb1f8485b695b00edc69aa9e9a35e7ba97`, which contains the
[parameter-invariant correction](https://github.com/dreal/dreal3/commit/2f564b2d7e9bbc930c67bfa0d5ce023809561447).
This is a source revision, not an official 3.16.12 binary release.

```sh
stlmc-installer install --solver dreal --experimental-build --jobs 4
stlmc-installer check --solver dreal
```

Successful compilation, linkage checks, and runtime feature probes do not
certify general ODE soundness. Upstream documents a case where failed ODE
pruning produced an incorrect delta-SAT witness; its
[issue remains open](https://github.com/dreal/dreal3/issues/325#issuecomment-293295914).
Both the official 3.16.06.02 binary and this pinned source build have reproduced
that witness defect. The parameter-invariant correction does not fix it.
Treat results from this build as experimental and validate
witnesses independently; sampled numerical checks are not an exact proof.
All macOS builds, including
Intel and ARM, are currently rejected by this build route. Nix and
Docker are not required. A host compiler, build tools, and the platform's
system development libraries/SDK are prerequisites; a private prefix does
not supply a compiler or replace the operating system runtime.

The installer automatically prepares CMake 3.29.6 in a private build venv;
no host CMake installation is required. This does not change system packages
or the Python environment used to run STLmc, including your project's `.venv`.

The build requires `gcc`, `g++`, `make`, `autoconf`, `automake`
(including `aclocal`), `autoreconf`, `libtoolize`, `m4`, `bison`, `flex`,
`pkg-config`, `git`, and `python2.7` on `PATH`, plus the system development
headers and static libraries needed by the compiler. Python 2.7 is required
only by the legacy IBEX build tools; it does not replace the Python version
used to run STLmc. The installer does not install these system prerequisites.

Third-party native dependencies are built inside the private prefix. On Linux,
static linking of those dependencies is required, with a completely static
executable preferred. Operating-system and compiler runtime libraries may
remain dynamic; this is not a promise of a completely static executable
or portability to every machine. Build-time dependency checks and the final
runtime probes must succeed before a build can be treated as usable.

The private build disables host CLP discovery and configures IBEX without LP
support (`--without-lp`). Its performance can therefore differ from an
external build with CLP/LP enabled.

Use `--prefix /path/to/private/dreal` to select a private build root. Each
attempt uses a fresh `builds/dreal-<unique-id>/prefix` below that root; without
`--prefix`, the root is the managed `dReal3` directory listed below. The build
manifest remains in the private prefix. Only after successful build and
runtime validation is the executable atomically copied to the managed
`dReal3/dReal` path. Failure leaves the previous executable active.

`--prefix` is an installer path, not a model input: it does not select a
`.model` file, change `-model-cfg`, or modify the model's dynamics. dReal
`--source` is rejected so that builds use the pinned source inputs.
`--thread-safe` and `--without-mcsat` are also Yices-only options, not dReal
build options.

Without `--experimental-build`, the installer uses the official-release
installation route rather than compiling this source snapshot. Its successful
installation does not establish ODE correctness; known limitations and the
remaining capability checks described above still apply.

## dReal executable discovery

Existing managed dReal installations are discovered at:

- macOS: `~/Library/Application Support/stlmc/solvers/dReal3/dReal`;
- Linux: `$XDG_DATA_HOME/stlmc/solvers/dReal3/dReal`, or
  `~/.local/share/stlmc/solvers/dReal3/dReal` when `XDG_DATA_HOME` is unset.

At runtime STLmc prefers the managed user installation above, then searches
`PATH` for `dReal`. Runtime checks inspect the dReal 3 version, algebraic and
ODE behavior, interior invariants, and zero-derivative parameter invariants.
The official 3.16.06.02 release is allowed despite its known invariant
limitation. The installer check reports this limitation; verification does
not repeat the warning. Unrelated failures remain errors. Passing these
targeted checks, including a check that succeeds with known-limit warnings,
does not certify every query or general ODE soundness. Independently supplied
builds are not thereby certified as official managed releases.
An explicit executable setting takes precedence; a separately supplied build
can be selected:

```sh
stlmc system.model -bound 5 -time-bound 20 -solver dreal \
    -executable-path /path/to/dReal
```

For a build available as `dReal` on `PATH`, run
`stlmc-installer check --solver dreal` to check compatibility. Native Apple
Silicon builds remain unvalidated; neither the version label alone nor a
successful binary launch establishes ODE correctness.

If a required solver is unavailable, STLmc reports the corresponding installer
command. Import errors in other native dependencies, such as SciPy, are a
separate environment issue: record the OS/CPU, Python version, and full error,
and check that the installed wheels match that environment. Reinstalling a
solver does not repair an incompatible SciPy binary.

## Removing components

Use `--dry-run` to inspect the removal plan first:

```sh
stlmc-installer uninstall --solver yices --visualize html pdf --dry-run
```

Then remove the selected components:

```sh
stlmc-installer uninstall --solver yices --visualize html pdf
```

`--solver` accepts `z3`, `cvc5`, `yices`, and `dreal`; `--visualize` accepts
`html`, `pdf`, and `text`. `uninstall --all --dry-run` previews removal of
all managed components; `--all` cannot be combined with individual selectors.
A selector or `--all` is required: removal never defaults to all components.
Removal does not uninstall STLmc itself, and `--dry-run` changes no files or
Python packages.

Only explicitly selected top-level Python packages in the active virtual
environment are uninstalled: `z3-solver`, `cvc5`, `yices`, `bokeh` for HTML,
and `matplotlib` for PDF. Text output has no optional package to uninstall.
Packages outside that virtual environment are preserved.

Native removal requires an installer ownership receipt and removes only
recorded files whose hashes still match. Modified or additional user files
are retained; only empty managed directories are pruned. Installations made
before ownership receipts were introduced, and custom source-build prefixes,
are kept for manual cleanup. Selecting Yices also removes its managed
activation, even when its native files must be retained. Apt/Homebrew packages,
externally supplied solver libraries, and counterexample or visualization
output files are not removed. NumPy and SciPy remain installed because they
are base STLmc dependencies, not optional visualization components.
The installer reports retained native paths for manual cleanup. It does not
change `STLMC_YICES_LIBRARY` or delete the installation explicitly selected
by that environment variable.

Stop jobs using the selected components before removing them. Python packages
may also be used by other applications in the same virtual environment, and
managed native installations are shared by that user across virtual
environments. The installer does not stop running processes or unload their
Python modules or native libraries; restart affected STLmc or UI processes
after changing their installed components.

## Offline and reproducible runs

STLmc may check PyPI for a newer version at startup and cache the result. To
disable that notification and its network request:

```sh
export STLMC_DISABLE_UPDATE_CHECK=1
```

Solver installation itself still needs network access unless dependencies
have already been installed. Record STLmc, Python, and solver versions with
your model, configuration, command, and logs when comparing runs. Solver
upgrades can change performance and witness selection.
