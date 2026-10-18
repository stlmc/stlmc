# Installation and troubleshooting

Install STLmc in a virtual environment with a current pip. The package
provides `stlmc`, `stlmc-vis`, and `stlmc-installer`.
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

Choose `install` or `check` before the component selectors. Both `--solver`
and `--visualize` accept multiple names, for example `install --solver z3 cvc5`
or `check --visualize html pdf text`. Running the installer without an action
shows help and does not install anything. `stlmc-installer install --all`
selects all components, including the official dReal binary on supported
platforms. `stlmc-installer check` checks all solvers
and visualization formats, including both HTML and PDF, without installing.
Native package installation may request administrator privileges. Python
packages install into the current interpreter's environment.

Use `stlmc-installer` to install solver and visualization dependencies.
Package extras are not provided; the default package includes no solver
bindings or optional HTML/PDF renderers.

## Platforms

Automatic Yices native-library installation supports Ubuntu/Debian through the
SRI package repository and macOS through Homebrew. Other Linux distributions
can use the optional source build after installing its build dependencies, or
install a native library manually. The default Yices installation uses the
official package distribution; source compilation is an explicit option.

`install --solver dreal` downloads the official dReal **3** release
3.16.06.02 on Linux x86-64 and supported macOS systems. macOS uses the Intel
release; Apple Silicon requires Rosetta to be installed already. It verifies the pinned
archive hash, exact version, and a basic algebraic SAT query. These checks
establish installation, not ODE correctness: this release has known bugs,
including omitted invariants involving zero-derivative parameters.
`check --solver dreal` reports this official release's known invariant
limitation. Verification allows execution without a runtime warning. This exception
does not suppress unrelated executable errors or failed capability checks.
A successful install or check does not certify ODE correctness; results may
be affected by these known bugs.
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

For ODE checking without a working Mac executable, run STLmc and its solver
together on Linux x86-64, then render the saved artifacts on the Mac. An amd64
Docker platform selection alone does not establish independence from Rosetta;
it is not a validated long-term workaround here.

## Yices on macOS

If Homebrew reports an untrusted third-party formula, explicitly trust only
the required formulae before retrying:

```sh
brew tap SRI-CSL/sri-csl
brew trust --formula sri-csl/sri-csl/yices2
brew trust --formula sri-csl/sri-csl/libpoly
brew trust --formula sri-csl/sri-csl/cudd
stlmc-installer install --solver yices
```

These are the Homebrew 6 trust commands. Trusting the whole tap is not required.
Users with an already available Python binding and native library do not need
to repeat this setup.

If an Apple Silicon installation cannot find `libyices.dylib`, expose the
Homebrew library directory in the current shell:

```sh
export DYLD_LIBRARY_PATH="$(brew --prefix)/lib"
stlmc-installer check --solver yices
```

The release workflow also checks Rosetta availability for legacy macOS
executables. A Python wheel installing successfully does not establish that
all downloaded native binaries can run on the host.

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
as incompatible and the installer explains how to build the required version.
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
installation does not establish ODE correctness; runtime warnings and the
remaining capability checks described above still apply.

## dReal executable discovery

Existing managed dReal installations are discovered at:

- macOS: `~/Library/Application Support/stlmc/solvers/dReal3/dReal`;
- Linux: `$XDG_DATA_HOME/stlmc/solvers/dReal3/dReal`, or
  `~/.local/share/stlmc/solvers/dReal3/dReal` when `XDG_DATA_HOME` is unset.

At runtime STLmc prefers the managed user installation above, then searches
`PATH` for `dReal`. Runtime checks inspect the dReal 3 version, algebraic and
ODE behavior, interior invariants, and zero-derivative parameter invariants.
The official 3.16.06.02 release is allowed with a warning for its known
invariant limitation; unrelated failures remain errors. Passing these
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

## Visualization

The visualization installer currently has a validated dependency profile only
for CPython 3.10: NumPy 2.2.6, SciPy 1.15.3, Bokeh 3.1.1, and Matplotlib
3.10.8. Visualization `check` and `install` on other Python versions
report an unvalidated-profile error (exit status 1). This narrower installer
coverage is separate from the core package's Python support range.

Writing model-checker artifacts and rendering text do not require Bokeh.
HTML rendering requires optional Bokeh, installed by
`stlmc-installer install --visualize html`. PDF rendering uses optional Matplotlib
with a headless backend; it does not require Bokeh or an external plotting
executable. Saved artifacts can be
rendered without solver bindings. Select the format explicitly when checking
or installing its prerequisites:

```sh
stlmc-installer check --visualize html
stlmc-installer install --visualize html
stlmc-installer check --visualize text
stlmc-installer check --visualize pdf
stlmc-installer install --visualize pdf
```

The HTML check requires Bokeh, whereas
the PDF check requires Matplotlib. Text and PDF checks require NumPy and SciPy
but not Bokeh. Renderer installation uses pip in the current Python environment
and does not invoke an OS package manager.

```sh
stlmc-vis result.counterexample -cfg result.cfg -output text
stlmc-vis result.counterexample -cfg result.cfg -output pdf
```

Result files use versioned, gzip-compressed JSON and retain the
`.counterexample` and `.witness` extensions. Legacy pickle files are outdated
and unsupported. Rerun model checking with the current STLmc version to
regenerate them; no conversion is provided.

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
