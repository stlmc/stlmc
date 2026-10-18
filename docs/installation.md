# Installation and troubleshooting

Install STLmc in a virtual environment with a current pip. The package
provides `stlmc`, `stlmc-vis`, and `stlmc-install-solvers`. The Python interfaces
for cvc5, Z3, and Yices are package dependencies; Yices additionally needs its
native library, and dReal needs an external executable.

```sh
stlmc-install-solvers --check
stlmc-install-solvers yices
stlmc-install-solvers dreal
```

The installer defaults to `all` when no solver is specified. `--check` reports
availability without installing software. Native installation may download
third-party software and request administrator privileges. Installing every
solver is unnecessary when your models only require one backend; Z3 is also
used internally by STLmc, independently of the final solver.

## Platforms

Automatic Yices native-library installation supports Ubuntu/Debian through the
SRI package repository and macOS through Homebrew. Other Linux distributions
require manual installation of the native library.

Automatic dReal installation downloads a dReal **3** binary for macOS or
x86-64 Linux. It does not install dReal 4. Automatic native solver setup on
Windows, and dReal setup on Linux ARM, are not supported by this installer.
Python package support does not imply availability of every solver on every
OS/CPU combination. The release workflow covers Linux x86-64 and macOS Apple
Silicon; check its results for the release you intend to use.

## Yices on macOS

If Homebrew reports an untrusted third-party formula, explicitly trust only
the required formulae before retrying:

```sh
brew tap SRI-CSL/sri-csl
brew trust --formula sri-csl/sri-csl/yices2
brew trust --formula sri-csl/sri-csl/libpoly
brew trust --formula sri-csl/sri-csl/cudd
stlmc-install-solvers yices
```

These are the Homebrew 6 trust commands. Trusting the whole tap is not required.
Users with an already available Python binding and native library do not need
to repeat this setup.

If an Apple Silicon installation cannot find `libyices.dylib`, expose the
Homebrew library directory in the current shell:

```sh
export DYLD_LIBRARY_PATH="$(brew --prefix)/lib"
stlmc-install-solvers yices --check
```

The release workflow also checks Rosetta availability for legacy macOS
executables. A Python wheel installing successfully does not establish that
all downloaded native binaries can run on the host.

## dReal executable discovery

The installer writes dReal to:

- macOS: `~/Library/Application Support/stlmc/solvers/dReal3/dReal`;
- Linux: `$XDG_DATA_HOME/stlmc/solvers/dReal3/dReal`, or
  `~/.local/share/stlmc/solvers/dReal3/dReal` when `XDG_DATA_HOME` is unset.

At runtime STLmc first searches `PATH` for `dReal`, then the user directory
above. A differently named or separately installed binary can be selected:

```sh
stlmc system.model -bound 5 -time-bound 20 -solver dreal \
    -executable-path /path/to/dReal
```

If a required solver is unavailable, STLmc reports the corresponding installer
command. Import errors in other native dependencies, such as SciPy, are a
separate environment issue: record the OS/CPU, Python version, and full error,
and check that the installed wheels match that environment. Reinstalling a
solver does not repair an incompatible SciPy binary.

## Visualization

HTML and text output use the Python dependencies installed with STLmc. PDF
output additionally requires Gnuplot with a PDF-capable terminal. It is not
installed by `stlmc-install-solvers`.

```sh
stlmc-vis result.counterexample -cfg result.cfg -output text
stlmc-vis result.counterexample -cfg result.cfg -output pdf
```

Only load artifacts from trusted sources: result files contain Python pickle
data, not a safe interchange format.

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
