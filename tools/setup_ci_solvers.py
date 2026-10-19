"""Expose managed native solver executables to subsequent CI subprocesses."""

import json
import os
from pathlib import Path
import sys


def yices_environment(manifest_path, selected_library, environment, platform):
    metadata = json.loads(Path(manifest_path).read_text())
    prefix = Path(metadata['prefix']).resolve(strict=True)
    library = Path(metadata['library']).resolve(strict=True)
    if library != Path(selected_library).resolve(strict=True) or not library.is_relative_to(prefix):
        raise RuntimeError('CI requires the active managed Yices installation')
    executable = prefix / 'bin' / 'yices-smt2'
    if not executable.is_file() or not os.access(executable, os.X_OK):
        raise RuntimeError('Managed yices-smt2 executable is unavailable')
    directories = [str(library.parent)]
    for dependency in metadata.get('dependencies', []):
        directories.append(str(Path(dependency['library']).resolve(strict=True).parent))
    variable = 'DYLD_LIBRARY_PATH' if platform == 'darwin' else 'LD_LIBRARY_PATH'
    if environment.get(variable):
        directories.append(environment[variable])
    values = {'PATH': str(executable.parent) + os.pathsep + environment.get('PATH', ''),
              variable: os.pathsep.join(dict.fromkeys(directories))}
    if any('\n' in value or '\r' in value for value in values.values()):
        raise RuntimeError('CI solver environment contains a newline')
    return values


def main():
    from stlmc.solver.availability import selected_yices_library, solver_data_dir
    # Validate manifest dependency hashes through the installed package before
    # exposing their directories to command-line solver subprocesses.
    selected = selected_yices_library()
    if selected is None or 'STLMC_YICES_LIBRARY' in os.environ:
        raise RuntimeError('CI requires an active managed Yices installation')
    values = yices_environment(solver_data_dir() / 'yices/active.json', selected,
                               os.environ, sys.platform)
    with open(os.environ['GITHUB_ENV'], 'a', encoding='utf-8') as output:
        for key, value in values.items():
            output.write('{}={}\n'.format(key, value))


if __name__ == '__main__':
    main()
