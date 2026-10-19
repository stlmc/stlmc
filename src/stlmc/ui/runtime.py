"""Check the exact STLMC interfaces required by the worker."""
import importlib
from importlib import metadata
import shlex
import sys
from packaging.specifiers import InvalidSpecifier, SpecifierSet


def inspect_visualization():
    """Keep optional rendering failures separate from solver availability."""
    command = '{} -m stlmc.cli.installer install --visualize html'.format(shlex.quote(sys.executable))
    try:
        policy = importlib.import_module('stlmc.cli.dependency_policy')
        expected = policy.visualization_packages(sys.version_info)['bokeh'].split('==')[1]
        actual = metadata.version('bokeh')
        if actual != expected:
            raise RuntimeError('Bokeh {} is installed; the managed version is {}'.format(actual, expected))
        from bokeh.models import HoverTool
        HoverTool(visible=False)
    except (ImportError, metadata.PackageNotFoundError, AttributeError, RuntimeError, OSError, ValueError, TypeError) as error:
        return {'available': False, 'error': 'HTML visualization unavailable: {}. Run: {}'.format(error, command)}
    return {'available': True, 'error': None}


def inspect_runtime():
    location = None
    try:
        if not (3, 11) <= sys.version_info[:2] < (3, 15):
            raise ImportError('Python 3.11 through 3.14 is required; create a new virtual environment')
        package = importlib.import_module('stlmc')
        location = getattr(package, '__file__', None) or str(list(getattr(package, '__path__', [])))
        printer = importlib.import_module('stlmc.utils.print').BasePrinter
        check = importlib.import_module('stlmc.cli.mc').main
        if not callable(getattr(printer, 'run_finished', None)) or not callable(check):
            raise ImportError('Required STLMC result interface is missing')
        installed = metadata.metadata('stlmc')
        # This UI targets the current source contract. Old editable metadata
        # otherwise passes pip check while importing incompatible updated code.
        if SpecifierSet(installed.get('Requires-Python') or '') != SpecifierSet('>=3.11,<3.15'):
            raise ImportError('STLMC installation metadata is outdated; reinstall STLmc with this interpreter')
    except (ImportError, AttributeError, OSError, InvalidSpecifier) as error:
        return {'stlmc': False, 'python': sys.version.split()[0],
                'executable': sys.executable, 'location': location,
                'error': 'Incompatible or missing STLMC: {}. Reinstall STLmc with this Python: '
                         '{} -m pip install --upgrade --pre --force-reinstall --no-deps stlmc. '
                         'Then restart stlmc-gui. For a development checkout, reinstall that '
                         'checkout in editable mode instead.'.format(error, shlex.quote(sys.executable))}
    return {'stlmc': True, 'python': sys.version.split()[0],
            'executable': sys.executable, 'location': location, 'error': None,
            'visualization': inspect_visualization()}
