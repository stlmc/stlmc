"""One isolated STLMC invocation; structured results use its printer boundary."""
import inspect
import json
from functools import wraps
import sys
import threading
import time
from pathlib import Path


def render_artifacts(visualization):
    """Persist rendering outcomes; a verification result is not a plot result."""
    artifacts = sorted(Path('.').glob('*.counterexample')) + sorted(Path('.').glob('*.witness'))
    for artifact in artifacts:
        result = {'artifact': artifact.name, 'error': None}
        try:
            if not visualization.get('available', False):
                raise RuntimeError(visualization.get('error') or 'HTML visualization is unavailable')
            from stlmc.cli.visualize import main as visualize
            previous = sys.argv
            try:
                sys.argv = ['stlmc-vis', str(artifact), '-cfg', str(artifact.with_suffix('.cfg')), '-output', 'html']
                code = visualize()
            finally:
                sys.argv = previous
            if code not in (None, 0) or not Path(str(artifact) + '.html').is_file():
                raise RuntimeError('stlmc-vis did not generate HTML (exit code {})'.format(code))
        except Exception as error:
            result['error'] = '{}. Install/check HTML support with: stlmc-installer install --visualize html'.format(error)
            print('Visualization unavailable: {}'.format(error), flush=True)
        with open('visualization.jsonl', 'a', encoding='utf-8') as stream:
            stream.write(json.dumps(result) + '\n')


def capture_results(original):
    """Forward exactly the arguments STLMC supplied, across printer versions."""
    signature = inspect.signature(original)

    @wraps(original)
    def finished(self, *args, **kwargs):
        arguments = signature.bind(self, *args, **kwargs)
        arguments.apply_defaults()
        values = arguments.arguments
        returned = original(self, *args, **kwargs)
        result = dict(status=values['status'], bound=values['bound'],
                      elapsed=values['elapsed'], formula=str(values['formula']),
                      scope=values['scope'], guarantee=values.get('guarantee'),
                      artifact=values.get('counterexample'),
                      config=values.get('visual_config'))
        with open('results.jsonl', 'a', encoding='utf-8') as stream:
            stream.write(json.dumps(result) + '\n')
        return returned

    return finished


def install_progress_hooks(printer):
    """Capture printer events even when CLI progress is suppressed for a pipe."""
    state = {'session': 0, 'goal': None, 'last_scenario': 0.0}
    lock = threading.Lock()

    def wrap(name, original):
        signature = inspect.signature(original)

        @wraps(original)
        def report(self, *args, **kwargs):
            arguments = signature.bind(self, *args, **kwargs)
            arguments.apply_defaults()
            returned = original(self, *args, **kwargs)
            values = {k: v for k, v in arguments.arguments.items() if k != 'self'}
            with lock:
                if name == 'run_started':
                    state['session'] += 1
                    state['goal'] = str(values.get('goal', 'Goal'))
                if name == 'scenario_progress':
                    now = time.monotonic()
                    if now - state['last_scenario'] < 0.25:
                        return returned
                    state['last_scenario'] = now
                event = dict(event=name, time=time.time(), session=state['session'],
                             goal=state['goal'], data=values)
                if name == 'scenario_progress':
                    temporary = Path('scenario.tmp')
                    temporary.write_text(json.dumps(event, default=str), encoding='utf-8')
                    temporary.replace('scenario.json')
                else:
                    with open('progress.jsonl', 'a', encoding='utf-8') as stream:
                        stream.write(json.dumps(event, default=str) + '\n')
            return returned
        return report

    for name in ('run_started', 'bound_finished', 'scenario_progress', 'run_finished'):
        original = getattr(printer, name, None)
        if callable(original):
            setattr(printer, name, wrap(name, original))


def main():
    from .runtime import inspect_runtime

    runtime = inspect_runtime()
    if sys.argv[1:] == ['--check-runtime']:
        print(json.dumps(runtime))
        return 0
    if not runtime['stlmc']:
        print(runtime['error'], flush=True)
        return 3

    from stlmc.utils.print import BasePrinter
    from stlmc.cli.mc import main as check

    BasePrinter.run_finished = capture_results(BasePrinter.run_finished)
    install_progress_hooks(BasePrinter)
    code = check()
    if code:
        return code
    # Only deserialize artifacts produced by this invocation, never uploads.
    render_artifacts(runtime.get('visualization', {}))
    return 0


if __name__ == '__main__':
    sys.exit(main())
