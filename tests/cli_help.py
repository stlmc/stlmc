import subprocess
import sys
import tempfile
import unittest
from unittest import mock
import contextlib
import ctypes
import io
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.cli.parser import BUILTIN_DEFAULTS, argument_help, build_parser
from stlmc.config_schema import OPTION_HELP, resolve_parallel_core
from stlmc.parser.config_visitor import ConfigVisitor


class CliHelpTest(unittest.TestCase):
    def test_readme_quickstart_runs_and_generates_inspectable_artifact(self):
        import os
        import re
        import shlex
        readme = (PROJECT_ROOT / 'README.md').read_text()
        section = readme.split('## Quick start\n', 1)[1].split('\n## ', 1)[0]
        model = re.search(r'```text\n(.*?)\n```', section, re.S).group(1)
        command = shlex.split(re.search(r'```sh\n(.*?)\n```', section, re.S).group(1))
        self.assertEqual(command[0], 'stlmc')
        env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'),
                   STLMC_DISABLE_UPDATE_CHECK='1', OPENBLAS_NUM_THREADS='1')
        with tempfile.TemporaryDirectory() as directory:
            working = Path(directory)
            (working / 'quickstart.model').write_text(model + '\n')
            completed = subprocess.run([
                sys.executable, '-c',
                'from stlmc.cli.mc import main; raise SystemExit(main())',
                *command[1:],
            ], cwd=working, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=20)
            self.assertEqual(completed.returncode, 0, completed.stdout)
            self.assertRegex(completed.stdout, r'status\s*:\s*violated at bound [012]')
            artifacts = list(working.glob('*.counterexample'))
            self.assertEqual(len(artifacts), 1, completed.stdout)
            config = artifacts[0].with_suffix('.cfg')
            self.assertTrue(config.is_file())
            # Only our own generated/trusted pickle is opened here.
            rendered = subprocess.run([
                sys.executable, '-c',
                'from stlmc.cli.visualize import main; main()',
                str(artifacts[0]), '-cfg', str(config), '-output', 'text',
            ], cwd=working, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=20)
            self.assertEqual(rendered.returncode, 0, rendered.stdout)
            self.assertNotIn('Traceback', rendered.stdout)

    def test_root_readme_links_are_absolute_and_repo_targets_exist(self):
        import re
        from urllib.parse import unquote
        readme = (PROJECT_ROOT / 'README.md').read_text()
        prefix = 'https://github.com/stlmc/stlmc/blob/main/'
        for target in re.findall(r'\]\(([^)]+)\)', readme):
            with self.subTest(target=target):
                self.assertTrue(target.startswith(('https://', '#')), target)
                if target.startswith(prefix):
                    relative = unquote(target[len(prefix):].split('#', 1)[0])
                    self.assertTrue((PROJECT_ROOT / relative).is_file(), target)

    def test_make_workflows_discover_all_unit_suites(self):
        import shutil
        if shutil.which('make') is None:
            self.skipTest('make is unavailable')
        for target in ('test-unit', 'test', 'test-quick'):
            completed = subprocess.run(['make', '-n', target], cwd=PROJECT_ROOT,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=10)
            self.assertEqual(completed.returncode, 0, completed.stdout)
            self.assertIn('unittest discover', completed.stdout)
            self.assertIn("-p '*.py'", completed.stdout)
        for target, script in (('test-flow-warnings', 'flow_warnings.py'),
                               ('test-sympy-differentiation', 'sympy_differentiation.py')):
            completed = subprocess.run(['make', '-n', target], cwd=PROJECT_ROOT,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=10)
            self.assertEqual(completed.returncode, 0, completed.stdout)
            self.assertIn(script, completed.stdout)

    def test_signal_during_z3_construction_does_not_unwind_partial_objects(self):
        import gc
        import signal
        import z3
        from stlmc.cli.mc import main, _raise_keyboard_interrupt
        from stlmc.utils.interrupt import clear_interrupt

        original = z3.AstRef.__init__
        unraisable = []
        output = io.StringIO()

        def interrupted_init(instance, *args, **kwargs):
            # Reproduce delivery before AstRef has installed its ctx/ast.
            _raise_keyboard_interrupt(signal.SIGTERM, None)
            original(instance, *args, **kwargs)

        try:
            with mock.patch.object(sys, 'argv', ['stlmc', __file__]), \
                    mock.patch('stlmc.update_check.notify_if_outdated'), \
                    mock.patch.object(z3.AstRef, '__init__', interrupted_init), \
                    mock.patch.object(sys, 'unraisablehook', unraisable.append), \
                    mock.patch('stlmc.application.workflow.VerificationWorkflow.run',
                               side_effect=lambda *args: z3.Bool('interrupt_during_init')), \
                    contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
                status = main()
                gc.collect()
            self.assertEqual(status, 130)
            self.assertFalse(unraisable)
            self.assertNotIn('Traceback', output.getvalue())
        finally:
            clear_interrupt()

    def test_native_argument_error_after_signal_is_clean_cancellation(self):
        import signal
        from stlmc.cli.mc import main, _raise_keyboard_interrupt
        from stlmc.utils.interrupt import clear_interrupt

        class InterruptedArgument:
            @classmethod
            def from_param(cls, value):
                _raise_keyboard_interrupt(signal.SIGTERM, None)
                raise TypeError('conversion interrupted')

        native = ctypes.CFUNCTYPE(None, InterruptedArgument)(lambda value: None)
        output = io.StringIO()
        try:
            with mock.patch.object(sys, 'argv', ['stlmc', __file__]), \
                    mock.patch('stlmc.update_check.notify_if_outdated'), \
                    mock.patch('stlmc.application.workflow.VerificationWorkflow.run',
                               side_effect=lambda *args: native(object())), \
                    contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
                status = main()
            self.assertEqual(status, 130)
            self.assertIn('interrupted by user', output.getvalue())
            self.assertNotIn('Traceback', output.getvalue())
            self.assertNotIn('error:', output.getvalue())
        finally:
            clear_interrupt()

    def test_native_argument_error_without_signal_remains_an_error(self):
        from stlmc.cli.mc import main
        output = io.StringIO()
        with mock.patch.object(sys, 'argv', ['stlmc', __file__]), \
                mock.patch('stlmc.update_check.notify_if_outdated'), \
                mock.patch('stlmc.application.workflow.VerificationWorkflow.run',
                           side_effect=ctypes.ArgumentError('ordinary native error')), \
                contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            status = main()
        self.assertEqual(status, 1)
        self.assertIn('ordinary native error', output.getvalue())
        self.assertIn('Traceback', output.getvalue())

    def test_development_temporal_form_option_is_hidden(self):
        help_text = build_parser(prog="stlmc").format_help()
        self.assertNotIn("unary-bounded-temporal", help_text)
        value_options, boolean_options = ConfigVisitor().generate_cmd_args()
        all_options = set(value_options).union(boolean_options)
        self.assertNotIn("use-unary-bounded-temporal-form", all_options)

    def test_quoted_config_value_preserves_spaces(self):
        with tempfile.TemporaryDirectory() as directory:
            config_path = Path(directory) / "space-path.cfg"
            expected = (
                "/Users/runner/Library/Application Support/"
                "stlmc/solvers/dReal3/dReal"
            )
            config_path.write_text(
                'dreal { executable-path = "' + expected + '" }\n',
                encoding="utf-8",
            )

            config = ConfigVisitor().parse_from_file(str(config_path))

        self.assertEqual(
            config.get_section("dreal").get_value("executable-path"),
            expected,
        )

    def test_every_config_option_has_a_specific_description(self):
        visitor = ConfigVisitor()
        value_options, boolean_options = visitor.generate_cmd_args()
        expected = set(value_options).union(boolean_options)

        self.assertTrue(expected.issubset(OPTION_HELP.keys()))

    def test_fast_help_contains_every_description(self):
        help_text = build_parser(prog="stlmc").format_help()

        for name in OPTION_HELP:
            with self.subTest(option=name):
                for line in argument_help(name).splitlines():
                    self.assertIn(line.strip(), help_text)

    def test_help_groups_optimizations_separately(self):
        help_text = build_parser(prog="stlmc").format_help()
        scenario_section = help_text.split("optimizations:", 1)[1].split(
            "solver options:", 1
        )[0]

        for option in ("-concrete", "-solver-batch-size", "-smt-preprocess"):
            self.assertIn(option, scenario_section)

        model_section = help_text.split("model checking:", 1)[1].split(
            "optimizations:", 1
        )[0]
        for option in ("-two-step", "-parallel", "-parallel-core"):
            self.assertIn(option, model_section)

        output_section = help_text.split("output and debugging:", 1)[1]
        for option in ("-verbose", "-visualize", "-save-smt2", "-smt2-dir"):
            self.assertIn(option, output_section)

    def test_help_shows_every_finite_option_choice(self):
        help_text = build_parser(prog="stlmc").format_help()

        for choices in (
            "choices: auto, cvc5, dreal, z3, yices",
            "choices: symbolic, explicit",
            "choices: QF_LRA, QF_NRA",
        ):
            self.assertIn(choices, help_text)

        self.assertIn("-solver SOLVER", help_text)
        self.assertIn("-path-strategy STRATEGY", help_text)
        self.assertIn("-logic LOGIC", help_text)

    def test_help_defaults_match_default_configuration(self):
        visitor = ConfigVisitor()
        config = visitor.parse_from_file(
            str(PROJECT_ROOT / "src" / "stlmc" / "default.cfg")
        )
        config_defaults = {}
        for section in config.sections:
            for name in section.arguments:
                value = section.get_value(name)
                if name in config_defaults:
                    self.assertEqual(config_defaults[name], value, name)
                config_defaults[name] = value

        self.assertEqual(BUILTIN_DEFAULTS, config_defaults)

    def test_parallel_core_auto_uses_available_logical_cpus(self):
        self.assertEqual(resolve_parallel_core("auto", cpu_count=12), "12")
        self.assertEqual(resolve_parallel_core("auto", cpu_count=0), "1")
        self.assertEqual(resolve_parallel_core("7", cpu_count=12), "7")

    def test_visualization_cli_import_does_not_load_heavy_dependencies(self):
        code = (
            "import sys; import stlmc.cli.visualize; "
            "assert 'bokeh' not in sys.modules; "
            "assert 'stlmc.visualize.visualizer' not in sys.modules"
        )
        completed = subprocess.run(
            [sys.executable, "-c", code],
            cwd=PROJECT_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )

        self.assertEqual(completed.returncode, 0, completed.stdout)

    def test_missing_model_path_exits_before_heavy_imports(self):
        code = (
            "import sys; "
            "sys.argv = ['stlmc']; "
            "from stlmc.cli.mc import main; "
            "result = main(); "
            "assert result == 2, result; "
            "assert 'z3' not in sys.modules; "
            "assert 'bokeh' not in sys.modules; "
            "assert 'stlmc.parser.model_visitor' not in sys.modules; "
            "assert 'stlmc.driver.base_driver' not in sys.modules"
        )
        completed = subprocess.run(
            [sys.executable, "-c", code],
            cwd=PROJECT_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout)
        self.assertEqual(
            completed.stdout.strip(),
            "error: should provide an STLmc model file path",
        )

    def test_model_path_usage_errors_exit_before_heavy_imports(self):
        # Keep each case in a fresh interpreter so imported-module assertions
        # cannot be satisfied by an earlier case accidentally.
        with tempfile.TemporaryDirectory() as directory:
            cases = (
                (["missing.model"], "not a valid STLmc model file path"),
                (["-solver", "z3"], "should provide an STLmc model file path"),
                ([directory], "is not a file"),
            )
            for arguments, expected in cases:
                case_code = (
                    "import sys; "
                    "sys.argv = {!r}; "
                    "from stlmc.cli.mc import main; "
                    "result = main(); "
                    "assert result == 2, result; "
                    "assert 'z3' not in sys.modules; "
                    "assert 'bokeh' not in sys.modules; "
                    "assert 'stlmc.driver.base_driver' not in sys.modules"
                ).format(["stlmc"] + arguments)
                completed = subprocess.run(
                    [sys.executable, "-c", case_code], cwd=PROJECT_ROOT,
                    text=True, stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                )
                self.assertEqual(completed.returncode, 0, completed.stdout)
                self.assertIn(expected, completed.stdout)

    def test_model_checker_import_does_not_eagerly_load_visualization(self):
        code = (
            "import sys; import stlmc.driver.base_driver; "
            "assert 'bokeh' not in sys.modules; "
            "assert 'stlmc.visualize.visualizer' not in sys.modules; "
            "assert 'stlmc.solver.dreal' not in sys.modules"
        )
        completed = subprocess.run(
            [sys.executable, "-c", code], cwd=PROJECT_ROOT,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout)

    def test_missing_explicit_config_exits_before_heavy_imports(self):
        with tempfile.NamedTemporaryFile("w", suffix=".model") as model_file:
            for option in (
                "-default-cfg", "-model-cfg", "-model-specific-cfg"
            ):
                code = (
                    "import sys; "
                    "sys.argv = {!r}; "
                    "from stlmc.cli.mc import main; "
                    "result = main(); "
                    "assert result == 2, result; "
                    "assert 'z3' not in sys.modules; "
                    "assert 'bokeh' not in sys.modules; "
                    "assert 'stlmc.driver.base_driver' not in sys.modules"
                ).format([
                    "stlmc", model_file.name, option,
                    "/definitely/missing/stlmc.cfg",
                ])
                completed = subprocess.run(
                    [sys.executable, "-c", code], cwd=PROJECT_ROOT,
                    text=True, stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                )
                self.assertEqual(completed.returncode, 0, completed.stdout)
                self.assertIn("configuration file", completed.stdout)
                self.assertIn("does not exist or is not a file", completed.stdout)

    def test_malformed_model_returns_usage_error(self):
        with tempfile.NamedTemporaryFile(
                "w", suffix=".model", encoding="utf-8") as model_file:
            model_file.write("this is not an stlmc model\n")
            model_file.flush()
            code = (
                "import sys; "
                "sys.argv = {!r}; "
                "from stlmc.cli.mc import main; "
                "raise SystemExit(main())"
            ).format(["stlmc", model_file.name])
            completed = subprocess.run(
                [sys.executable, "-c", code], cwd=PROJECT_ROOT,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )

        self.assertEqual(completed.returncode, 2, completed.stdout)
        self.assertTrue(
            "parsing error:" in completed.stdout
            or "conversion error:" in completed.stdout,
            completed.stdout,
        )

if __name__ == "__main__":
    unittest.main()
