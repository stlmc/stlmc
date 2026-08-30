import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.cli.parser import BUILTIN_DEFAULTS, argument_help, build_parser
from stlmc.config_schema import OPTION_HELP, resolve_parallel_core
from stlmc.parser.config_visitor import ConfigVisitor


class CliHelpTest(unittest.TestCase):
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

        for option in ("-concrete", "-solver-batch-size"):
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

if __name__ == "__main__":
    unittest.main()
