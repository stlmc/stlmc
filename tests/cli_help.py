import subprocess
import sys
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.cli.parser import BUILTIN_DEFAULTS, argument_help, build_parser
from stlmc.config_schema import OPTION_HELP
from stlmc.parser.config_visitor import ConfigVisitor


class CliHelpTest(unittest.TestCase):
    def test_every_config_option_has_a_specific_description(self):
        visitor = ConfigVisitor()
        value_options, boolean_options = visitor.generate_cmd_args()
        expected = set(value_options).union(boolean_options)

        self.assertTrue(expected.issubset(OPTION_HELP.keys()))

    def test_fast_help_contains_every_description(self):
        help_text = build_parser(prog="stlmc").format_help()

        for name in OPTION_HELP:
            with self.subTest(option=name):
                self.assertIn(argument_help(name), help_text)

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

if __name__ == "__main__":
    unittest.main()
