import tempfile
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent


class ParserInputTest(unittest.TestCase):
    def assert_syntax_diagnostic(self, parser, source, description):
        with tempfile.NamedTemporaryFile("w", suffix=".input") as input_file:
            input_file.write(source)
            input_file.flush()
            with self.assertRaises(SyntaxError) as raised:
                parser(input_file.name)
        message = str(raised.exception)
        self.assertIn(":1:", message)
        self.assertIn("syntax error in {}".format(description), message)
        self.assertIn("unexpected", message)
        self.assertIn("expected", message)
        self.assertIn("^", message)

    def test_all_benchmark_models_parse(self):
        from stlmc.parser.model_visitor import ModelVisitor

        paths = sorted((PROJECT_ROOT / "tests" / "benchmarks").glob("*/*.model"))
        self.assertEqual(len(paths), 21)
        for path in paths:
            with self.subTest(model=str(path.relative_to(PROJECT_ROOT))):
                ModelVisitor().get_parse_tree(str(path))

    def test_all_benchmark_configurations_parse(self):
        from stlmc.parser.config_visitor import ConfigVisitor

        default_path = PROJECT_ROOT / "src" / "stlmc" / "default.cfg"
        parsed = 0
        for directory in sorted((PROJECT_ROOT / "tests" / "benchmarks").iterdir()):
            if not directory.is_dir():
                continue
            model_configs = [
                path for path in directory.glob("*.cfg")
                if "-" not in path.stem
            ]
            if not model_configs:
                continue
            model_config = model_configs[0]
            for goal_config in sorted(directory.glob("*.cfg")):
                visitor = ConfigVisitor()
                config = visitor.parse_from_file(str(default_path))
                config = visitor.parse_from_file(str(model_config), config)
                if goal_config != model_config:
                    visitor.parse_from_file(str(goal_config), config)
                parsed += 1
        self.assertEqual(parsed, 78)

    def test_visualization_configuration_parses(self):
        from stlmc.parser.visualize_visitor import VisualizeConfigParser

        with tempfile.NamedTemporaryFile("w", suffix=".cfg") as config_file:
            config_file.write("{ output = html group { (x, y), (z) } }")
            config_file.flush()
            parser = VisualizeConfigParser()
            parser.read(config_file.name)
        self.assertEqual(parser.output, "html")
        self.assertEqual(parser.group, {0: {"x", "y"}, 1: {"z"}})

    def test_model_syntax_error_has_actionable_context(self):
        from stlmc.parser.model_visitor import ModelVisitor

        self.assert_syntax_diagnostic(
            ModelVisitor().get_parse_tree, "real x @;", "model"
        )

    def test_model_section_typo_suggests_keyword_without_parser_internals(self):
        from stlmc.parser.model_visitor import ModelVisitor

        source = """real x;
{ mode: true; inv: flow: d/dt[x] = 0; jump: }
init: true;
propositions:
goal: true;
"""
        with tempfile.NamedTemporaryFile("w", suffix=".model") as model_file:
            model_file.write(source)
            model_file.flush()
            with self.assertRaises(SyntaxError) as raised:
                ModelVisitor().get_parse_tree(model_file.name)
        message = str(raised.exception)
        self.assertIn("unknown keyword 'propositions'", message)
        self.assertIn("did you mean 'proposition'?", message)
        self.assertNotIn("anon", message)
        self.assertNotIn("temporal op", message)

    def test_model_declaration_keyword_typo_suggests_const(self):
        from stlmc.parser.model_visitor import ModelVisitor

        with tempfile.NamedTemporaryFile("w", suffix=".model") as model_file:
            model_file.write("con = b;")
            model_file.flush()
            with self.assertRaises(SyntaxError) as raised:
                ModelVisitor().get_parse_tree(model_file.name)
        message = str(raised.exception)
        self.assertIn("unknown keyword 'con'", message)
        self.assertIn("did you mean 'const'?", message)

    def test_model_constant_name_value_explains_allowed_literals(self):
        from stlmc.parser.model_visitor import ModelVisitor

        with tempfile.NamedTemporaryFile("w", suffix=".model") as model_file:
            model_file.write("const con = b;")
            model_file.flush()
            with self.assertRaises(SyntaxError) as raised:
                ModelVisitor().get_parse_tree(model_file.name)
        message = str(raised.exception)
        self.assertIn("constant values must be a number", message)
        self.assertIn("a name cannot be used here", message)

    def test_operator_without_right_expression_points_to_invalid_operator(self):
        from stlmc.parser.model_visitor import ModelVisitor

        source = """real x;
{ mode: true; inv: x > 10 + * 2; flow: d/dt[x] = 0; jump: }
init: true;
goal: true;
"""
        with tempfile.NamedTemporaryFile("w", suffix=".model") as model_file:
            model_file.write(source)
            model_file.flush()
            with self.assertRaises(SyntaxError) as raised:
                ModelVisitor().get_parse_tree(model_file.name)
        message = str(raised.exception)
        self.assertIn(":2:29: syntax error in model", message)
        self.assertIn("operator '*' cannot follow '+'", message)
        self.assertIn("inv: x > 10 + * 2", message)
        self.assertNotIn("add op", message)
        self.assertNotIn("func op", message)

    def test_unary_plus_in_flow_is_supported(self):
        from stlmc.parser.model_visitor import ModelVisitor

        source = """real x;
{ mode: true; inv: flow: d/dt[x] = x * + 10; jump: }
init: true;
goal: true;
"""
        with tempfile.NamedTemporaryFile("w", suffix=".model") as model_file:
            model_file.write(source)
            model_file.flush()
            model, _, _, _ = ModelVisitor().get_parse_tree(model_file.name)
        self.assertEqual(len(model.modules), 1)

    def test_configuration_syntax_error_has_actionable_context(self):
        from stlmc.parser.config_visitor import ConfigVisitor

        self.assert_syntax_diagnostic(
            ConfigVisitor().parse_from_file, "common { solver = @ }", "configuration"
        )

    def test_unknown_configuration_section_suggests_nearest_name(self):
        from stlmc.exceptions import NotSupportedError
        from stlmc.parser.config_visitor import ConfigVisitor

        with tempfile.NamedTemporaryFile("w", suffix=".cfg") as config_file:
            config_file.write("commmon { bound = 1 }")
            config_file.flush()
            with self.assertRaises(NotSupportedError) as raised:
                ConfigVisitor().parse_from_file(config_file.name)
        message = str(raised.exception)
        self.assertIn("{}:1:1".format(config_file.name), message)
        self.assertIn("unknown configuration section 'commmon'", message)
        self.assertIn("did you mean 'common'?", message)

    def test_unknown_configuration_option_is_not_silently_ignored(self):
        from stlmc.exceptions import NotSupportedError
        from stlmc.parser.config_visitor import ConfigVisitor

        with tempfile.NamedTemporaryFile("w", suffix=".cfg") as config_file:
            config_file.write("common { timebounds = 30 }")
            config_file.flush()
            with self.assertRaises(NotSupportedError) as raised:
                ConfigVisitor().parse_from_file(config_file.name)
        message = str(raised.exception)
        self.assertIn("{}:1:10".format(config_file.name), message)
        self.assertIn("unknown option 'timebounds'", message)
        self.assertIn("did you mean 'time-bound'?", message)

    def test_undefined_configuration_parent_has_location(self):
        from stlmc.exceptions import NotSupportedError
        from stlmc.parser.config_visitor import ConfigVisitor

        with tempfile.NamedTemporaryFile("w", suffix=".cfg") as config_file:
            config_file.write("common extends missing { bound = 1 }")
            config_file.flush()
            with self.assertRaises(NotSupportedError) as raised:
                ConfigVisitor().parse_from_file(config_file.name)
        message = str(raised.exception)
        self.assertIn("{}:1:16".format(config_file.name), message)
        self.assertIn("parent section 'missing' is not defined", message)

    def test_invalid_boolean_configuration_value_lists_choices(self):
        from stlmc.parser.config_visitor import ConfigVisitor

        with tempfile.NamedTemporaryFile("w", suffix=".cfg") as config_file:
            config_file.write('common { parallel = "yes" }')
            config_file.flush()
            with self.assertRaises(ValueError) as raised:
                ConfigVisitor().parse_from_file(config_file.name)
        message = str(raised.exception)
        self.assertIn("{}:1:10".format(config_file.name), message)
        self.assertIn("invalid value", message)
        self.assertIn("boolean option 'parallel'", message)
        self.assertIn("choose one of: false, true", message)

    def test_invalid_typed_configuration_value_keeps_source_location(self):
        from stlmc.parser.checker import check_validity
        from stlmc.parser.config_visitor import ConfigVisitor

        default_path = PROJECT_ROOT / "src" / "stlmc" / "default.cfg"
        config = ConfigVisitor().parse_from_file(str(default_path))
        with tempfile.NamedTemporaryFile("w", suffix=".cfg") as config_file:
            config_file.write('common { threshold = "many" }')
            config_file.flush()
            config = ConfigVisitor().parse_from_file(config_file.name, config)
            with self.assertRaises(ValueError) as raised:
                check_validity(config)
        message = str(raised.exception)
        self.assertIn("{}:1:10".format(config_file.name), message)
        self.assertIn("invalid value 'many' for option 'threshold'", message)
        self.assertIn("expected float", message)

    def test_visualization_syntax_error_has_actionable_context(self):
        from stlmc.parser.visualize_visitor import VisualizeConfigParser

        self.assert_syntax_diagnostic(
            VisualizeConfigParser().read,
            "{ output = @ group { } }",
            "visualization configuration",
        )

    def test_unsupported_visualization_output_lists_choices_and_location(self):
        from stlmc.parser.visualize_visitor import VisualizeConfigParser

        with tempfile.NamedTemporaryFile("w", suffix=".cfg") as config_file:
            config_file.write("{ output = png }")
            config_file.flush()
            with self.assertRaises(ValueError) as raised:
                VisualizeConfigParser().read(config_file.name)
        message = str(raised.exception)
        self.assertIn("{}:1:12".format(config_file.name), message)
        self.assertIn("unsupported visualization output 'png'", message)
        self.assertIn("choose one of: html, pdf", message)


if __name__ == "__main__":
    unittest.main()
