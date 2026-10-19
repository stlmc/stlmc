"""CLI and browser clients share parsers and configuration precedence."""
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from stlmc.application.configuration import load_configuration
from stlmc.application.inspection import inspect_inputs
from stlmc.cli.command import CliCommand
from stlmc.parser.config_visitor import ConfigVisitor
from stlmc.parser.model_visitor import ModelVisitor

MODEL = '''[-1,2] x; {mode:true;inv:true;flow:d/dt[x]=0;jump:}
init:x=0;proposition:[alias]:x>0;
goal:[f1]:[][0,1](x<=1); [f2]:[][0,1](x>=1);
'''


def snapshot(config):
    return {section.name: {key: section.get_value(key) for key in section.arguments}
            for section in config.sections}


class ConfigurationApiTest(unittest.TestCase):
    def test_file_and_text_parsers_have_identical_semantics(self):
        text = 'common {bound=2 time-bound=3}\nz3 {logic="QF_LRA"}\nyices extends z3 {}'
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cfg = root / 'input.cfg'; cfg.write_text(text)
            model = root / 'input.model'; model.write_text(MODEL)
            self.assertEqual(snapshot(ConfigVisitor().parse_from_file(str(cfg))),
                             snapshot(ConfigVisitor().parse_text(text)))
            file_goals = ModelVisitor().get_parse_tree(str(model))[3]
            text_goals = ModelVisitor().parse_text(MODEL)[3]
            self.assertEqual(list(file_goals.values()), list(text_goals.values()))

    def test_preview_matches_actual_cli_with_inheritance_and_repeated_sections(self):
        text = '''common {bound=2 time-bound=3 solver="dreal" goal="f2"
two-step="true" reach="false" parallel="true" parallel-core=2}
z3 {logic="QF_LRA"} yices extends z3 {} common {threshold=0.25}'''
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            model = root / 'example.model'; model.write_text(MODEL)
            cfg = root / 'example.cfg'; cfg.write_text(text)
            with mock.patch('sys.argv', ['stlmc', str(model)]):
                cli = CliCommand(); cli.parse()
            preview = inspect_inputs(MODEL, text)
            self.assertEqual(preview['common'], snapshot(cli.config)['common'])
            self.assertEqual(preview['goals'], ['f1', 'f2'])
            self.assertIsNone(preview['model_error'])
            self.assertEqual(snapshot(load_configuration(str(model))), snapshot(cli.config))
            self.assertEqual(snapshot(load_configuration(config_text=text)), snapshot(cli.config))

    def test_missing_required_values_are_not_invented(self):
        info = inspect_inputs(MODEL)
        common = load_configuration().get_section('common')
        self.assertEqual(info['common']['solver'], common.get_value('solver'))
        self.assertEqual(info['common']['threshold'], common.get_value('threshold'))
        self.assertNotIn('bound', info['common'])
        self.assertNotIn('time-bound', info['common'])
        with self.assertRaises(Exception):
            load_configuration().check_mandatory()

    def test_model_error_keeps_config_values_and_does_not_guess_goal_labels(self):
        info = inspect_inputs('goal: [fake]: invalid;', 'common {threshold=0.5}')
        self.assertTrue(info['model_error'])
        self.assertEqual(info['goals'], [])
        self.assertEqual(info['common']['threshold'], '0.5')

    def test_model_specific_layer_and_explicit_false_override(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cfg = root / 'model.cfg'; cfg.write_text('common {bound=2 time-bound=3 two-step="true"}')
            goal = root / 'goal.cfg'; goal.write_text('common {bound=4}')
            config = load_configuration(model_cfg=str(cfg), model_specific_cfg=str(goal),
                                        overrides={'two-step': False, 'threshold': 0})
            common = config.get_section('common')
            self.assertEqual(common.get_value('bound'), '4')
            self.assertEqual(common.get_value('two-step'), 'false')
            self.assertEqual(common.get_value('threshold'), '0')


if __name__ == '__main__':
    unittest.main()
