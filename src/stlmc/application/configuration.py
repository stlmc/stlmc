"""Shared configuration loading for CLI and other STLmc clients."""
import json
from pathlib import Path

from ..exceptions import NotSupportedError
from ..parser.config_visitor import ConfigVisitor
from ..solver.availability import find_dreal


def common_overrides_text(values):
    """Serialize only explicit overrides using the existing config language."""
    values = {key: value for key, value in values.items() if value is not None}
    if not values:
        return ''
    assignments = '\n'.join('    {} = {}'.format(key, json.dumps(
        str(value).lower() if isinstance(value, bool) else value))
        for key, value in values.items())
    return '\ncommon {\n' + assignments + '\n}\n'


def load_configuration(file_name=None, *, default_cfg=None, model_cfg=None,
                       model_specific_cfg=None, config_text=None, overrides=None,
                       visitor=None):
    """Load the same default, model, and goal-specific layers as the CLI.

    Text input is the in-memory equivalent of an explicit model config. Missing
    mandatory settings are left missing so editors can display partial input;
    execution still uses the existing mandatory and typed validation.
    """
    visitor = visitor or ConfigVisitor()
    default_path = Path(default_cfg) if default_cfg is not None else Path(__file__).parents[1] / 'default.cfg'
    config = visitor.parse_from_file(str(default_path))
    if default_cfg is None:
        dreal = config.get_section('dreal')
        if dreal.get_value('executable-path') == 'dReal':
            dreal.set_value('executable-path', find_dreal() or 'dReal')
    if config_text is not None:
        config = visitor.parse_text(config_text, config, source_name='<model config>')
    else:
        if model_cfg is None and file_name is not None:
            path = Path(file_name)
            candidate = path.parent / (path.name.split('.')[0] + '.cfg')
            if candidate.exists():
                model_cfg = str(candidate)
        if model_cfg is not None:
            if not Path(model_cfg).exists():
                raise NotSupportedError('model config "{}" does not exist'.format(model_cfg))
            config = visitor.parse_from_file(str(model_cfg), config)
    if model_specific_cfg is not None:
        if not Path(model_specific_cfg).exists():
            raise NotSupportedError('model specific config "{}" does not exist'.format(model_specific_cfg))
        config = visitor.parse_from_file(str(model_specific_cfg), config)
    if overrides:
        config = visitor.parse_text(common_overrides_text(overrides), config,
                                    source_name='<explicit overrides>')
    return config
