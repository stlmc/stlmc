"""Read model metadata and configuration without running a solver."""
from ..config_schema import SECTION_TYPE_RULES
from ..parser.model_visitor import ModelVisitor
from .configuration import load_configuration


def diagnostic(error, source):
    """Adapter for parser diagnostics; never include request bodies or traces."""
    return {'source': source, 'message': getattr(error, 'summary', str(error)),
            'line': getattr(error, 'source_line', None),
            'column': getattr(error, 'source_column', None)}


def inspect_inputs(model_text='', config_text=''):
    try:
        configuration = load_configuration(config_text=config_text)
    except Exception as error:
        return {'common': None, 'goals': [], 'model_error': None,
                'diagnostics': [diagnostic(error, 'config')], 'solver_choices': []}
    section = configuration.get_section('common')
    common = {name: section.get_value(name) for name in section.arguments}
    labels, model_error, diagnostics = [], None, []
    if model_text.strip():
        try:
            _, _, _, goal_labels = ModelVisitor().parse_text(model_text)
            labels = list(dict.fromkeys(goal_labels.values()))
        except Exception as error:
            model_error = str(error)
            diagnostics.append(diagnostic(error, 'model'))
    solvers = next(rule for name, rule in SECTION_TYPE_RULES['common'] if name == 'solver')
    return {'common': common, 'goals': labels, 'model_error': model_error,
            'solver_choices': sorted(solvers), 'diagnostics': diagnostics}
