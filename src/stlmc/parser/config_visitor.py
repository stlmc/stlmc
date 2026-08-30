from difflib import get_close_matches
from pathlib import Path
from typing import Dict, List, Set, Union

from lark import Lark, Transformer
from lark.exceptions import VisitError

from ..config_schema import (
    SECTION_BOOLEAN_OPTIONS, SECTION_MANDATORY_OPTIONS, SECTION_NAMES,
    SECTION_TYPE_RULES, SECTION_VALUE_OPTIONS, all_boolean_options,
    all_value_options,
)
from ..exceptions import IllegalArgumentError, NotSupportedError
from ..objects.configuration import Configuration, Section
from .syntax_error import parse_file


_PARSER = Lark.open(
    str(Path(__file__).with_name("grammars") / "config.lark"),
    parser="lalr", start="start", propagate_positions=True,
)


class _ConfigTransformer(Transformer):
    def quoted_value(self, children):
        return str(children[0])

    def scalar_value(self, children):
        return str(children[0])

    def assignment(self, children):
        return children[0], children[1] if len(children) > 1 else ""

    def name_list(self, children):
        return children

    def basic_section(self, children):
        return children[0], [], children[1:]

    def extended_section(self, children):
        return children[0], children[1], children[2:]

    def start(self, children):
        return children


class ConfigVisitor:
    def __init__(self):
        self.config = Configuration()
        self.section_argument_dict = {
            section: set(SECTION_VALUE_OPTIONS[section]) for section in SECTION_NAMES
        }
        self.section_boolean_argument_dict = {
            section: set(SECTION_BOOLEAN_OPTIONS[section]) for section in SECTION_NAMES
        }
        self.type_check_dict = {
            section: set(SECTION_TYPE_RULES[section]) for section in SECTION_NAMES
        }
        self.section_names: List[str] = list(SECTION_NAMES)
        self.section_mandatory_dict = {
            section: set(SECTION_MANDATORY_OPTIONS[section]) for section in SECTION_NAMES
        }
        self.section_selectable_dict: Dict[str, List[Set[str]]] = {
            section: [] for section in SECTION_NAMES
        }

    def get_missing_arguments(self, config: Configuration) -> Dict[str, Set[str]]:
        missing_dict = {}
        for section in config.sections:
            if section.name not in self.section_names:
                raise IllegalArgumentError(
                    '"{}" is not a valid section name'.format(section.name)
                )
            choices = self.section_selectable_dict[section.name]
            if any(choice.issubset(section.arguments) for choice in choices):
                continue
            missing = self.section_mandatory_dict[section.name].difference(
                section.arguments
            )
            if missing:
                missing_dict[section.name] = missing
        return missing_dict

    def generate_cmd_args(self):
        return all_value_options(), all_boolean_options()

    def parse_from_file(
        self, file_name: str, base: Union[Configuration, None] = None
    ) -> Configuration:
        self.config = base if base is not None else Configuration()
        tree = parse_file(
            _PARSER, file_name, description="configuration",
            keywords=self.section_names,
        )

        try:
            sections = _ConfigTransformer().transform(tree)
        except VisitError as error:
            raise error.orig_exc from error

        for name_token, parent_tokens, assignments in sections:
            name = str(name_token)
            if name not in self.section_names:
                close = get_close_matches(name, self.section_names, n=1, cutoff=0.8)
                suggestion = "; did you mean {!r}?".format(close[0]) if close else ""
                raise NotSupportedError(
                    "{}:{}:{}: unknown configuration section {!r}{}".format(
                        file_name, name_token.line, name_token.column, name, suggestion
                    )
                )
            parent_names = [str(token) for token in parent_tokens]
            allowed_arguments = (
                self.section_argument_dict[name]
                | self.section_boolean_argument_dict[name]
            )
            arguments = {}
            argument_locations = {}
            for argument_token, value in assignments:
                argument = str(argument_token)
                if argument not in allowed_arguments:
                    close = get_close_matches(
                        argument, allowed_arguments, n=1, cutoff=0.75
                    )
                    suggestion = (
                        "; did you mean {!r}?".format(close[0]) if close else ""
                    )
                    raise NotSupportedError(
                        "{}:{}:{}: unknown option {!r} in section {!r}{}".format(
                            file_name, argument_token.line, argument_token.column,
                            argument, name, suggestion,
                        )
                    )
                arguments[argument] = value
                argument_locations[argument] = (
                    file_name, argument_token.line, argument_token.column
                )
                if argument in self.section_boolean_argument_dict[name]:
                    normalized = str(value).strip('"').lower()
                    if normalized not in {"true", "false"}:
                        raise ValueError(
                            "{}:{}:{}: invalid value {!r} for boolean option {!r}; "
                            "choose one of: false, true".format(
                                file_name, argument_token.line,
                                argument_token.column, str(value), argument,
                            )
                        )
            section = Section()
            section.name = name
            section.parent_names.extend(parent_names)
            section.mandatory.extend(self.section_mandatory_dict[name])
            for parent_token, parent_name in zip(parent_tokens, parent_names):
                parent = self.config.sections_by_name.get(parent_name)
                if parent is None:
                    raise NotSupportedError(
                        "{}:{}:{}: parent section {!r} is not defined".format(
                            file_name, parent_token.line, parent_token.column,
                            parent_name,
                        )
                    )
                section.arguments.update(parent.arguments)
                section.argument_locations.update(parent.argument_locations)
            section.arguments.update(arguments)
            section.argument_locations.update(argument_locations)
            section.arguments = {
                key: value for key, value in section.arguments.items() if value != ""
            }
            section.argument_locations = {
                key: location for key, location in section.argument_locations.items()
                if key in section.arguments
            }
            self.config.add_section(section)

        self.config.set_section_mandatory_dict(self.section_mandatory_dict)
        self.config.set_type_check_dict(self.type_check_dict)
        return self.config
