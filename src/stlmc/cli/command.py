"""CLI command loading and layered configuration merging."""

import os.path

from .parser import build_parser
from ..exceptions import IllegalArgumentError
from ..objects.configuration import Configuration
from ..parser.config_visitor import ConfigVisitor
from ..application.configuration import load_configuration


class CliCommand:
    """Parse a CLI request and expose its fully merged configuration."""

    def __init__(self):
        self.config_visitor = ConfigVisitor()
        self.config = Configuration()
        self.built_in_names = [
            "file", "default_cfg", "model_cfg", "model_specific_cfg"
        ]
        self.parser = build_parser()
        self.arg_value_dict = {}
        self.file = ""

    def update_solver_config(self, solver_name):
        section = self.config.get_section(solver_name)
        for name in self.config_visitor.section_argument_dict[solver_name]:
            if name in self.arg_value_dict:
                section.arguments[name] = '"{}"'.format(
                    self.arg_value_dict.pop(name)
                )
        for name in self.config_visitor.section_boolean_argument_dict[solver_name]:
            if name in self.arg_value_dict:
                value = self.arg_value_dict.pop(name)
                if value != "false":
                    section.arguments[name] = '"{}"'.format(value)

    def parse(self):
        args = self.parser.parse_args()
        self._validate_input(args.file)
        self.config = self._load_configuration(args)
        self._collect_overrides(args)
        self._apply_common_overrides()

        solver_name = self.config.get_section("common").get_value("solver")
        if solver_name not in {"cvc5", "yices", "z3", "dreal", "auto"}:
            raise ValueError('"{}" is not a valid SMT solver'.format(solver_name))
        if solver_name != "auto":
            self.update_solver_config(solver_name)
        else:
            # Probe the effective requested settings, not stale defaults.
            # Shared arguments (logic) must reach every candidate before any
            # one candidate consumes them.
            overrides = dict(self.arg_value_dict)
            for backend in ("z3", "cvc5", "yices", "dreal"):
                if backend not in self.config.sections_by_name:
                    continue
                self.arg_value_dict = dict(overrides)
                self.update_solver_config(backend)
            consumed = set().union(*(
                set(self.config_visitor.section_argument_dict[backend]) |
                set(self.config_visitor.section_boolean_argument_dict[backend])
                for backend in ("z3", "cvc5", "yices", "dreal")
            ))
            self.arg_value_dict = {key: value for key, value in overrides.items() if key not in consumed}
        self._apply_missing_section_overrides(solver_name)
        self.config.check_mandatory()

    @staticmethod
    def _validate_input(file_name):
        if file_name is None:
            raise ValueError("should provide an STLmc model file path")
        if not os.path.exists(file_name):
            raise ValueError('"{}" is not a valid STLmc model file path'.format(file_name))
        if not os.path.isfile(file_name):
            raise ValueError('"{}" is not a file (please provide an STLmc model "file")'.format(file_name))

    def _load_configuration(self, args):
        return load_configuration(args.file, default_cfg=args.default_cfg,
                                  model_cfg=args.model_cfg,
                                  model_specific_cfg=args.model_specific_cfg,
                                  visitor=self.config_visitor)

    def _collect_overrides(self, args):
        for raw_name, raw_value in vars(args).items():
            if raw_name in self.built_in_names:
                if raw_name == "file":
                    self.file = raw_value
                continue
            if raw_value is None:
                continue
            name = raw_name.replace("_", "-")
            value = raw_value
            if name not in {"logic", "smt2-dir", "executable-path"}:
                value = str(value).lower()
            self.arg_value_dict[name] = value

    def _apply_common_overrides(self):
        section = self.config.get_section("common")
        for name in self.config_visitor.section_argument_dict["common"]:
            if name in self.arg_value_dict:
                section.arguments[name] = self.arg_value_dict.pop(name)
        for name in self.config_visitor.section_boolean_argument_dict["common"]:
            if name in self.arg_value_dict:
                value = self.arg_value_dict.pop(name)
                if value != "false":
                    section.arguments[name] = value

    def _apply_missing_section_overrides(self, selected_solver):
        missing_by_section = self.config_visitor.get_missing_arguments(self.config)
        for section_name in self.config_visitor.section_names:
            missing = missing_by_section.get(section_name, set())
            for name in tuple(missing):
                if name in self.arg_value_dict:
                    self.config.get_section(section_name).arguments[name] = (
                        self.arg_value_dict.pop(name)
                    )
                    missing.remove(name)

        missing_by_section = self.config_visitor.get_missing_arguments(self.config)
        for section_name, missing in missing_by_section.items():
            if section_name == selected_solver:
                raise IllegalArgumentError(
                    "should give the following arguments in order to run:\n  {}".format(
                        ",".join(missing)
                    )
                )
            print('warning: a section "{}" has missing arguments ({})'.format(
                section_name, ",".join(missing)
            ))
