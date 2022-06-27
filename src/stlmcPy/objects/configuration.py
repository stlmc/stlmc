from typing import Dict, Set, List, Tuple, Union

from ..exception.exception import ElementNotFoundError, NotSupportedError


class Section:
    def __init__(self):
        self.name = ""
        self.arguments: Dict[str, str] = dict()
        self.mandatory: List[str] = list()
        self.parent_names: List[str] = list()

    def has_parents(self):
        return len(self.parent_names) > 0

    def get_value(self, argument_name: str) -> str:
        if argument_name not in self.arguments:
            raise ElementNotFoundError("parameter \"{}\" does not exist in \"{}\" section".format(argument_name, self.name))
        return self.arguments[argument_name].replace("\"", "")

    def set_value(self, argument_name: str, value: str):
        if argument_name not in self.arguments:
            raise ElementNotFoundError("parameter \"{}\" does not exist in \"{}\" section".format(argument_name, self.name))
        self.arguments[argument_name] = value

    def is_argument_in(self, argument_name: str):
        return argument_name in self.arguments

    def __repr__(self):
        args_str = list()
        for k in self.arguments:
            args_str.append("  {} = {}".format(k, self.arguments[k]))

        header = "{}".format(self.name)
        if len(self.parent_names) > 0:
            header = "{} extends {}".format(self.name, " , ".join(self.parent_names))

        return "{} {{\n{}\n}}".format(header, "\n".join(args_str))


TypeCheckElement = Tuple[str, Union[str, List[str]]]


class Configuration:
    def __init__(self):
        self.sections_by_name: Dict[str, Section] = dict()
        self.mandatory_dict: Dict[str, List[str]] = dict()
        self.type_check_dict: Dict[str, TypeCheckElement] = dict()

    def set_section_mandatory_dict(self, mandatory_dict: Dict[str, List[str]]):
        self.mandatory_dict = mandatory_dict.copy()

    def set_type_check_dict(self, type_check_dict: Dict[str, TypeCheckElement]):
        self.type_check_dict = type_check_dict.copy()

    def check_mandatory(self):
        for section_name in self.mandatory_dict:
            mandatory_list = self.mandatory_dict[section_name]
            section = self.get_section(section_name)
            for mandatory_name in mandatory_list:
                try:
                    if section.get_value(mandatory_name) == "":
                        raise NotSupportedError(
                            "parameter \"{}\" is a mandatory argument of \"{}\" section".format(mandatory_name, section.name))
                except ElementNotFoundError:
                    raise NotSupportedError(
                        "\"{}\" is a mandatory argument of \"{}\" section".format(mandatory_name, section.name))

    def get_section(self, section_name: str):
        if section_name not in self.sections_by_name:
            raise ElementNotFoundError("there is no section named \"{}\"".format(section_name))
        return self.sections_by_name[section_name]

    def is_section_in(self, section_name: str):
        return section_name in self.sections_by_name

    @property
    def sections(self) -> Set[Section]:
        return set(self.sections_by_name.values())

    def add_section(self, section: Section):
        if section.name in self.sections_by_name:
            self.sections_by_name[section.name].arguments.update(section.arguments)
        else:
            self.sections_by_name[section.name] = section

    def __repr__(self):
        section_strings = list()
        for section in self.sections:
            section_strings.append(str(section))

        return "\n".join(section_strings)

    def update_dependencies(self, ordering: List[str]):
        for name in ordering:
            assert name in self.sections_by_name
            section = self.sections_by_name[name]
            if section.has_parents():
                for p_name in section.parent_names:
                    parent = self.sections_by_name[p_name]
                    section.arguments.update(parent.arguments)
