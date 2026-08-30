from pathlib import Path

from lark import Lark, Transformer

from .syntax_error import parse_file


_PARSER = Lark.open(
    str(Path(__file__).with_name("grammars") / "visualize.lark"),
    parser="lalr", start="start", propagate_positions=True,
)


class _VisualizeTransformer(Transformer):
    def output(self, children):
        return "output", children[0]

    def variable_group(self, children):
        return {str(child) for child in children}

    def group_list(self, children):
        return list(children)

    def group(self, children):
        return "groups", children[0] if children else []

    def start(self, children):
        return children


class VisualizeConfigParser:
    def __init__(self):
        self.group = {}
        self.output = ""
        self.supported_outputs = {"html", "pdf"}

    def read(self, file_name):
        self.group = {}
        self.output = ""
        tree = parse_file(
            _PARSER, file_name, description="visualization configuration",
            keywords=("output", "group"),
        )
        for kind, value in _VisualizeTransformer().transform(tree):
            if kind == "output":
                output = str(value)
                if output not in self.supported_outputs:
                    raise ValueError(
                        "{}:{}:{}: unsupported visualization output {!r}; "
                        "choose one of: {}".format(
                            file_name, value.line, value.column, output,
                            ", ".join(sorted(self.supported_outputs)),
                        )
                    )
                self.output = output
            else:
                self.group = dict(enumerate(value))
        return self
