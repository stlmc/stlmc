from functools import singledispatch

from termcolor import colored

from ..constraints.constraints import *


class BasePrinter:
    def __init__(self, color, verbose_color, debug_color, line_color):
        self.color = color
        self.verbose_color = verbose_color
        self.debug_color = debug_color
        self.line_color = line_color
        self.verbose = False
        self.debug = False

    def print_normal(self, text: str):
        print(colored(text, self.color), flush=True)

    def print_normal_dark(self, text: str):
        print(colored(text, "white", attrs=['dark']), flush=True)

    def print_verbose(self, text: str):
        if self.verbose:
            print(colored(text, self.verbose_color), flush=True)

    def print_debug(self, text: str):
        if self.debug:
            print(colored(text, self.debug_color), flush=True)

    def print_line(self):
        print(colored("======================================", self.line_color), flush=True)


class Printer(BasePrinter):
    def __init__(self):
        super().__init__("white", "blue", "cyan", "white")


class ExceptionPrinter(BasePrinter):
    def __init__(self):
        super().__init__("red", "magenta", "grey", "white")


def indented_str(s: str, indent: int):
    li = [" " for _ in range(indent)]
    li.append(s)
    return "".join(li)


@singledispatch
def pprint(const: Formula, indent: int):
    print(indented_str(str(const), indent))


@pprint.register(Leaf)
def _(const: Formula, indent: int):
    print(indented_str(str(const), indent))


@pprint.register(Integral)
def _(const: Integral, indent: int):
    print(indented_str("(integral {}".format(const.current_mode_number), indent))
    print(indented_str("[{}]".format(", ".join([str(v) for v in const.end_vector])), indent + 2))
    print(indented_str("[{}]".format(", ".join([str(v) for v in const.start_vector])), indent + 2))
    dynamics_pprint(const.dynamics, indent + 2)
    print(indented_str(")", indent))


@pprint.register(UnaryFormula)
def _(const: UnaryFormula, indent: int):
    print(indented_str("{} (".format(const.type), indent))
    pprint(const.child, indent + 2)
    print(indented_str(")", indent))


@pprint.register(BinaryFormula)
def _(const: BinaryFormula, indent: int):
    print(indented_str("{} (".format(const.type), indent))
    pprint(const.left, indent + 2)
    pprint(const.right, indent + 2)
    print(indented_str(")", indent))


@pprint.register(MultinaryFormula)
def _(const: MultinaryFormula, indent: int):
    print(indented_str("{} (".format(const.type), indent))
    for e in const.children:
        pprint(e, indent + 2)
    print(indented_str(")", indent))


def dynamics_pprint(dynamic: Dynamics, indent: int):
    print(indented_str("{} (".format(dynamic.type), indent))
    li = [indented_str("{} = {}".format(v, e), indent + 2) for (v, e) in zip(dynamic.vars, dynamic.exps)]
    print("\n".join(li))
    print(indented_str(")", indent))
