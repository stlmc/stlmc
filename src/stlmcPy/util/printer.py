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


def pprint(const: Formula, indent: int):
    print(p_string(const, indent))


def indented_str(s: str, indent: int):
    li = [" " for _ in range(indent)]
    li.append(s)
    return "".join(li)


@singledispatch
def p_string(const: Formula, indent: int):
    return indented_str(str(const), indent)


@p_string.register(Leaf)
def _(const: Formula, indent: int):
    return indented_str(str(const), indent)


@p_string.register(Integral)
def _(const: Integral, indent: int):
    s = [
        indented_str("(integral {}".format(const.current_mode_number), indent),
        indented_str("[{}]".format(", ".join([str(v) for v in const.end_vector])), indent + 2),
        indented_str("[{}]".format(", ".join([str(v) for v in const.start_vector])), indent + 2),
        dynamics_p_string(const.dynamics, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(s)


@p_string.register(UnaryFormula)
def _(const: UnaryFormula, indent: int):
    s = [
        indented_str("{} (".format(const.type), indent),
        p_string(const.child, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(s)


@p_string.register(BinaryFormula)
def _(const: BinaryFormula, indent: int):
    s = [
        indented_str("{} (".format(const.type), indent),
        p_string(const.left, indent + 2),
        p_string(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(s)


@p_string.register(MultinaryFormula)
def _(const: MultinaryFormula, indent: int):
    s = [indented_str("{} (".format(const.type), indent)]
    for e in const.children:
        s.append(p_string(e, indent + 2))
    s.append(indented_str(")", indent))
    return "\n".join(s)


def dynamics_p_string(dynamic: Dynamics, indent: int):
    s = [indented_str("{} (".format(dynamic.type), indent)]
    li = [indented_str("{} = {}".format(v, e), indent + 2) for (v, e) in zip(dynamic.vars, dynamic.exps)]
    s.append("\n".join(li))
    s.append(indented_str(")", indent))
    return "\n".join(s)
