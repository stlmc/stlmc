from termcolor import colored


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
