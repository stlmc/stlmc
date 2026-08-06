class BasePrinter:
    def __init__(self):
        self.verbose = False
        self.debug = False

    def print_normal(self, text: str):
        print(text, flush=True)

    def print_normal_dark(self, text: str):
        print(text, flush=True)

    def print_verbose(self, text: str):
        if self.verbose:
            print(text, flush=True)

    def print_debug(self, text: str):
        if self.debug:
            print(text, flush=True)

    def print_line(self):
        print("======================================", flush=True)


class Printer(BasePrinter):
    def __init__(self):
        super().__init__()

class ExceptionPrinter(BasePrinter):
    def __init__(self):
        super().__init__()
