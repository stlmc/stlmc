from termcolor import colored


class Printer:
    verbose_on = False
    debug_on = False

    @staticmethod
    def print_normal(text: str):
        print(colored(text, "white"), flush=True)

    @staticmethod
    def print_normal_dark(text: str):
        print(colored(text, "white", attrs=['dark']), flush=True)

    @staticmethod
    def print_verbose(text: str):
        if Printer.verbose_on:
            print(colored(text, "blue"), flush=True)

    @staticmethod
    def print_debug(text: str):
        if Printer.debug_on:
            print(colored(text, "cyan"), flush=True)

    @staticmethod
    def print_line():
        print(colored("======================================", "white"), flush=True)
