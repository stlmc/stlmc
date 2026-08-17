import sys


def _raise_keyboard_interrupt(signum, frame):
    from ..util.interrupt import StlmcInterrupted, request_interrupt

    request_interrupt()
    raise StlmcInterrupted


def main():
    # Help must not load ANTLR, Z3, dReal, or visualization modules.
    if "-h" in sys.argv[1:] or "--help" in sys.argv[1:]:
        from .parser import print_help

        return print_help(prog=sys.argv[0])

    import signal
    import traceback

    from ..driver.abstract_driver import StlModelChecker
    from ..driver.base_driver import BaseDriverFactory
    from ..exception.exception import (
        IllegalArgumentError, NotSupportedError, OperationError, ParsingError,
    )
    from ..update_check import notify_if_outdated
    from ..util.interrupt import StlmcInterrupted, clear_interrupt, is_interrupted
    from ..util.print import ExceptionPrinter

    clear_interrupt()
    notify_if_outdated()
    printer = ExceptionPrinter()
    previous_sigint_handler = None
    previous_sigterm_handler = None
    if hasattr(signal, "SIGINT"):
        previous_sigint_handler = signal.getsignal(signal.SIGINT)
        signal.signal(signal.SIGINT, _raise_keyboard_interrupt)
    if hasattr(signal, "SIGTERM"):
        previous_sigterm_handler = signal.getsignal(signal.SIGTERM)
        signal.signal(signal.SIGTERM, _raise_keyboard_interrupt)
    try:
        # default driver factory
        driver_factory = BaseDriverFactory()

        stlmc = StlModelChecker()
        stlmc.create_env(driver_factory)
        stlmc.run()
        if is_interrupted():
            raise StlmcInterrupted
    except NotSupportedError as E:
        printer.print_normal("conversion error: {}".format(E))
        return 2
    except IllegalArgumentError as E:
        printer.print_normal("argument error: {}".format(E))
        return 2
    except OperationError as E:
        printer.print_normal("operation error: {}".format(E))
    except ParsingError as E:
        printer.print_normal("parsing error: {}".format(E))
    except (KeyboardInterrupt, StlmcInterrupted):
        printer.print_normal("interrupted by user")
        return 130
    except Exception as E:
        printer.print_normal("error: {}".format(E))
        printer.print_normal(traceback.format_exc())
    finally:
        if previous_sigint_handler is not None:
            signal.signal(signal.SIGINT, previous_sigint_handler)
        if previous_sigterm_handler is not None:
            signal.signal(signal.SIGTERM, previous_sigterm_handler)
