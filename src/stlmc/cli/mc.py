from ..driver.abstract_driver import *
from ..driver.base_driver import *
from ..exception.exception import *
from ..util.print import *
import signal
import traceback
from ..update_check import notify_if_outdated


def _raise_keyboard_interrupt(signum, frame):
    raise KeyboardInterrupt


def main():
    notify_if_outdated()
    printer = ExceptionPrinter()
    previous_sigterm_handler = None
    if hasattr(signal, "SIGTERM"):
        previous_sigterm_handler = signal.getsignal(signal.SIGTERM)
        signal.signal(signal.SIGTERM, _raise_keyboard_interrupt)
    try:
        # default driver factory
        driver_factory = BaseDriverFactory()

        stlmc = StlModelChecker()
        stlmc.create_env(driver_factory)
        stlmc.run()
    except NotSupportedError as E:
        printer.print_normal("system error: {}".format(E))
    except OperationError as E:
        printer.print_normal("operation error: {}".format(E))
    except ParsingError as E:
        printer.print_normal("parsing error: {}".format(E))
    except KeyboardInterrupt:
        printer.print_normal("interrupted by user")
        return 130
    except Exception as E:
        printer.print_normal("error: {}".format(E))
        printer.print_normal(traceback.format_exc())
    finally:
        if previous_sigterm_handler is not None:
            signal.signal(signal.SIGTERM, previous_sigterm_handler)
