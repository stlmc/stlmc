from ..driver.abstract_driver import *
from ..driver.base_driver import *
from ..exception.exception import *
from ..util.print import *
import traceback


def main():
    printer = ExceptionPrinter()
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
    except Exception as E:
        printer.print_normal("error: {}".format(E))
        printer.print_normal(traceback.format_exc())