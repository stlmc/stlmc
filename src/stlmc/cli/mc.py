import sys


def _raise_keyboard_interrupt(signum, frame):
    from ..utils.interrupt import StlmcInterrupted, request_interrupt

    request_interrupt()
    raise StlmcInterrupted


def main():
    # Help must not load ANTLR, Z3, dReal, or visualization modules.
    if "-h" in sys.argv[1:] or "--help" in sys.argv[1:]:
        from .parser import print_help

        return print_help(prog=sys.argv[0])

    # Missing input is a CLI usage error. Report it before importing solver,
    # parser, numerical, and visualization dependencies.
    if len(sys.argv) == 1:
        print("error: should provide an STLmc model file path", flush=True)
        return 2

    # Validate CLI syntax and the positional model path before importing the
    # model checker. This keeps all usage errors independent of solver and UI
    # startup costs.
    import os.path
    from .parser import build_parser

    preflight_args = build_parser(prog=sys.argv[0]).parse_args(sys.argv[1:])
    if preflight_args.file is None:
        print("error: should provide an STLmc model file path", flush=True)
        return 2
    if not os.path.exists(preflight_args.file):
        print(
            'error: "{}" is not a valid STLmc model file path'.format(
                preflight_args.file
            ),
            flush=True,
        )
        return 2
    if not os.path.isfile(preflight_args.file):
        print(
            'error: "{}" is not a file (please provide an STLmc model "file")'
            .format(preflight_args.file),
            flush=True,
        )
        return 2

    config_paths = (
        ("default configuration", preflight_args.default_cfg),
        ("model configuration", preflight_args.model_cfg),
        ("model-specific configuration", preflight_args.model_specific_cfg),
    )
    for description, path in config_paths:
        if path is not None and not os.path.isfile(path):
            print(
                'error: {} file "{}" does not exist or is not a file'.format(
                    description, path
                ),
                flush=True,
            )
            return 2

    import signal
    import traceback

    from ..exceptions import (
        IllegalArgumentError, NotSupportedError, OperationError, ParsingError,
        SolverUnavailableError,
    )
    from ..update_check import notify_if_outdated
    from ..utils.interrupt import StlmcInterrupted, clear_interrupt, is_interrupted
    from ..utils.print import ExceptionPrinter

    clear_interrupt()
    notify_if_outdated()
    printer = ExceptionPrinter()
    # Z3 is also used internally by STLMC's abstraction and core-learning
    # machinery, independently of the selected continuous solver.
    try:
        import z3  # noqa: F401
    except (ImportError, OSError) as error:
        printer.print_normal(
            "solver error: Z3 is unavailable ({}). "
            "Run: stlmc-install-solvers z3".format(error)
        )
        return 3

    from ..driver.abstract_driver import StlModelChecker
    from ..driver.base_driver import BaseDriverFactory
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
    except SolverUnavailableError as E:
        printer.print_normal("solver error: {}".format(E))
        return 3
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
