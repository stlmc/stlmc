"""Cooperative interrupt handling for solver and encoding loops."""

import threading


_interrupt_requested = threading.Event()


class StlmcInterrupted(BaseException):
    """Raised at a safe checkpoint after SIGINT requests cancellation."""


def clear_interrupt():
    _interrupt_requested.clear()


def request_interrupt():
    _interrupt_requested.set()


def raise_if_interrupted():
    if _interrupt_requested.is_set():
        raise StlmcInterrupted


def is_interrupted():
    return _interrupt_requested.is_set()
