class ElementNotFoundError(Exception):
    pass


class CreateObjectError(Exception):
    def __init__(self, obj):
        self.obj = obj


class OperationError(Exception):
    pass


class NotSupportedError(Exception):
    pass


class IllegalArgumentError(Exception):
    pass


class ParsingError(Exception):
    pass
