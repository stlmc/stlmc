class NotFoundElementError(Exception):
    def __init__(self, obj, message):
        self.obj = obj
        self.message = message


class CreateObjectError(Exception):
    def __init__(self, obj):
        self.obj = obj


class OperationError(Exception):
    pass


class NotSupportedError(Exception):
    pass
