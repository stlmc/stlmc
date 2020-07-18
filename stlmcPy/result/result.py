class Result:
    pass


class TrueResult(Result):
    def __repr__(self):
        return "TrueResult"


class FalseResult(Result):
    def __repr__(self):
        return "FalseResult"
