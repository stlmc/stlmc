from ....constraints.constraints import *


class Label:
    pass


class Chi(Label):
    def __init__(self, i: int, k: int, formula: Formula):
        self.formula = formula
        self.i, self.k = i, k
        self._name = "chi^{{{},{}}}_{}".format(i, k, hash(formula))

    def __repr__(self):
        return "{} ({})".format(self._name, self.formula)

    def __hash__(self):
        return hash(self._name)

    def __eq__(self, other):
        return hash(self) == hash(other)

    def is_intermediate(self):
        return not isinstance(self.formula, Proposition)


class TimeLabel(Label):
    def __init__(self, i: int, k: int, interval: Interval, name: str):
        self.interval = interval
        self.i, self.k = i, k
        self._name = name

    def __repr__(self):
        return self._name

    def __hash__(self):
        return hash(self._name)

    def __eq__(self, other):
        return hash(self) == hash(other)


class TimeIn(TimeLabel):
    def __init__(self, i: int, k: int, interval: Interval):
        TimeLabel.__init__(self, i, k, interval,
                           "@time${}^{{{},{}}}_in".format(hash(interval), i, k))


class TimePre(TimeLabel):
    def __init__(self, i: int, k: int, interval: Interval):
        TimeLabel.__init__(self, i, k, interval,
                           "@time${}^{{{},{}}}_pre".format(hash(interval), i, k))


class TimePost(TimeLabel):
    def __init__(self, i: int, k: int, interval: Interval):
        TimeLabel.__init__(self, i, k, interval,
                           "@time${}^{{{},{}}}_post".format(hash(interval), i, k))


class TimeLast(TimeLabel):
    def __init__(self, i: int):
        TimeLabel.__init__(self, i, i, Interval(True, "tau_0", "tau_max", False),
                           "@time$^{}_last".format(i))

    