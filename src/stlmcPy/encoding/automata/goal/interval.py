import abc

from ....constraints.aux.operations import sup, inf
from ....constraints.constraints import Real, Interval, Expr


class SymbolicInterval:
    def __init__(self, index: int, template: str):
        self.index, self._template = index, template

    @abc.abstractmethod
    def inf(self) -> Expr:
        pass

    @abc.abstractmethod
    def sup(self) -> Expr:
        pass

    def template(self) -> str:
        return self._template


class Partition(SymbolicInterval):
    def __init__(self, index: int):
        self._inf, self._sup = _inf(index), _sup(index)
        self._name = "J_{}".format(index)
        SymbolicInterval.__init__(self, index, "J")

    def __repr__(self):
        return self._name

    def __sub__(self, other):
        assert isinstance(other, Interval)
        return Subtraction(self, other)

    def inf(self) -> Expr:
        return self._inf

    def sup(self) -> Expr:
        return self._sup


class Subtraction(SymbolicInterval):
    def __init__(self, partition: Partition, interval: Interval):
        SymbolicInterval.__init__(self, partition.index, "J - {}".format(interval))
        self.partition = partition
        self.interval = interval
        self._inf, self._sup = _inf(self.index), _sup(self.index)
        self._name = "J_{} - {}".format(self.index, interval)

    def __repr__(self):
        return self._name

    def inf(self) -> Expr:
        return self._inf - sup(self.interval)

    def sup(self) -> Expr:
        return self._sup - inf(self.interval)


def equal(interval1: SymbolicInterval, interval2: SymbolicInterval) -> bool:
    return type_equivalent(interval1, interval2) and _index_equivalence(interval1, interval2)


def type_equivalent(interval1: SymbolicInterval, interval2: SymbolicInterval) -> bool:
    if isinstance(interval1, Partition) and isinstance(interval2, Partition):
        return interval1.index == interval2.index

    if isinstance(interval1, Subtraction) and isinstance(interval2, Subtraction):
        return interval1.interval == interval2.interval

    return False


def _index_equivalence(interval1: SymbolicInterval, interval2: SymbolicInterval) -> bool:
    return interval1.index == interval2.index


def _inf(num: int):
    # [tau_{num - 1}, tau_{num})
    return Real("tau_{}".format(num - 1))


def _sup(num: int):
    # [tau_{num - 1}, tau_{num})
    return Real("tau_{}".format(num))

