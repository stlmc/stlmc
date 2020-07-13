import abc


class BaseSolver:

    @abc.abstractmethod
    def solve(self, all_consts):
        pass
