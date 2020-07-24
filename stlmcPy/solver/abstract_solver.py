import abc


class BaseSolver:

    @abc.abstractmethod
    def solve(self, all_consts, info_dict=None):
        pass

    @abc.abstractmethod
    def make_assignment(self):
        pass


class SMTSolver:
    @abc.abstractmethod
    def simplify(self, consts):
        pass

    @abc.abstractmethod
    def substitution(self, const, *dicts):
        pass
