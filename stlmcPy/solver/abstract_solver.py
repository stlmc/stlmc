import abc


class BaseSolver:

    @abc.abstractmethod
    def solve(self, all_consts, info_dict=None):
        pass

    @abc.abstractmethod
    def make_assignment(self):
        pass
