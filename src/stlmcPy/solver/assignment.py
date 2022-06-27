import abc

from ..exception.exception import NotSupportedError


def get_integral(integrals_list, i, k):
    for integral in integrals_list[i]:
        if integral.current_mode_number == k:
            return integral
    raise NotSupportedError("Finding flows failed")


def remove_prefix(src_str, prefix):
    size = len(prefix)
    return src_str[size:]


class Assignment:
    @abc.abstractmethod
    def get_assignments(self):
        pass

    @abc.abstractmethod
    def eval(self, const):
        pass
