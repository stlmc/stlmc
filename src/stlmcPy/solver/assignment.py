import abc
from typing import Dict

from ..constraints.constraints import *
from ..exception.exception import NotSupportedError
from ..util.printer import indented_str


def get_integral(integrals_list, i, k):
    for integral in integrals_list[i]:
        if integral.current_mode_number == k:
            return integral
    raise NotSupportedError("Finding flows failed")


def remove_prefix(src_str, prefix):
    size = len(prefix)
    return src_str[size:]


class Assignment:
    true = "true"
    false = "false"
    any = "don't care"

    def __init__(self):
        self._assn_dict: Dict[Variable, Constant] = self._get_assignments()

    def __getitem__(self, key: Variable):
        return self._assn_dict[key]

    def keys(self):
        return self._assn_dict.keys()

    def values(self):
        return self._assn_dict.values()

    def items(self):
        return self._assn_dict.items()

    def __iter__(self):
        return self._assn_dict.__iter__()

    def __repr__(self):
        li = [indented_str("{} --> {}".format(v, self._assn_dict[v]), 2) for v in self._assn_dict]
        return "assn [\n{}\n]".format("\n".join(li))

    def __len__(self):
        return len(self._assn_dict)

    @abc.abstractmethod
    def _get_assignments(self):
        pass

    @abc.abstractmethod
    def eval(self, const: Formula):
        pass
