from .aux import symbolic_interval
from ....constraints.aux.operations import *


def global_clk_subst(max_depth: int) -> Dict[int, VarSubstitution]:
    clk_dict: Dict[int, VarSubstitution] = dict()

    cur_depth = 1
    while cur_depth <= max_depth:
        clk_dict[cur_depth] = _global_clk_subst_at(cur_depth)
        cur_depth += 1

    return clk_dict


def _global_clk_subst_at(cur_depth: int) -> VarSubstitution:
    interval = symbolic_interval(cur_depth)

    subst = VarSubstitution()
    subst.add(sup(interval), global_clk())
    return subst


def global_clk():
    return Real("g@clk")


def is_global_clk_in(formula: Formula) -> bool:
    return global_clk() in get_vars(formula)