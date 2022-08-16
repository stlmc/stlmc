from typing import Dict, Tuple

from .aux import *
from ....constraints.aux.operations import Substitution
from ....constraints.constraints import *
from ....objects.goal import Goal
from ....util.printer import pprint


class StlGoal(Goal):
    def __init__(self, formula: Formula, config: Dict):
        super().__init__(formula)
        # initial bound starts from 0
        # [ 0 ... bound ]
        self._cur_bound = 0

        # check configuration
        assert "threshold" in config and "prop_dict" in config
        assert "time-bound" in config

        # type checking
        assert isinstance(config["threshold"], float)
        assert isinstance(config["time-bound"], float)
        assert isinstance(config["prop_dict"], Dict)

        self.threshold = config["threshold"]
        self.prop_dict = config["prop_dict"]
        self.tau_max = config["time-bound"]

        # build substitution for user-defined propositions
        subst = Substitution()
        for p in self.prop_dict:
            subst.add(p, self.prop_dict[p])

        # get an eps-strengthening reduced formula
        self.st_formula = strengthen_reduction(subst.substitute(self.formula), self.threshold)
        self.sub_formulas = calc_sub_formulas(self.st_formula)

        print("formula: {}".format(formula))
        for f in self.sub_formulas:
            print("{} --> {}".format(f, hash(f)))
        print("===============")

        # encoding related
        self._initial = chi(1, 1, self.st_formula)

        # cache
        self._cache: Dict[int, Dict] = dict()

    def encode(self):
        while True:
            yield self._encode()

    def _encode(self):
        b = self._cur_bound

        # already generated
        if b in self._cache:
            return self._generate_const(is_final=False), self._generate_const(is_final=True)

        # corresponding stl depth
        # b -> 2 * b + 1 and 2 * b + 2
        stl_f_d1, time_f_d1, _ = k_depth_stl_consts(self.sub_formulas, 2 * b + 1, self.tau_max)
        stl_f_d2, time_f_d2, final_f = k_depth_stl_consts(self.sub_formulas, 2 * b + 2, self.tau_max)

        const_dict = dict()
        const_dict["final"] = final_f
        const_dict["stl"] = And([stl_f_d1, time_f_d1, stl_f_d2, time_f_d2])
        const_dict["time-ordering"] = time_ordering(2 * b + 2, self.tau_max)

        # update cache
        self._cache[b] = const_dict

        t_c, t_c_f = self._generate_const(is_final=False), self._generate_const(is_final=True)

        # print
        # self._print_const(is_final=False)
        # self._print_const(is_final=True)

        # increase bound
        self._cur_bound += 1

        return t_c, t_c_f

    def _generate_const(self, is_final):
        b = self._cur_bound

        assert b in self._cache
        const_dict = self._cache[b]

        final_c = const_dict["final"]
        stl_c = const_dict["stl"]
        time_order = const_dict["time-ordering"]

        total_c = [self._initial] if b == 0 else []

        if is_final:
            total_c.extend([stl_c, final_c, time_order])
        else:
            total_c.extend([stl_c])

        return And(total_c)

    def _print_const(self, is_final):
        b = self._cur_bound

        assert b in self._cache
        const_dict = self._cache[b]

        final_c = const_dict["final"]
        stl_c = const_dict["stl"]
        time_order = const_dict["time-ordering"]

        print("stl const:")
        print("  stl:")
        pprint(stl_c, 4)

        if is_final:
            print("  final:")
            pprint(final_c, 4)

        print("  time ordering:")
        pprint(time_order, 4)


class ReachStlGoal(Goal):
    def encode(self):
        pass


def k_depth_stl_consts(sub_formulas: Set[Formula], depth: int, tau_max: float) -> Tuple[Formula, Formula, Formula]:
    left_time = is_left_time(sub_formulas)
    right_time = is_right_time(sub_formulas)

    # calculate time condition
    sup_i = symbolic_sup(depth)
    inf_i_next = symbolic_inf(depth + 1) if depth % 2 == 1 else symbolic_sup(depth + 1)

    # depth odd : closed interval (point []), depth even : open interval ()

    t_l_i = Bool("T^{}_l".format(depth))
    t_r_i = Bool("T^{}_r".format(depth))

    left_time_intersect = sup_i < RealVal(str(tau_max)) if depth % 2 == 1 else sup_i <= RealVal(str(tau_max))
    right_time_intersect = inf_i_next >= RealVal(str(tau_max))

    time_const_left = t_l_i == left_time_intersect
    time_const_right = t_r_i == right_time_intersect

    time_consts = set()
    if left_time:
        time_consts.add(time_const_left)
    if right_time:
        time_consts.add(time_const_right)

    goal_consts = set()
    for f in sub_formulas:
        is_globally = isinstance(f, GloballyFormula)
        is_finally = isinstance(f, FinallyFormula)
        if isinstance(f, Proposition):
            continue

        if is_finally or is_globally:
            goal_consts.update({symbolic_goal(f, i, depth) for i in range(1, depth + 1)})

            if is_globally:
                time_consts.update(globally_time_const(depth, f))

            if is_finally:
                time_consts.update(finally_time_const(depth, f))

        else:
            goal_consts.add(symbolic_goal(f, depth, depth))

    goal_const = And(list(goal_consts))
    time_const = And(list(time_consts))
    final_const = And([final(f, depth) for f in sub_formulas])

    return goal_const, time_const, final_const


def symbolic_goal(f: Formula, i: int, d: int):
    # if isinstance(f, Bool):
    #     assert i == d
    #     return None

    if isinstance(f, And):
        assert i == d
        # assert len(f.children) == 2
        left = chi(i, d, f)
        right = And([chi(i, i, child) for child in f.children])
        return left == right

    if isinstance(f, Or):
        assert i == d
        # assert len(f.children) == 2
        left = chi(i, d, f)
        right = Or([chi(i, i, child) for child in f.children])
        return left == right

    if isinstance(f, UntilFormula):
        assert i == d
        left = chi(i, i, f)
        right = Or([And([chi(i, i, f.left), chi(i, i, f.right), Bool("T^{}_l".format(i))]),
                    And([chi(i, i, f.left), chi(i + 1, i + 1, f)])])
        return left == right

    if isinstance(f, ReleaseFormula):
        assert i == d
        left = chi(i, i, f)
        right = Or([chi(i, i, f.left),
                    And([chi(i, i, f.right), Bool("T^{}_r".format(i))]),
                    And([chi(i, i, f.right), chi(i + 1, i + 1, f)])])
        return left == right

    if isinstance(f, GloballyFormula):
        left = chi(i, d, f)
        right = Or([And([t1(i, d, f), chi(i, d + 1, f)]), t2(i, d, f),
                    And([chi(d, d, f.child), chi(i, d + 1, f)]),
                    And([t1(i, d, f), Bool("T^{}_r".format(d))]),
                    And([t2(i, d, f), Bool("T^{}_r".format(d))]),
                    And([chi(d, d, f.child), Bool("T^{}_r".format(d))])])
        return left == right

    if isinstance(f, FinallyFormula):
        new_interval = Interval(True, RealVal("0.0"), f.local_time.left, False)
        left = chi(i, d, f)
        right = Or([And([t3(i, d, f), chi(d, d, f.child),
                         chi(i, d, GloballyFormula(new_interval, f.global_time, f.child)),
                         Bool("T^{}_l".format(d))]),
                    chi(i, d + 1, f)])
        return left == right

    raise Exception("cannot find related rule")


def globally_time_const(depth: int, f: Formula) -> Set[Formula]:
    assert isinstance(f, GloballyFormula)

    consts = set()

    sup_k = symbolic_sup(depth)
    inf_k = symbolic_inf(depth)

    sup_formula = f.local_time.right
    inf_formula = f.local_time.left
    time_interval = f.local_time

    # 1 ... depth
    for i in range(1, depth + 1):
        sup_i = symbolic_sup(i)
        inf_i = symbolic_inf(i)

        t_1 = t1(i, depth, f)
        t_2 = t2(i, depth, f)

        add_left_close = True if depth % 2 == 1 and time_interval.left_end else False
        add_right_close = True if depth % 2 == 1 and time_interval.right_end else False

        if depth % 2 == 1 and add_left_close:
            left_jk_locate = Lt(sup_k, Add(inf_i, inf_formula))
        else:
            left_jk_locate = Leq(sup_k, Add(inf_i, inf_formula))

        if depth % 2 == 1 and add_right_close:
            right_jk_locate = Gt(inf_k, Add(sup_i, sup_formula))
        else:
            right_jk_locate = Geq(inf_k, Add(sup_i, sup_formula))

        const1 = t_1 == left_jk_locate
        const2 = t_2 == right_jk_locate

        consts.add(const1)
        consts.add(const2)
    return consts


def finally_time_const(depth: int, f: Formula) -> Set[Formula]:
    assert isinstance(f, FinallyFormula)

    consts = set()
    inf_k = symbolic_inf(depth)
    # 1 ... depth

    kl_interval = True if depth % 2 == 1 and f.local_time.right_end else False

    for i in range(1, depth + 1):
        inf_i = symbolic_inf(i)

        sup_formula = f.local_time.right
        t_3 = t3(i, depth, f)

        if (not kl_interval) and i % 2 == 1:
            time_cond = Lt(Sub(inf_k, sup_formula), inf_i)
        else:
            time_cond = Leq(Sub(inf_k, sup_formula), inf_i)

        const = t_3 == time_cond
        consts.add(const)
    return consts
