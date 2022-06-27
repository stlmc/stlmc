from functools import singledispatch

from .constraints import *
from .operations import generate_id


# We add linear order constraints for separation only

def baseCase(baseSize):
    genVar = generate_id(1, "tau_")
    return [Real(next(genVar)) for _ in range(baseSize)]


# result : partition (key : formula, value : matched partition)
# sepMap :
# bConsts : partitionConsts
def guessPartition(formula, baseCase):
    result = {}
    sepMap = {}

    # add order constraints based on base partition (ex . tau_0 < tau_1 ...) to bConst
    # _addConstOrd(baseCase, genVar, bConst, False)  # change to tau_0 <= tau_1 ...
    _guess(formula, baseCase, result, sepMap)

    return (result, sepMap)


@singledispatch
def _checkStable(f: Formula, sub_list, k):
    print(type(f))
    print(f)
    raise NotImplementedError('Something wrong')


@_checkStable.register(UnaryTemporalFormula)
def _(f: UnaryTemporalFormula, sub_list, k):
    str_list = [str(c) for c in sub_list]
    form_index = str(str_list.index(str(f.child)))

    left = str(2 * k)
    point = str(2 * k + 1)
    right = str(2 * k + 2)
    str_id = "chi_" + form_index

    # if isinstance(f.child, Bool):
    #     left = str(int((int(left) / 2) - 1))
    #     right = str(int((int(right) / 2) - 1))
    #     str_id = f.child.id
    result = list()
    result.append(Neq(Bool(str_id + "_" + left), Bool(str_id + "_" + point)))
    result.append(Neq(Bool(str_id + "_" + point), Bool(str_id + "_" + right)))

    return Or(result)


@_checkStable.register(Not)
def _(f: Not, sub_list, k):
    str_list = [str(c) for c in sub_list]
    form_index = str(str_list.index(str(f.child)))
    left = str(2 * k)
    right = str(2 * k + 2)
    str_id = "chi_" + form_index

    # if isinstance(f.child, Bool):
    #     left = str(int((int(left) / 2) - 1))
    #     right = str(int((int(right) / 2) - 1))
    #     str_id = f.child.id

    return Neq(Bool(str_id + "_" + left), Bool(str_id + "_" + right))


@_checkStable.register(BinaryTemporalFormula)
def _(f: BinaryTemporalFormula, sub_list, k):
    result = list()
    str_list = [str(c) for c in sub_list]
    lef_index = str(str_list.index(str(f.left)))
    rig_index = str(str_list.index(str(f.right)))

    left_l = str(2 * k)
    left_r = str(2 * k)
    point = str(2 * k + 1)
    right_l = str(2 * k + 2)
    right_r = str(2 * k + 2)
    left_id = "chi_" + lef_index
    right_id = "chi_" + rig_index

    # if isinstance(f.left, Bool):
    #     left_l = str(int((int(left_l) / 2) - 1))
    #     right_l = str(int((int(right_l) / 2) - 1))
    #     left_id = f.left.id
    # if isinstance(f.right, Bool):
    #     left_r = str(int((int(left_r) / 2) - 1))
    #     right_r = str(int((int(right_r) / 2) - 1))
    #     right_id = f.right.id
    result.append(Neq(Bool(left_id + "_" + left_l), Bool(left_id + "_" + point)))
    result.append(Neq(Bool(left_id + "_" + point), Bool(left_id + "_" + right_l)))
    result.append(Neq(Bool(right_id + "_" + left_r), Bool(right_id + "_" + point)))
    result.append(Neq(Bool(right_id + "_" + point), Bool(right_id + "_" + right_r)))
    return Or(result)


def check_f_t(f, sub_list, k):
    str_list = [str(c) for c in sub_list]
    form_index = str(str_list.index(str(f)))

    left = str(2 * k)
    right = str(2 * k + 2)
    str_id = "chi_" + form_index

    # if isinstance(f.child, Bool):
    #     left = str(int((int(left) / 2) - 1))
    #     right = str(int((int(right) / 2) - 1))
    #     str_id = f.child.id

    return And([Not(Bool(str_id + "_" + left)), Bool(str_id + "_" + right)])


def check_t_f(f, sub_list, k):
    str_list = [str(c) for c in sub_list]
    form_index = str(str_list.index(str(f)))

    left = str(2 * k)
    right = str(2 * k + 2)
    str_id = "chi_" + form_index

    # if isinstance(f.child, Bool):
    #     left = str(int((int(left) / 2) - 1))
    #     right = str(int((int(right) / 2) - 1))
    #     str_id = f.child.id

    return And([Bool(str_id + "_" + left), Not(Bool(str_id + "_" + right))])


def genPartition(subform, subformula_list, bound):
    consts = []
    tau_abstraction = dict()
    count = 0
    if isinstance(subform, BinaryTemporalFormula) or isinstance(subform, UnaryTemporalFormula):
        for k in range(1, bound + 2):
            left_chi = _checkStable(subform, subformula_list, k)
            right_list = list()
            for t in [subform.local_time.left, subform.local_time.right]:
                if isinstance(t, float):
                    t = RealVal(str(t))
                right_chi = list()
                right_chi.append(Eq(t, RealVal("0")))
                # if k == 0:
                #    right_chi.append(Lt((RealVal("0") - t), RealVal("0")))
                # elif k == bound + 1:
                #    right_chi.append(Lt((Real("tau_" + str(bound + 1)) - t), RealVal("0")))
                # else:
                right_chi.append(Lt((Real("tau_" + str(k)) - t), RealVal("0")))
                for j in range(1, k):
                    time_k = Real("tau_" + str(k))
                    if k == 0:
                        time_k = RealVal("0")

                    right_chi.append(Eq(time_k - t, Real("tau_" + str(j))))

                tau_abstraction[Bool("newTau_" + str(count) + "_" + str(k))] = Or(right_chi)

                if k >= (bound + 1):
                    consts.append(Bool("newTau_" + str(count) + "_" + str(k)))
                else:
                    consts.append(Implies(left_chi, Bool("newTau_" + str(count) + "_" + str(k))))
                    # right_list.append(Bool("newTau_" + str(count) + "_" + str(k - 1)))
                count += 1

            # if k < bound + 1:
            #    consts.append(Implies(left_chi, And(right_list)))
    return consts, tau_abstraction



def make_right_consts(t, k, bound, count, tau_abstraction):
    if isinstance(t, float):
        t = RealVal(str(t))
    right_chi = list()
    right_chi.append(Eq(t, RealVal("0")))
    right_chi.append(Lt((Real("tau_" + str(k)) - t), RealVal("0")))
    for j in range(1, k):
        time_k = Real("tau_" + str(k))
        right_chi.append(Eq(time_k - t, Real("tau_" + str(j))))

    tau_abstraction[Bool("newTau_" + str(count) + "_" + str(k))] = Or(right_chi)
    return Bool("newTau_" + str(count) + "_" + str(k)), tau_abstraction


@singledispatch
def _guess(formula, baseCase, result, sepMap):
    raise NotImplementedError('Something wrong')


@_guess.register(Constant)
def _(formula, baseCase, result, sepMap):
    result[formula] = set()


@_guess.register(Bool)
def _(formula, baseCase, result, sepMap):
    result[formula] = set(baseCase)


@_guess.register(Not)
def _(formula, baseCase, result, sepMap):
    _guess(formula.child, baseCase, result, sepMap)

    result[formula] = set(baseCase)


@_guess.register(MultinaryFormula)
def _(formula, baseCase, result, sepMap):
    for c in formula.children:
        _guess(c, baseCase, result, sepMap)

    result[formula] = set(baseCase)


@_guess.register(Implies)
def _(formula, baseCase, result, sepMap):
    _guess(formula.left, baseCase, result, sepMap)
    _guess(formula.right, baseCase, result, sepMap)

    result[formula] = set(baseCase)


@_guess.register(UnaryTemporalFormula)
def _(formula, baseCase, result, sepMap):
    _guess(formula.child, baseCase, result, sepMap)

    sepMap[formula] = baseCase

    result[formula] = set(baseCase)


@_guess.register(BinaryTemporalFormula)
def _(formula, baseCase, result, sepMap):
    _guess(formula.left, baseCase, result, sepMap)
    _guess(formula.right, baseCase, result, sepMap)

    sepMap[formula] = baseCase

    result[formula] = set(baseCase)
