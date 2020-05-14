from .differentiation import *
from .node import *

def getForallConsts(const):
    exp = const.exp
    # Change proposition formula type to Gt or Ge
    if isinstance(exp, Lt):
        exp = Gt((exp.right() - exp.left()), RealVal(0))
    if isinstance(exp, Le):
        exp = Ge((exp.right() - exp.left()), RealVal(0))

    # If proposition is just boolean variable, return original expression
    if not (isinstance(exp, Gt) or isinstance(exp, Numeq) or isinstance(exp, Numneq) or isinstance(exp, Ge)):
        if exp.getType() == Type.Bool:
            return [exp.substitution(const.modePropDict)]
        else:
            print(exp)
            print(exp.getType())
            raise ("Proposition constraints something wrong")

    # Case Real value >(or >=) 0
    if len(exp.getVars()) == 0:
        return [exp]
    result = list()
    handlingExp = exp.left() - exp.right()
    handlingExp = handlingExp.substitution(const.modePropDict)
    substitutionExp = handlingExp.substitution(const.ode)
    diffExp = diff(substitutionExp)

    # monotone increase or decrease
    result.append(Or(Ge(diffExp, RealVal(0)), Le(diffExp, RealVal(0))))

    # Special case : a == b
    if isinstance(exp, Numeq):
        result.append(Numeq(handlingExp.substitution(const.startDict), RealVal(0)))
        result.append(Numeq(handlingExp.substitution(const.endDict), RealVal(0)))
        result.append(Numeq(diffExp, RealVal(0)))
    # Special case : a =/= b
    elif isinstance(exp, Numneq):
        subresult = list()
        subresult.append(Forall(const.curMode, const.usingPropDict, Gt(handlingExp, RealVal(0)), const.modePropDict, const.startDict, const.endDict, const.ode))
        subresult.append(Forall(const.curMode, const.usingPropDict, Lt(handlingExp, RealVal(0)), const.modePropDict, const.startDict, const.endDict, const.ode))
        result.append(Or(*subresult))
    else:
        # f(t') >= 0
        result.append(Ge(handlingExp.substitution(const.endDict), RealVal(0)))
        if isinstance(exp, Gt):
            # Check a start point of interval satisfies the proposition
            result.append(Gt(handlingExp.substitution(const.startDict), RealVal(0)))
            # Case : f(t) = 0 -> dot(f(T)) > 0, forall T in (t, t')
            result.append(Implies(handlingExp.substitution(const.startDict) == RealVal(0),
                             Forall(const.curMode, const.usingPropDict, Gt(diffExp, RealVal(0)), const.modePropDict, const.startDict, const.endDict, const.ode)))
            # Case : f(t') = 0 -> dot(f(T)) < 0, forall T in (t, t')
            result.append(Implies(handlingExp.substitution(const.endDict) == RealVal(0),
                             Forall(const.curMode, const.usingPropDict, Lt(diffExp, RealVal(0)), const.modePropDict, const.startDict, const.endDict, const.ode)))
        elif isinstance(exp, Ge):
            result.append(Ge(handlingExp.substitution(const.startDict), RealVal(0)))
            result.append(Implies(handlingExp.substitution(const.startDict) == RealVal(0),
                             Forall(const.curMode, const.usingPropDict, Ge(diffExp, RealVal(0)), const.modePropDict, const.startDict, const.endDict, const.ode)))
            result.append(Implies(handlingExp.substitution(const.endDict) == RealVal(0),
                             Forall(const.curMode, const.usingPropDict, Le(diffExp, RealVal(0)), const.modePropDict, const.startDict, const.endDict, const.ode)))
    return result

