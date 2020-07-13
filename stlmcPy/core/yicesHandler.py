from yices import *
import yices_api as yapi
from stlmcPy.core import error
from stlmcPy.constraints.node import *
from functools import singledispatch
from .differentiation import *


def getForallConsts(const):
    exp = const.exp

    if len(exp.getVars()) == 0:
        return exp

    # If proposition is just boolean variable, return original expression
    if not (isinstance(exp, Gt) or isinstance(exp, Numeq) or isinstance(exp, Numneq) or isinstance(exp, Ge)):
        if exp.getType() == Type.Bool:
            return exp.substitution(const.modePropDict)
        else:
            print(exp)
            print(exp.getType())
            raise Exception("Proposition constraints something wrong")

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
        subresult.append(
            Forall(const.curMode, const.propID, Gt(handlingExp, RealVal(0)), const.modePropDict, const.startDict,
                   const.endDict, const.ode, const.delta))
        subresult.append(
            Forall(const.curMode, const.propID, Lt(handlingExp, RealVal(0)), const.modePropDict, const.startDict,
                   const.endDict, const.ode, const.delta))
        result.append(Or(*subresult))
    else:
        # f(t') >= 0
        result.append(Ge(handlingExp.substitution(const.endDict), RealVal(0)))
        if isinstance(exp, Gt):
            # Check a start point of interval satisfies the proposition
            result.append(Gt(handlingExp.substitution(const.startDict), RealVal(0)))
            # Case : f(t) = 0 -> dot(f(T)) > 0, forall T in (t, t')
            result.append(Implies(handlingExp.substitution(const.startDict) == RealVal(0),
                                  Forall(const.curMode, const.propID, Gt(diffExp, RealVal(0)), const.modePropDict,
                                         const.startDict, const.endDict, const.ode, const.delta)))
            # Case : f(t') = 0 -> dot(f(T)) < 0, forall T in (t, t')
            result.append(Implies(handlingExp.substitution(const.endDict) == RealVal(0),
                                  Forall(const.curMode, const.propID, Lt(diffExp, RealVal(0)), const.modePropDict,
                                         const.startDict, const.endDict, const.ode, const.delta)))
        elif isinstance(exp, Ge):
            result.append(Ge(handlingExp.substitution(const.startDict), RealVal(0)))
            result.append(Implies(handlingExp.substitution(const.startDict) == RealVal(0),
                                  Forall(const.curMode, const.propID, Ge(diffExp, RealVal(0)), const.modePropDict,
                                         const.startDict, const.endDict, const.ode, const.delta)))
            result.append(Implies(handlingExp.substitution(const.endDict) == RealVal(0),
                                  Forall(const.curMode, const.propID, Le(diffExp, RealVal(0)), const.modePropDict,
                                         const.startDict, const.endDict, const.ode, const.delta)))

    return And(*result)


def getvarval(self):
    all_terms = self.model.collect_defined_terms()
    var_val = dict()
    for term in all_terms:
        var_val[str(Terms.get_name(term))] = self.model.get_value(term)
    return var_val


# return a check result and the Z3 constraint size
def yicescheckSat(consts, logic):
    strConsts = [yicesObj(c) for c in consts]
    cfg = Config()

    if logic != "NONE":
        cfg.default_config_for_logic(logic)
    else:
        cfg.default_config_for_logic('QF_NRA')

    ctx = Context(cfg)

    yicesConsts = [Terms.parse_term(c) for c in strConsts]

    ctx.assert_formulas(yicesConsts)

    result = ctx.check_context()
    if result == Status.SAT:
        m = Model.from_context(ctx, 1)
        result = False
    else:
        m = None
        result = True if Status.UNSAT else "Unknown"

    cfg.dispose()
    ctx.dispose()

    return (result, sizeAst(Terms.yand(yicesConsts)), m)


# return the size of the Z3 constraint
def sizeAst(node: Terms):
    if node == Terms.NULL_TERM:
        return 0
    retval = yapi.yices_term_num_children(node)
    if retval == -1:
        return 0
    else:
        return 1 + sum([sizeAst(yapi.yices_term_child(node, c)) for c in range(retval)])


@singledispatch
def yicesObj(const: Node):
    print(type(const))
    print(const)
    raise NotImplementedError('Something wrong')


@yicesObj.register(Constant)
def _(const):
    if const.getType() == Type.Bool:
        value = 'true' if const.value else 'false'
        return value
    return str(const.value)


@yicesObj.register(Variable)
def _(const):
    op = {Type.Bool: Types.bool_type(), Type.Real: Types.real_type(), Type.Int: Types.int_type()}
    x = Terms.new_uninterpreted_term(op[const.getType()], str(const.id))

    return str(const.id)


@yicesObj.register(Ge)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(>= ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Gt)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(> ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Le)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(<= ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Lt)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(< ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Numeq)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(= ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Plus)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(+ ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Minus)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(- ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Pow)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())

    cfg = Config()
    cfg.default_config_for_logic('QF_LRA')
    ctx = Context(cfg)
    red_val = Terms.new_uninterpreted_term(Types.real_type(), 'red')
    red = Terms.parse_term('(= red ' + y + ')')
    ctx.assert_formulas([red])
    status = ctx.check_context()

    if status == Status.SAT:
        model = Model.from_context(ctx, 1)
        yval = str(model.get_value(red_val))
    else:
        raise error.Exception("something wrong in divisor of power")
    cfg.dispose()
    ctx.dispose()
    result = '(^ ' + x + ' ' + yval + ')'
    return result


@yicesObj.register(Mul)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(* ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Div)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(/ ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Neg)
def _(const):
    x = yicesObj(const.child())
    result = '(- ' + str(0) + ' ' + x + ')'
    return result


@yicesObj.register(And)
def _(const):
    yicesargs = [yicesObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return 'true'
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        result = '(and ' + ' '.join(yicesargs) + ')'
        return result


@yicesObj.register(Or)
def _(const):
    yicesargs = [yicesObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return 'true'
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        result = '(or ' + ' '.join(yicesargs) + ')'
        return result


@yicesObj.register(Implies)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(=> ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Beq)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(= ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Not)
def _(const):
    x = yicesObj(const.child())
    result = '(not ' + x + ')'
    return result


@yicesObj.register(Integral)
def _(const):
    result = const.getConstraints()
    yicesresult = [yicesObj(c) for c in result]
    result = '(and ' + ' '.join(yicesresult) + ')'
    return result


@yicesObj.register(Forall)
def _(const):
    result = list()
    result.append(And(const.getCurMode(), const.propID))
    result.append(const.propID == getForallConsts(const))
    yicesresult = [yicesObj(c) for c in result]
    result = '(and ' + ' '.join(yicesresult) + ')'
    return result


@yicesObj.register(Solution)
def _(const):
    result = const.getConstraints()
    yicesresult = [yicesObj(c) for c in result]
    result = '(and ' + ' '.join(yicesresult) + ')'
    return result
