import dreal
import z3
import itertools
from functools import singledispatch, update_wrapper
from .error import *
from .node import *

# https://gist.github.com/adamnew123456/9218f99ba35da225ca11
def dispatchmethod(func):
    """
    This provides for a way to use ``functools.singledispatch`` inside of a class. It has the same
    basic interface that ``singledispatch`` does:

    >>> class A:
    ...     @dispatchmethod
    ...     def handle_message(self, message):
    ...         # Fallback code...
    ...         pass
    ...     @handle_message.register(int)
    ...     def _(self, message):
    ...         # Special int handling code...
    ...         pass
    ...
    >>> a = A()
    >>> a.handle_message(42)
    # Runs "Special int handling code..."

    Note that using ``singledispatch`` in these cases is impossible, since it tries to dispatch
    on the ``self`` argument, not the ``message`` argument. This is technically a double
    dispatch, since both the type of ``self`` and the type of the second argument are used to
    determine what function to call - for example:

    >>> class A:
    ...     @dispatchmethod
    ...     def handle_message(self, message):
    ...         print('A other', message)
    ...         pass
    ...     @handle_message.register(int)
    ...     def _(self, message):
    ...         print('A int', message)
    ...         pass
    ...
    >>> class B:
    ...     @dispatchmethod
    ...     def handle_message(self, message):
    ...         print('B other', message)
    ...         pass
    ...     @handle_message.register(int)
    ...     def _(self, message):
    ...         print('B int', message)
    ...
    >>> def do_stuff(A_or_B):
    ...     A_or_B.handle_message(42)
    ...     A_or_B.handle_message('not an int')

    On one hand, either the ``dispatchmethod`` defined in ``A`` or ``B`` is used depending
    upon what object one passes to ``do_stuff()``, but on the other hand, ``do_stuff()``
    causes different versions of the dispatchmethod (found in either ``A`` or ``B``)
    to be called (both the fallback and the ``int`` versions are implicitly called).

    Note that this should be fully compatable with ``singledispatch`` in any other respects
    (that is, it exposes the same attributes and methods).
    """
    dispatcher = singledispatch(func)

    def register(type, func=None):
        if func is not None:
            return dispatcher.register(type, func)
        else:
            def _register(func):
                return dispatcher.register(type)(func)

            return _register

    def dispatch(type):
        return dispatcher.dispatch(type)

    def wrapper(inst, dispatch_data, *args, **kwargs):
        cls = type(dispatch_data)
        impl = dispatch(cls)
        return impl(inst, dispatch_data, *args, **kwargs)

    wrapper.register = register
    wrapper.dispatch = dispatch
    wrapper.registry = dispatcher.registry
    wrapper._clear_cache = dispatcher._clear_cache
    update_wrapper(wrapper, func)
    return wrapper

class dreal4Handler:
    # return a check result and the Z3 constraint size
    def __init__(self):
        self.var_dict = dict()

    def dreal4CheckSat(self, consts, logic="None"):
        #dreal.set_log_level(dreal.LogLevel.DEBUG)
        solver = dreal.Context()
        dreal4Consts = list()
        dreal4Consts=[self.dreal4Obj(c, solver) for c in consts]

        if logic != "NONE":
            #solver = z3.SolverFor(logic)
            ## Logic.QF_NRA
            solver.SetLogic(logic)
        else:
            solver.SetLogic(dreal.Logic.QF_LRA)


            #testresult = dreal.And(*dreal4Consts)
            #target_dreal_simplify = z3.simplify(dreal.And(*z3Consts))
        solver.Assert(dreal.And(*dreal4Consts))
        #solver.add(target_z3_simplify)

        #    solver.add(z3Consts)

        #    solver.set("timeout", 21600000)  #timeout : 6 hours
        #    solver.set("timeout", 7200000)
        #with open("thermoLinear.smt2", 'w') as fle:
        #    print(dreal.And(), file=fle)

        m = solver.CheckSat()
        # this case is sat
        if m is not None:
            result = False
            print(m)
            print("-----------------------")
        else:
            result = True
        #return (result, sizeAst(z3.And(*z3Consts)), m)
        solver.Exit()
        return (result, 0, m)

    # return the size of the Z3 constraint
    def sizeAst(self, node:z3.AstRef):
        return 1 + sum([sizeAst(c) for c in node.children()])


    @dispatchmethod
    def dreal4Obj(self, const:Node, ctx):
        print(type(const))
        print(const)
        raise NotImplementedError('Something wrong')

    @dreal4Obj.register(Constant)
    def _(self, const, solver):
        op = {Type.Bool: dreal.Variable.Bool, Type.Real: dreal.Variable.Real, Type.Int: dreal.Variable.Int}
        if const.getType() == Type.Bool:
            value = dreal.Formula.TRUE() if const.value else dreal.Formula.FALSE()
            return value
        else:
            return dreal.Expression(const.value)
            #value = str(const.value)
            #return dreal.Variable(value, op[const.getType()])

    @dreal4Obj.register(Variable)
    def _(self, const, solver):
        op = {Type.Bool: dreal.Variable.Bool, Type.Real: dreal.Variable.Real, Type.Int: dreal.Variable.Int}
        if str(const.id) in self.var_dict:
            return self.var_dict[str(const.id)]
        vv = dreal.Variable(str(const.id), op[const.getType()])
        solver.DeclareVariable(vv)
        self.var_dict[str(const.id)] = vv
        return vv

    @dreal4Obj.register(Ge)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return x >= y

    @dreal4Obj.register(Gt)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return x > y

    @dreal4Obj.register(Le)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return x <= y

    @dreal4Obj.register(Lt)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return x < y

    @dreal4Obj.register(Numeq)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return x == y

    @dreal4Obj.register(Plus)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return x + y

    @dreal4Obj.register(Minus)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return x - y

    @dreal4Obj.register(Pow)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return x**y

    @dreal4Obj.register(Mul)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return x * y

    @dreal4Obj.register(Div)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return x / y

    @dreal4Obj.register(Neg)
    def _(self, const, solver):
        x = self.dreal4Obj(const.child(), solver)
        return -x

    @dreal4Obj.register(And)
    def _(self, const, solver):
        dreal4Args = [self.dreal4Obj(c, solver) for c in const.children]
        if len(dreal4Args) < 1:
            return dreal.Formula.TRUE()
        elif len(dreal4Args) < 2:
            return dreal4Args[0]
        else:
            return dreal.And(*dreal4Args)

    @dreal4Obj.register(Or)
    def _(self, const, solver):
        dreal4Args = [self.dreal4Obj(c, solver) for c in const.children]
        if len(dreal4Args) < 1:
            return dreal.Formula.TRUE()
        elif len(dreal4Args) < 2:
            return dreal4Args[0]
        else:
            return dreal.Or(*dreal4Args)

    @dreal4Obj.register(Implies)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return dreal.Implies(x, y)

    @dreal4Obj.register(Beq)
    def _(self, const, solver):
        x = self.dreal4Obj(const.left(), solver)
        y = self.dreal4Obj(const.right(), solver)
        return x == y

    @dreal4Obj.register(Not)
    def _(self, const, solver):
        x = self.dreal4Obj(const.child(), solver)
        return dreal.Not(x)

    @dreal4Obj.register(Integral)
    def _(self, const, solver):
        result = []
        subDict = {}
        for i in range(len(const.endList)):
            keyIndex = str(const.endList[i]).find('_')
            keyValue = str(const.endList[i])[0:keyIndex]
            subDict[keyValue] = const.startList[i]
        if const.flowType == 'diff':
            for i in const.ode.values():
                subvariables = list(i.getVars())
                for j in range(len(subvariables)):
                    if subvariables[j] in const.ode.keys():
                        if str(const.ode[subvariables[j]]) == str(RealVal(0)):
                            pass
                        else:
                            #print(str(const.ode[subvariables[j]]))
                            raise dreal4ConstODEerror()
            substitutionExp = {}
            for i in const.ode.keys():
                substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
            for i in range(len(const.endList)):
                keyIndex = str(const.endList[i]).find('_')
                keyValue = str(const.endList[i])[0:keyIndex]
                if keyValue in substitutionExp.keys():
                    result.append(const.endList[i] == const.startList[i] + substitutionExp[keyValue] * const.time)

        elif const.flowType == 'sol':
            subDict['time'] = const.time
            substitutionExp = {}
            for i in const.ode.keys():
                substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
            for i in range(len(const.endList)):
                keyIndex = str(const.endList[i]).find('_')
                keyValue = str(const.endList[i])[0:keyIndex]
                if keyValue in substitutionExp.keys():
                    result.append(const.endList[i] == substitutionExp[keyValue])
        else:
            raise FlowTypeEerror()

        dreal4Result = [self.dreal4Obj(c, solver) for c in result]
        return dreal.And(*dreal4Result)

    @dreal4Obj.register(Forall)
    def _(self, const, solver):
        typeList = [i.getType() for i in const.condition.getVars()]
        if not(Type.Real in typeList):
            subCondition = self.dreal4Obj(const.condition.substitution(const.modeDict), solver)
            return subCondition
        else:
            endCond = self.dreal4Obj(const.condition.substitution(const.endDict), solver)
            startCond = self.dreal4Obj(const.condition.substitution(const.startDict), solver)
            return dreal.And(endCond, startCond)

    @dreal4Obj.register(Solution)
    def _(self, const, solver):
        subDict = {}
        for i in range(len(const.endList)):
            keyIndex = str(const.endList[i]).find('_')
            keyValue = str(const.endList[i])[0:keyIndex]
            subDict[keyValue] = const.startList[i]
        for i in const.ode.values():
            subvariables = list(i.getVars())
            for j in range(len(subvariables)):
                if subvariables[j] in const.ode.keys():
                    if str(const.ode[subvariables[j]]) == str(RealVal(0)):
                        pass
                    else:
                        raise dreal4ConstODEerror()
                else:
                    raise dreal4ConstODEerror()
        substitutionExp = {}
        for i in const.ode.keys():
            substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
        result = []
        for i in range(len(const.endList)):
            keyIndex = str(const.endList[i]).find('_')
            keyValue = str(const.endList[i])[0:keyIndex]
            result.append(const.endList[i] == substitutionExp[keyValue])

        dreal4Result = [dreal4Obj(c, solver) for c in result]
        return dreal.And(*dreal4Result)

