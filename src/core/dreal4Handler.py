import dreal
import itertools
from functools import singledispatch, update_wrapper
from .error import *
from .dreal4Node import *

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

def dreal4CheckSatPlz(consts, var_dict):
    # dreal.set_log_level(dreal.LogLevel.DEBUG)
    # print(type(consts))

    # print(consts)
    solver = dreal.Context()
    print("vardict start")
    print(var_dict)
    for k in var_dict.values():
        print(k)
        solver.DeclareVariable(k)
    print("vardict end")

    print("const loop start")
    print(dreal.And(*consts))
    solver.Assert(dreal.And(*consts))
    solver.SetLogic(dreal.Logic.QF_LRA)
    m = solver.CheckSat()
    print(m)
    solver.Exit()


class dreal4Handler:
    # return a check result and the Z3 constraint size
    def __init__(self):
        self.var_dict = dict()
        self.solver = dreal.Context()
        self.count = 0

    def dreal4CheckSat(self, consts, logic="None"):
        #dreal.set_log_level(dreal.LogLevel.DEBUG)
        #print(type(consts))
        #print(consts)
        print("plz")
        hp = [self.dreal4Obj(c) for c in consts]
        # hp.append(self.dreal4Obj(consts[39]))
        # hp.append(self.dreal4Obj(consts[40]))
        # hp.append(self.dreal4Obj(consts[38]))
        dreal4CheckSatPlz(hp, self.var_dict)
        print("plz end")



        print("const loop start")
        for l in range(len(consts)):
#        for l in range(0,38):
            print("index : " + str(l))
            print(consts[l])
            lpfp = self.dreal4Obj(consts[l])
           # print("\nsolver Assert start")
            #oob = self.dreal4Obj(c)
            #print(oob)
            # if l == 40 or l == 39 or l == 38:
            #     print("dreal print")
            #     print(lpfp)
            self.solver.Assert(lpfp)



        print("dreal check Sat")
        print(self.dreal4Obj(consts[39]))
        print(self.dreal4Obj(consts[40]))
        print("after")
        #self.solver.Assert(self.dreal4Obj(consts[38]))
        #self.solver.Assert(self.dreal4Obj(consts[39]))
        #self.solver.Assert(self.dreal4Obj(consts[40]))
            #mmm = self.solver.CheckSat()
        #    print("solver Assert end\n")
        print("loop loop loop end")

        #    print(type(c))
        #    print("\n")
        #    print(c)
        #    print("\n")
        #    print("=====================")
        #print("const loop end")
        #dreal4Consts=[self.dreal4Obj(c) for c in consts]

        if logic != "NONE":
            #solver = z3.SolverFor(logic)
            ## Logic.QF_NRA
            self.solver.SetLogic(logic)
        else:
            print("none logic")
            self.solver.SetLogic(dreal.Logic.QF_LRA)

        #print("yepopipipi")
        #print(dreal4Consts)
        #print("yepspeopseoripseor2end")

            #testresult = dreal.And(*dreal4Consts)
            #target_dreal_simplify = z3.simplify(dreal.And(*z3Consts))
        #self.solver.Assert(dreal.And(*dreal4Consts))
        #solver.add(target_z3_simplify)
        #    solver.add(z3Consts)

        #    solver.set("timeout", 21600000)  #timeout : 6 hours
        #    solver.set("timeout", 7200000)
        #with open("thermoLinear.smt2", 'w') as fle:
        #    print(dreal.And(), file=fle)

        print("hell gate is start")
        m = self.solver.CheckSat()

        print("hell gate is open")
        # this case is sat
        if m is not None:
            result = False
            print(m)
            print("-----------------------")
        else:
            result = True
        #return (result, sizeAst(z3.And(*z3Consts)), m)
        self.solver.Exit()
        return (result, 0, m)

    # return the size of the Z3 constraint
    #def sizeAst(self, node:z3.AstRef):
    #    return 1 + sum([sizeAst(c) for c in node.children()])


    @dispatchmethod
    def dreal4Obj(self, const:Node):
        print(type(const))
        print(const)
        raise NotImplementedError('Something wrong')

    @dreal4Obj.register(Constant)
    def _(self, const):
        op = {Type.Bool: dreal.Variable.Bool, Type.Real: dreal.Variable.Real, Type.Int: dreal.Variable.Int}
        if const.getType() == Type.Bool:
            value = dreal.Formula.TRUE() if const.value else dreal.Formula.FALSE()
            return value
        else:
            return dreal.Expression(const.value)
            #value = str(const.value)
            #return dreal.Variable(value, op[const.getType()])

    @dreal4Obj.register(Variable)
    def _(self, const):
        op = {Type.Bool: dreal.Variable.Bool, Type.Real: dreal.Variable.Real, Type.Int: dreal.Variable.Int}
        if str(const.id) in self.var_dict:
            return self.var_dict[str(const.id)]
        vv = dreal.Variable(str(const.id), op[const.getType()])
        self.solver.DeclareVariable(vv)
        self.var_dict[str(const.id)] = vv
        return vv

    @dreal4Obj.register(Ge)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return x >= y

    @dreal4Obj.register(Gt)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return x > y

    @dreal4Obj.register(Le)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return x <= y

    @dreal4Obj.register(Lt)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return x < y

    @dreal4Obj.register(Numeq)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return x == y

    @dreal4Obj.register(Plus)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return x + y

    @dreal4Obj.register(Minus)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return x - y

    @dreal4Obj.register(Pow)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return x**y

    @dreal4Obj.register(Mul)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return x * y

    @dreal4Obj.register(Div)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return x / y

    @dreal4Obj.register(Neg)
    def _(self, const):
        x = self.dreal4Obj(const.child())
        return -x

    @dreal4Obj.register(Sin)
    def _(self, const):
        x = self.dreal4Obj(const.child())
        return sin(x)

    @dreal4Obj.register(Cos)
    def _(self, const):
        x = self.dreal4Obj(const.child())
        return cos(x)

    @dreal4Obj.register(Tan)
    def _(self, const):
        x = self.dreal4Obj(const.child())
        return tan(x)

    @dreal4Obj.register(And)
    def _(self, const):
        dreal4Args = [self.dreal4Obj(c) for c in const.children]
        if len(dreal4Args) < 1:
            return dreal.Formula.TRUE()
        elif len(dreal4Args) < 2:
            return dreal4Args[0]
        else:
            return dreal.logical_and(*dreal4Args)

    @dreal4Obj.register(Or)
    def _(self, const):
        dreal4Args = [self.dreal4Obj(c) for c in const.children]
        if len(dreal4Args) < 1:
            return dreal.Formula.TRUE()
        elif len(dreal4Args) < 2:
            return dreal4Args[0]
        else:
            return dreal.logical_or(*dreal4Args)

    @dreal4Obj.register(Implies)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return dreal.logical_imply(x, y)

    @dreal4Obj.register(Beq)
    def _(self, const):
        x = self.dreal4Obj(const.left())
        y = self.dreal4Obj(const.right())
        return dreal.logical_iff(x, y)

    @dreal4Obj.register(Not)
    def _(self, const):
        # print("what the not")
        # print(const.child())
        # print(type(const.child()))
        # print("end of what the not")
        # if type(const.child())==And:
        #     if type(const.child().left()) == Dreal4Forall:
        #         return dreal.logical_or(const.child().left(), dreal.logical_not(const.child().right()))
        #     elif type(const.child().right()) == Dreal4Forall:
        #         return dreal.logical_or(logical_not(const.child().left()), const.child().right())
        x = self.dreal4Obj(const.child())
        return dreal.logical_not(x)

    @dreal4Obj.register(Integral)
    def _(self, const):
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

        dreal4Result = [self.dreal4Obj(c) for c in result]
        return dreal.And(*dreal4Result)

    @dreal4Obj.register(Forall)
    def _(self, const):
        typeList = [i.getType() for i in const.condition.getVars()]
        if not(Type.Real in typeList):
            subCondition = self.dreal4Obj(const.condition.substitution(const.modeDict))
            return subCondition
        else:
            endCond = self.dreal4Obj(const.condition.substitution(const.endDict))
            startCond = self.dreal4Obj(const.condition.substitution(const.startDict))
            return dreal.And(endCond, startCond)

    @dreal4Obj.register(Dreal4Forall)
    def _(self, const):
        self.count += 1
        print(self.count)
        for ct in const.curFlow.exps:
            p = self.dreal4Obj(const.props)
            var = dreal.Variable("drealTime_"+str(const.k), dreal.Variable.Real)
            print("vars id at forall")
            print(var)
            print(var.get_id())
            subProp = p
            for freeVar in p.GetFreeVariables():
                if str(freeVar) == "time":
                    subProp = p.Substitute(freeVar, var)
                    break
            for fv in subProp.GetFreeVariables():
                print(fv)
                print(fv.get_id())
            print("Dreal4Forall")
            print(subProp)
            if const.k == 0:
                tau_f = self.var_dict["tau_" + str(const.k)]
                #dTime = self.var_dict["drealTime_" + str(const.k)]
                #tau_inv = dreal.logical_and(0 <= dTime, dTime < tau_f)
                #return dreal.Formula.TRUE()
                return dreal.forall([var], dreal.logical_imply(dreal.logical_and(var >= 0, var < tau_f), subProp))
            else:
                tau_i = self.var_dict["tau_" + str(const.k - 1)]
                tau_f = self.var_dict["tau_" + str(const.k)]
                #dTime = self.var_dict["drealTime_" + str(const.k)]
                #tau_inv = dreal.logical_and(tau_i <= dTime, dTime < tau_f)
                return dreal.forall([var], dreal.logical_imply(dreal.logical_and(var >= tau_i, var < tau_f), subProp))
                # dreal.forall([var], logical_imply(logical_and(var >= tau_i, var < tau_f), fkfk)

        # TODO: find whether ccc's contVar is in the declaration part
        # if not included, declared it again
        # if included, just add.
        '''
        typeList = [i.getType() for i in const.condition.getVars()]
        if not (Type.Real in typeList):
            subCondition = self.dreal4Obj(const.condition.substitution(const.modeDict))
            return subCondition
        else:
            endCond = self.dreal4Obj(const.condition.substitution(const.endDict))
            startCond = self.dreal4Obj(const.condition.substitution(const.startDict))
            return dreal.And(endCond, startCond)
        '''

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

        dreal4Result = [dreal4Obj(c) for c in result]
        return dreal.And(*dreal4Result)

