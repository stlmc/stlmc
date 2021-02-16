import asyncio
import os
import random
from functools import singledispatch

from yices import *

from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import get_vars, reverse_inequality, diff, \
    substitution_zero2t, reduce_not
from stlmcPy.constraints.translation import make_forall_consts, make_dynamics_consts
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.abstract_solver import SMTSolver
from stlmcPy.solver.assignment import Assignment
from stlmcPy.tree.operations import size_of_tree


class YicesAssignment(Assignment):
    def __init__(self, _yices_model):
        self._yices_model = _yices_model

    # solver_model_to_generalized_model
    def get_assignments(self):
        new_dict = dict()
        for e in self._yices_model.collect_defined_terms():
            if Terms.is_real(e):
                new_dict[Real(Terms.to_string(e))] = RealVal(str(self._yices_model.get_float_value(e)))
            elif Terms.is_int(e):
                new_dict[Int(Terms.to_string(e))] = IntVal(str(self._yices_model.get_integer_value(e)))
            elif Terms.is_bool(e):
                new_dict[Bool(Terms.to_string(e))] = BoolVal(str(self._yices_model.get_bool_value(e)))
            else:
                NotSupportedError("cannot generate assignments")
        return new_dict
        # new_dict = dict()
        # op_var_dict = {'bool': Bool, 'int': Int, 'real': Real}
        # op_dict = {'bool': BoolVal, 'int': IntVal, 'real': RealVal}
        # for d in self._z3_model.decls():
        #     var_type_str = str(d.range()).lower()
        #     new_var = op_var_dict[var_type_str](d.name())
        #     z3_val = self._z3_model[d]
        #     new_dict[new_var] = op_dict[var_type_str](str(z3_val))
        # return new_dict

    def eval(self, const):
        pass
        # if self._z3_model is None:
        #     raise NotSupportedError("Z3 has no model")
        # return self._z3_model.eval(z3Obj(const))


class YicesSolver(SMTSolver):
    def __init__(self):
        SMTSolver.__init__(self)
        self._yices_model = None
        self._cache = list()
        self._logic_list = ["QF_LRA", "QF_NRA"]
        self._logic = "QF_NRA"

    def set_logic(self, logic_name: str):
        self._logic = (logic_name.upper() if logic_name.upper() in self._logic_list else 'QF_NRA')

    async def _run(self, consts, logic):
        try:
            return await asyncio.wait_for(self._yicescheckSat(consts, logic), timeout=100000000.0)
        except asyncio.TimeoutError:
            print('timeout!')

    def yicescheckSat(self, consts, logic):
        return asyncio.run(self._run(consts, logic))


    async def _yicescheckSat(self, consts, logic):
        assert self.logger is not None
        logger = self.logger

        cfg = Config()

        # TODO : current logic input is LRA, it should be QF_NRA
        if logic != "NONE":
            cfg.default_config_for_logic(self._logic)
        else:
            cfg.default_config_for_logic(self._logic)

        ctx = Context(cfg)
        yicesConsts = list()
        for i in range(len(consts)):
            yicesConsts.append(Terms.parse_term(consts[i]))

        logger.start_timer("solving timer")
        ctx.assert_formulas(yicesConsts)

        result = ctx.check_context()

        logger.stop_timer("solving timer")

        if result == Status.SAT:
            m = Model.from_context(ctx, 1)
            result = "False"
        else:
            m = None
            result = "True" if Status.UNSAT else "Unknown"

        cfg.dispose()
        ctx.dispose()

        return result, m



    def solve(self, all_consts=None, info_dict=None, boolean_abstract=None):
        if "logic" in self.conf_dict:
            self.set_logic(self.conf_dict["logic"])
        size = 0
        if all_consts is not None:
            #self._cache.append(all_consts)
            size = size_of_tree(all_consts)
            self._cache.append(yicesObj(all_consts))
        result, self._yices_model = self.yicescheckSat(self._cache, self._logic)
        return result, size

    def make_assignment(self):
        return YicesAssignment(self._yices_model)

    def clear(self):
        self._cache = list()

    def simplify(self, consts):
        pass

    def substitution(self, const, *dicts):
        pass

    def add(self, const):
        pass


@singledispatch
def yicesObj(const: Constraint):
    raise NotSupportedError('Something wrong :: ' + str(const) + ":" + str(type(const)))


@yicesObj.register(RealVal)
def _(const: RealVal):
    return str(const.value)


@yicesObj.register(IntVal)
def _(const: IntVal):
    return str(const.value)


@yicesObj.register(BoolVal)
def _(const: BoolVal):
    if const.value == 'True':
        return 'true'
    elif const.value == 'False':
        return 'false'
    else:
        raise NotSupportedError("Yices solver cannot translate this")


@yicesObj.register(Variable)
def _(const: Variable):
    op = {'bool': Types.bool_type(), 'real': Types.real_type(), 'int': Types.int_type()}
    x = Terms.new_uninterpreted_term(op[const.type], str(const.id))

    return str(const.id)


@yicesObj.register(Geq)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(>= ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Gt)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(> ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Leq)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(<= ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Lt)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(< ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Eq)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(= ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Neq)
def _(const):
    reduceNot = Not(Eq(const.left, const.right))
    return yicesObj(reduceNot)


@yicesObj.register(Add)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(+ ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Sub)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(- ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Pow)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)

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
        raise NotSupportedError("something wrong in divisor of power")
    cfg.dispose()
    ctx.dispose()
    result = '(^ ' + x + ' ' + yval + ')'
    return result


@yicesObj.register(Mul)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(* ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Div)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(/ ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Neg)
def _(const):
    x = yicesObj(const.child)
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
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(=> ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Not)
def _(const):
    x = yicesObj(const.child)
    result = '(not ' + x + ')'
    return result


@yicesObj.register(Integral)
def _(const: Integral):
    res = yicesObj(make_dynamics_consts(const.dynamics))

    return res

@yicesObj.register(Forall)
def _(const: Forall):
    bound_str = str(int(const.end_tau.id[4:]) - 1)

    if len(get_vars(const.const)) == 0:
        return yicesObj(const.const)

    new_forall_const = const.const
    if isinstance(const.const, Bool):
        return yicesObj(const.const)
    if get_vars(const.const) is None:
        return yicesObj(const.const)
    if isinstance(const.const, Not):
        if isinstance(const.const.child, Bool):
            return "(not " + yicesObj(const.const.child) + ")"
        if isinstance(const.const.child, Not):
            return yicesObj(const.const.child.child)
        reduced_const = reduce_not(const.const)
        new_const = yicesObj(
            Forall(const.current_mode_number, const.end_tau, const.start_tau, reduced_const, const.integral))
        return new_const
    elif isinstance(const.const, Implies):
        left = reduce_not(Not(const.const.left))
        right = const.const.right
        left_new = yicesObj(Forall(const.current_mode_number, const.end_tau, const.start_tau, left, const.integral))
        right_new = yicesObj(Forall(const.current_mode_number, const.end_tau, const.start_tau, right, const.integral))
        return "(or " + yicesObj(left_new) + " " + yicesObj(right_new) + ")"
    elif isinstance(const.const, And) or isinstance(const.const, Or):
        result = list()
        for c in const.const.children:
            if isinstance(c, Bool):
                result.append(yicesObj(c))
            elif get_vars(c) is None:
                result.append(yicesObj(c))
            else:
                result.append(
                    yicesObj(Forall(const.current_mode_number, const.end_tau, const.start_tau, c, const.integral)))

        if isinstance(const.const, Or):
            return '(or ' + ' '.join(result) + ')'
        else:
            return '(and ' + ' '.join(result) + ')'
    elif not isinstance(const.const, Bool):
        op_dict = {Gt: Gt, Geq: Geq, Lt: Lt, Leq: Leq, Eq: Eq, Neq: Neq}
        exp = Sub(const.const.left, const.const.right)
        new_forall_child_const = reverse_inequality(op_dict[const.const.__class__](exp, RealVal('0')))
        new_forall_const = make_forall_consts(
            Forall(const.current_mode_number, const.end_tau, const.start_tau, new_forall_child_const, const.integral))
    new_const = And([Eq(Real("currentMode_" + bound_str), RealVal(str(const.current_mode_number))),
                     new_forall_const])
    return yicesObj(new_const)
