import z3

from ..constraints.operations import *
from ..constraints.translation import make_forall_consts, make_dynamics_consts
from ..exception.exception import NotSupportedError
from ..solver.abstract_solver import SMTSolver
from ..solver.assignment import Assignment
from ..tree.operations import size_of_tree


class Z3Solver(SMTSolver):
    def __init__(self):
        SMTSolver.__init__(self)
        self._z3_model = None
        self._cache = list()
        self._cache_raw = list()
        self._logic_dict = dict()
        self._logic_dict["QF_NRA"] = "NRA"
        self._logic_dict["QF_LRA"] = "LRA"
        self._logic = "NRA"

        self.solver = None
        self.set_time("solving timer", 0)

    def set_logic(self, logic_name: str):
        self._logic = (self._logic_dict[logic_name.upper()] if logic_name.upper() in self._logic_dict else "NRA")

    def z3checkSat(self, consts, logic):
        assert self.logger is not None
        logger = self.logger

        logger.start_timer("solving timer")
        self.solver.add(consts)

        result = self.solver.check()
        logger.stop_timer("solving timer")
        self.reset_time("solving timer")
        self.set_time("solving timer", logger.get_duration_time("solving timer"))
        str_result = str(result)

        if str_result == "sat":
            m = self.solver.model()
            result = "False"
        else:
            m = None
            result = "True" if str_result == "unsat" else "Unknown"

        return result, m

    def solve(self, all_consts=None, info_dict=None, boolean_abstract=None):
        z3_section = self.config.get_section("z3")
        logic = z3_section.get_value("logic")
        self.set_logic(logic)

        if self.solver is None:
            self.solver = z3.SolverFor(self._logic)

        if all_consts is not None:
            self._cache_raw.append(all_consts)
        else:
            all_consts = BoolVal("True")
        size = size_of_tree(And(self._cache_raw))
        result, self._z3_model = self.z3checkSat(z3Obj(all_consts), self._logic)
        return result, size

    def clear(self):
        self._cache = list()
        self._cache_raw = list()
        self.solver = z3.Solver()

    def set_time_bound(self, time_bound: str):
        pass

    def result_simplify(self):
        return z3.simplify(z3.And(self._cache))

    def simplify(self, consts):
        return z3.simplify(consts)

    def cache(self):
        return self._cache

    def add(self, const):
        self._cache_raw.append(const)
        self.solver.add(z3Obj(const))
        self.solver.push()

    def raw_add(self, const):
        self.solver.add(z3Obj(const))

    def raw_push(self):
        self.solver.push()

    def raw_pop(self):
        self.solver.pop()

    def raw_check(self):
        return self.solver.check()

    def raw_model(self):
        return Z3Assignment(self.solver.model())

    def substitution(self, const, *dicts):
        total_dict = dict()
        for i in range(len(dicts)):
            total_dict.update(dicts[i])
        substitute_list = [(z3Obj(v), z3Obj(total_dict[v])) for v in total_dict]
        return z3.substitute(z3Obj(const), substitute_list)

    def make_assignment(self):
        return Z3Assignment(self._z3_model)

    def unsat_core(self, psi, assertion_and_trace):
        trace_dict = dict()
        for (assertion, trace) in assertion_and_trace:
            # trace should be boolean var
            trace_dict[str(trace.id)] = assertion
            self.solver.assert_and_track(z3Obj(assertion), z3Obj(trace))
        # self.add(Not(psi))
        self.solver.add(z3.Not(z3.And(psi)))
        self.solver.set(':core.minimize', True)
        self.solver.check()
        unsat_cores = self.solver.unsat_core()
        result = set()
        for unsat_core in unsat_cores:
            result.add(trace_dict[str(unsat_core)])
        return result

    def add_contradict_consts(self):
        pass


class Z3Assignment(Assignment):
    def __init__(self, z3_model):
        self._z3_model = z3_model

    # solver_model_to_generalized_model
    def get_assignments(self):
        if self._z3_model is None:
            return dict()
        new_dict = dict()
        op_var_dict = {'bool': Bool, 'int': Int, 'real': Real}
        op_dict = {'bool': BoolVal, 'int': IntVal, 'real': RealVal}
        for d in self._z3_model.decls():
            var_type_str = str(d.range()).lower()
            new_var = op_var_dict[var_type_str](d.name())
            z3_val = self._z3_model[d]
            new_dict[new_var] = op_dict[var_type_str](str(z3_val).replace("?", ""))
        return new_dict

    def eval(self, const):
        if self._z3_model is None:
            raise NotSupportedError("Z3 has no model")
        return self._z3_model.eval(z3Obj(const))

    def z3eval(self, const):
        if self._z3_model is None:
            raise NotSupportedError("Z3 has no model")
        return self._z3_model.eval(const)


@singledispatch
def z3Obj(const: Constraint):
    raise NotSupportedError('Something wrong :: ' + str(const) + ":" + str(type(const)))


@z3Obj.register(RealVal)
def _(const: RealVal):
    if const.value == "inf":
        return z3.RealVal("99999")
    return z3.RealVal(const.value)


@z3Obj.register(IntVal)
def _(const: IntVal):
    if const.value == "inf":
        return z3.IntVal("99999")
    return z3.IntVal(const.value)


@z3Obj.register(BoolVal)
def _(const: BoolVal):
    if const.value == 'True':
        return z3.BoolVal(True)
    elif const.value == 'False':
        return z3.BoolVal(False)
    else:
        raise NotSupportedError("Z3 solver cannot translate this")


@z3Obj.register(Variable)
def _(const: Variable):
    op = {'bool': z3.Bool, 'real': z3.Real, 'int': z3.Int}
    return op[const.type](const.id)


@z3Obj.register(Geq)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x >= y


@z3Obj.register(Gt)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x > y


@z3Obj.register(Leq)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x <= y


@z3Obj.register(Lt)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x < y


@z3Obj.register(Eq)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x == y


@z3Obj.register(Neq)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x != y


@z3Obj.register(Add)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x + y


@z3Obj.register(Sub)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x - y


@z3Obj.register(Pow)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x ** y


@z3Obj.register(Mul)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x * y


@z3Obj.register(Div)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x / y


@z3Obj.register(Neg)
def _(const):
    x = z3Obj(const.child)
    return -x


@z3Obj.register(And)
def _(const):
    z3args = [z3Obj(c) for c in const.children]
    if len(z3args) < 1:
        return z3.BoolVal(True)
    elif len(z3args) < 2:
        return z3args[0]
    else:
        return z3.And(z3args)


@z3Obj.register(Or)
def _(const):
    z3args = [z3Obj(c) for c in const.children]
    if len(z3args) < 1:
        return z3.BoolVal(True)
    elif len(z3args) < 2:
        return z3args[0]
    else:
        return z3.Or(z3args)


@z3Obj.register(Implies)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return z3.Implies(x, y)


@z3Obj.register(Not)
def _(const):
    x = z3Obj(const.child)
    return z3.Not(x)


@z3Obj.register(Integral)
def _(const: Integral):
    return z3Obj(make_dynamics_consts(const.dynamics))


@z3Obj.register(Forall)
def _(const: Forall):
    bound_str = str(int(const.end_tau.id[4:]) - 1)

    if len(get_vars(const.const)) == 0:
        return z3Obj(const.const)

    new_forall_const = const.const
    if isinstance(const.const, Bool):
        return z3Obj(const.const)
    if get_vars(const.const) is None:
        return z3Obj(const.const)
    if isinstance(const.const, Not):
        if isinstance(const.const.child, Bool):
            return "(not " + z3Obj(const.const.child) + ")"
        if isinstance(const.const.child, Not):
            return z3Obj(const.const.child.child)
        reduced_const = reduce_not(const.const)
        new_const = z3Obj(
            Forall(const.current_mode_number, const.end_tau, const.start_tau, reduced_const, const.integral))
        return new_const
    elif isinstance(const.const, Implies):
        left = reduce_not(Not(const.const.left))
        right = const.const.right
        left_new = z3Obj(Forall(const.current_mode_number, const.end_tau, const.start_tau, left, const.integral))
        right_new = z3Obj(Forall(const.current_mode_number, const.end_tau, const.start_tau, right, const.integral))
        return "(or " + z3Obj(left_new) + " " + z3Obj(right_new) + ")"
    elif isinstance(const.const, And) or isinstance(const.const, Or):
        result = list()
        for c in const.const.children:
            if isinstance(c, Bool):
                result.append(z3Obj(c))
            elif get_vars(c) is None:
                result.append(z3Obj(c))
            else:
                result.append(
                    z3Obj(Forall(const.current_mode_number, const.end_tau, const.start_tau, c, const.integral)))

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
    return z3Obj(new_const)