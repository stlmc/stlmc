import asyncio
import os
import random
from functools import singledispatch

from yices import *

from constraints.constraints import *
from constraints.operations import get_vars, reverse_inequality, diff, \
    substitution_zero2t, reduce_not
from constraints.translation import make_forall_consts, make_dynamics_consts
from exception.exception import NotSupportedError
from solver.abstract_solver import SMTSolver
from tree.operations import size_of_tree


class YicesSolver(SMTSolver):
    def __init__(self):
        SMTSolver.__init__(self)
        self._yices_model = None
        self._cache = list()
        self._logic_list = ["QF_LRA", "QF_NRA"]
        self._logic = "QF_NRA"
        self.set_time("solving timer", 0)

    def set_logic(self, logic_name: str):
        self._logic = (logic_name.upper() if logic_name.upper() in self._logic_list else 'QF_NRA')

    def get_declared_variables(self, consts):
        declare_list = list()
        all_vars = set()

        for i in consts:
            all_vars = all_vars.union(get_vars(i))

        all_vars_list = [c for c in all_vars if not isinstance(c, Integral)]
        all_vars_list = sorted(all_vars_list, key=lambda x: x.id)

        # variables declaration
        for i in all_vars_list:
            op = {Real: "Real", Bool: "Bool", Int: "Int"}
            if type(i) in op:
                type_str = op[type(i)]
                sub_result = "(declare-fun " + i.id + " () " + type_str + ")"
                declare_list.append(sub_result)
        # sub_result = "(declare-fun tau () Real)"
        # declare_list.append(sub_result)

        return declare_list

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

        declares = self.get_declared_variables(consts)
        results = list()

        for c in consts:
            results.append(yicesObj(c))

        str_file_name = "yices_model" + str(random.random())
        with open(str_file_name + ".smt2", 'w') as model_file:
            model_file.write("(set-logic {})\n".format(self._logic))
            model_file.write("\n".join(declares))
            model_file.write("\n")
            assertion = "(assert (and"
            for i in results:
                assertion = assertion + " " + i
            assertion = assertion + "))"
            model_file.write(assertion + "\n")
            model_file.write("(check-sat)\n")
            model_file.write("(get-model)\n")
            model_file.write("(exit)\n")

        model_file_name = "{}.smt2".format(str_file_name)
        proc = await asyncio.create_subprocess_exec(
            'yices-smt2', model_file_name,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE)

        logger.start_timer("solving timer")
        stdout, stderr = await proc.communicate()
        logger.stop_timer("solving timer")
        self.reset_time("solving timer")
        self.set_time("solving timer", logger.get_duration_time("solving timer"))
        stdout_str = stdout.decode()[len("Solution:\n"):-1]
        stderr_str = stderr.decode()
        # output_str = "{}\n{}".format(stdout_str, stderr_str)
        output_str = stdout.decode()

        if os.path.isfile(model_file_name):
            os.remove(model_file_name)
        '''
        batcmd = "yices-smt2 " + model_file_name
        p = subprocess.check_output(batcmd, shell = True)
        output_str = p.decode("utf-8")[:-1]
        print(output_str)
        '''

        # print(output_str)
        if "unsat" in output_str:
            result = "True"
        elif "sat" in output_str:
            result = "False"
        else:
            result = "Unknown"

        return result, None

    def solve(self, all_consts=None, info_dict=None, boolean_abstract=None):
        size = 0
        if all_consts is not None:
            self._cache.append(all_consts)
            size = size_of_tree(all_consts)
        result, self._yices_model = self.yicescheckSat(self._cache, self._logic)
        return result, size

    def make_assignment(self):
        pass

    def clear(self):
        self._cache = list()

    def simplify(self, consts):
        pass

    def substitution(self, const, *dicts):
        pass

    def add(self, const):
        pass



# def new_yicesObj(const: Constraint):
#     indicator = False
#     indicator_depth = -1
#     parent = None
#
#     def turn_off_indicator():
#         return False, -1, None
#
#     def turn_on_indicator(_ind: bool, _ind_depth: int, _parent):
#         return _ind, _ind_depth, _parent
#
#     queue = list()
#     waiting_queue = list()
#
#     waiting_queue.append(const)
#     queue.append((0, const, None))
#     level = 0
#     while len(waiting_queue) > 0:
#         n = waiting_queue.pop(0)
#         if isinstance(n, NonLeaf):
#             level += 1
#             for c in n.children:
#                 waiting_queue.append(c)
#                 queue.append((level, c, n))
#
#     result = ""
#     is_first = True
#     l = None
#     while len(queue) > 0:
#         n, node, p = queue.pop(0)
#         print("node is {}\n".format(node))
#         if indicator is True:
#             # assert parent is not None
#             if parent is p and indicator_depth == n and node in l:
#                 if isinstance(node, Variable):
#                     result += "{} ".format(node.id)
#                 elif isinstance(node, Constant):
#                     if node.value == 'True':
#                         result += 'true '
#                     elif node.value == 'False':
#                         result += 'false '
#                     else:
#                         result += "{} ".format(node.value)
#             else:
#                 assert l is not None
#
#                 indicator, indicator_depth, parent = turn_off_indicator()
#                 result += ")"
#         else:
#             if isinstance(node, And):
#                 l = node.children
#                 if len(node.children) < 1:
#                     result += 'true'
#                 elif len(node.children) < 2:
#                     result += "{}".format(node.children[0])
#                 else:
#                     indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#                     result += '(and '
#             elif isinstance(node, Or):
#                 l = node.children
#                 if len(node.children) < 1:
#                     result += 'true'
#                 elif len(node.children) < 2:
#                     result += "{}".format(node.children[0])
#                 else:
#                     indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#                     result += '(or '
#             elif isinstance(node, Gt):
#                 l = node.children
#                 result += '(> '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Geq):
#                 l = node.children
#                 result += '(>= '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Lt):
#                 l = node.children
#                 result += '(< '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Leq):
#                 l = node.children
#                 result += '(<= '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Eq):
#                 l = node.children
#                 result += '(= '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Add):
#                 l = node.children
#                 result += '(+ '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Sub):
#                 l = node.children
#                 result += '(- '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Mul):
#                 l = node.children
#                 result += '(* '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Div):
#                 l = node.children
#                 result += '(/ '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Neg):
#                 l = node.children
#                 result += '(- '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Pow):
#                 # n1, node1, p1 = queue.pop(0)
#                 # n2, node2, p2 = queue.pop(0)
#                 # assert n1 == n2 and p1 is p2 and n1 is node.left and n2 is node.right
#                 #
#                 # cfg = Config()
#                 # cfg.default_config_for_logic('QF_LRA')
#                 # ctx = Context(cfg)
#                 # red_val = Terms.new_uninterpreted_term(Types.real_type(), 'red')
#                 # red = Terms.parse_term('(= red ' + y + ')')
#                 # ctx.assert_formulas([red])
#                 # status = ctx.check_context()
#                 #
#                 # if status == Status.SAT:
#                 #     model = Model.from_context(ctx, 1)
#                 #     yval = str(model.get_value(red_val))
#                 # else:
#                 #     raise NotSupportedError("something wrong in divisor of power")
#                 # cfg.dispose()
#                 # ctx.dispose()
#                 # result = '(^ ' + x + ' ' + yval + ')'
#                 # return result
#                 pass
#             elif isinstance(node, Implies):
#                 l = node.children
#                 result += '(=> '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Not):
#                 l = node.children
#                 result += '(not '
#                 indicator, indicator_depth, parent = turn_on_indicator(True, n, p)
#             elif isinstance(node, Integral):
#                 queue.insert(0, make_dynamics_consts(node.dynamics))
#             else:
#                 pass
#     return result
#
#


@singledispatch
def yicesObj(const: Constraint):
    raise NotSupportedError('Something wrong :: ' + str(const) + ":" + str(type(const)))


@yicesObj.register(RealVal)
def _(const: RealVal):
    res = str(const.value)
    if "inf" in res:
        return "9999999999"
    if "-" in res:
        return "(- 0 " + res[1:] + ")"
    return res


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
