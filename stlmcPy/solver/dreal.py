from stlmcPy.constraints.operations import get_vars, reverse_inequality, diff, \
    substitution_zero2t, reduce_not
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.assignment import Assignment, remove_prefix, get_integral
from stlmcPy.solver.abstract_solver import BaseSolver, SMTSolver
from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import get_vars, substitution_zero2t, substitution, clause, infix
from timeit import default_timer as timer

from stlmcPy.util.logger import Logger

from stlmcPy.constraints.constraints import *
from functools import singledispatch
import os 
from sympy.parsing.sympy_parser import (
    parse_expr,
    standard_transformations,
    implicit_multiplication,
)

import subprocess


class dRealSolver(SMTSolver):
    def __init__(self):
        SMTSolver.__init__(self)
        self._dreal_model = None
        self._cache = list()
        self._logic = "NRA"
        declare_list = list()

    def set_logic(self, logic_name: str):
        self._logic = (logic_name.upper() if logic_name.upper() in self._logic_list else 'NRA')

    def get_declared_variables(self, consts):
        declare_list = list()
        all_vars = set()
        clause_set = set()
        variable_range= list()
        for i in self._cache:
            clause_set = clause_set.union(clause(i))

        for c in clause_set:
            if c._range:
                variable_range.append(c)
       

        continuous_vars = set()
        time_vars = set()
        discrete_vars = set()
        integrals = set()
        consider_mode = set()
        for i in consts:
            all_vars = all_vars.union(get_vars(i))
        for i in all_vars:
            if isinstance(i, Real) and i.id.rfind("_") != i.id.find("_"):
                continuous_vars.add(Real(i.id[0:i.id.find("_")]))
            elif isinstance(i, Real) and "tau_" in i.id:
                time_vars.add(i)
            elif isinstance(i, Real) and "time_" in i.id:
                pass
            elif isinstance(i, Integral):
                if not i.current_mode_number in consider_mode:
                    consider_mode.add(i.current_mode_number)
                    integrals.add(i)
            else:
                discrete_vars.add(i)
        var_range_dict = dict()
        
        for i in continuous_vars:
            var_range_dict[i.id] = ("[", -99999, 99999, "]")
        for i in time_vars:
            var_range_dict[i.id] = ("[", -99999, 99999, "]")
        for i in variable_range:
            if i.left.id.find("_") == i.left.id.rfind("_"):
                str_id = i.left.id
            else:
                str_id = i.left.id[0:i.left.id.find("_")]
            (left_strict, lower, upper, right_strict) = var_range_dict[str_id]
            if isinstance(i, Lt) or isinstance(i, Leq):
                upper = float(i.right.value)
                if isinstance(i, Lt):
                    left_strict = "("
            else:
                lower = float(i.right.value)
                if isinstance(i, Gt):
                    right_strict = ")"
            var_range_dict[str_id] = (left_strict, lower, upper, right_strict)

        # get max bound
        max_bound = -1
        for i in time_vars:
            if "tau_" in i.id:
                cur_bound = int(i.id[i.id.find("_")+1:])
                if cur_bound > max_bound:
                    max_bound = cur_bound - 1

        # continuous variables declaration
        for i in var_range_dict:
            (left_strict, lower, upper, right_strict) = var_range_dict[i]
            range_str = "[" + str(lower) + ", " + str(upper) + "]"
            if "tau_" in i:
                if i[i.find("_")+1:] == "1":
                    time_range = "(declare-fun time_0 () Real " + range_str + ")"
                    declare_list.append(time_range)
                elif int(i[i.find("_")+1:]) <= max_bound + 1:
                    time_range = "(declare-fun time_" + str(int(i[i.find("_")+1:]) - 1) + " () Real " + range_str + ")"
                    declare_list.append(time_range)
            else:
                sub_result = "(declare-fun " + i + " () Real "
                sub_result = sub_result + range_str + ")"
                declare_list.append(sub_result)
                for j in range(max_bound+2):
                    sub_result = "(declare-fun " + i + "_" + str(j) + "_0 () Real " + range_str + ")"
                    declare_list.append(sub_result)
                    sub_result = "(declare-fun " + i + "_" + str(j) + "_t () Real " + range_str + ")"
                    if j < max_bound + 1:
                        declare_list.append(sub_result)

        # discrete variables declaration
        for i in discrete_vars:
            op = {Real : "Real", Bool : "Bool", Int : "Int"}
            type_str = op[type(i)]
            if "currentMode_" in i.id:
                type_str = "Int"
            sub_result = "(declare-fun " + i.id + " () " + type_str + ")"
            declare_list.append(sub_result)


        # ode declaration
        sub_dict = dict()
        for i in var_range_dict:
            for j in range(max_bound + 1):
                sub_dict[Real(i + "_" + str(j) + "_0")] = Real(i)
                sub_dict[Real(i + "_" + str(j) + "_t")] = Real(i)

        for cur_integral in integrals:
            sub_result = "(define-ode flow_" + str(int(cur_integral.current_mode_number) + 1) + " ("
            for i in range(len(cur_integral.dynamics.exps)):
                cur_id = cur_integral.end_vector[i].id[0:cur_integral.end_vector[i].id.find("_")]
                cur_exp = substitution(cur_integral.dynamics.exps[i], sub_dict) 
                sub = "(= d/dt[" + cur_id + "] (" + drealObj(cur_exp) + "))"
                sub_result = sub_result + " " + sub
            sub_result = sub_result + "))"
            declare_list.append(sub_result)

        return declare_list

    def add_contradict_consts(self):
        clause_set = set()
        for i in self._cache:
            clause_set = clause_set.union(clause(i))

        cons = set()
        for i in clause_set:
            if isinstance(i, BinaryFormula) and not isinstance(i, Implies) and not isinstance(i, Neq):
                if len(get_vars(i)) > 0:
                    cons.add(i)
        cons_list = list(cons)
        for i in range(len(cons_list)):
            cur_const = cons_list[i]
            for j in range(i+1, len(cons_list)):
                flag = False
                comp_const = cons_list[j]
                if len(get_vars(cur_const.left)) > 0:
                    if str(cur_const.left) == str(comp_const.left):
                        if isinstance(cur_const, Eq) and isinstance(comp_const, Eq):
                            if not str(cur_const.right) == str(comp_const.right):
                                flag = True
                        elif type(cur_const) in [Lt, Leq] and type(comp_const) in [Gt, Geq]:
                            if len(get_vars(cur_const.right)) == 0 and len(get_vars(comp_const.right)) == 0:
                                if int(parse_expr(infix(cur_const.right))) < int(parse_expr(infix(comp_const.right))):
                                    flag = True
                        elif type(cur_const) in [Gt, Geq] and type(comp_const) in [Lt, Leq]:
                            if len(get_vars(cur_const.right)) == 0 and len(get_vars(comp_const.right)) == 0:
                                if int(parse_expr(infix(cur_const.right))) > int(parse_expr(infix(comp_const.right))):
                                    flag = True
                    elif str(cur_const.left) == str(comp_const.right):
                        if type(cur_const) in [Lt, Leq] and type(comp_const) in [Lt, Leq]:
                            if len(get_vars(cur_const.right)) == 0 and len(get_vars(comp_const.left)) == 0:
                                if int(parse_expr(infix(cur_const.right))) < int(parse_expr(infix(comp_const.left))):
                                    flag = True
                        elif type(cur_const) in [Gt, Geq] and type(comp_const) in [Gt, Geq]:
                            if len(get_vars(cur_const.right)) == 0 and len(get_vars(comp_const.left)) == 0:
                                if int(parse_expr(infix(cur_const.right))) > int(parse_expr(infix(comp_const.left))):
                                    flag = True
                elif len(get_vars(cur_const.right)) > 0:
                    if str(cur_const.right) == str(comp_const.left):
                        if type(cur_const) in [Lt, Leq] and type(comp_const) in [Lt, Leq]:
                            if len(get_vars(cur_const.left)) == 0 and len(get_vars(comp_const.right)) == 0:
                                if int(parse_expr(infix(cur_const.left))) > int(parse_expr(infix(comp_const.right))):
                                    flag = True
                        elif type(cur_const) in [Gt, Geq] and type(comp_const) in [Gt, Geq]:
                            if len(get_vars(cur_const.left)) == 0 and len(get_vars(comp_const.right)) == 0:
                                if int(parse_expr(infix(cur_const.left))) < int(parse_expr(infix(comp_const.right))):
                                    flag = True
                    elif str(cur_const.right) == str(comp_const.right):
                        if type(cur_const) in [Lt, Leq] and type(comp_const) in [Gt, Geq]:
                            if len(get_vars(cur_const.left)) == 0 and len(get_vars(comp_const.left)) == 0:
                                if int(parse_expr(infix(cur_const.left))) > int(parse_expr(infix(comp_const.left))):
                                    flag = True
                        elif type(cur_const) in [Gt, Geq] and type(comp_const) in [Lt, Leq]:
                            if len(get_vars(cur_const.left)) == 0 and len(get_vars(comp_const.left)) == 0:
                                if int(parse_expr(infix(cur_const.left))) < int(parse_expr(infix(comp_const.left))):
                                    flag = True
                if flag:
                    self._cache.append(Or([Not(cur_const), Not(comp_const)]))
                        





    def drealcheckSat(self, consts, logic):
        declares = self.get_declared_variables(consts)
        results = list()

        #self.add_contradict_consts()

        for i in self._cache:
            results.append(drealObj(i))

        str_file_name = "dreal_model"
        with open(str_file_name + ".smt2", 'w') as model_file:
            model_file.write("(set-logic QF_NRA_ODE)\n")
            model_file.write("\n".join(declares))
            model_file.write("\n")
            assertion = "(assert (and"
            for i in results:
                assertion = assertion + " " + i
            assertion = assertion + "))"
            model_file.write(assertion + "\n")
            model_file.write("(check-sat)\n")
            model_file.write("(exit)\n")

        batcmd = "dReal dreal_model.smt2 --short_sat --delta_heuristic --delta --sat-prep-bool"
        p = subprocess.check_output(batcmd, shell = True)
        output = p.decode("utf-8")[:-1]
        
        if output == "unsat":
            result = True
        else:
            result = False

        return result, -1, None

    def solve(self, all_consts=None, info_dict=None, boolean_abstract=None):
        if all_consts is not None:
            self._cache.append(all_consts)
        result, size, self._dreal_model = self.drealcheckSat(self._cache, self._logic)
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

    def set_logic(self, logic_name: str):
        pass


# return the size of the Z3 constraint
'''
def sizeAst(node: Terms):
    if node == Terms.NULL_TERM:
        return 0
    retval = yapi.yices_term_num_children(node)
    if retval == -1:
        return 0
    else:
        return 1 + sum([sizeAst(yapi.yices_term_child(node, c)) for c in range(retval)])
'''

@singledispatch
def drealObj(const: Constraint):
    raise NotSupportedError('Something wrong :: ' + str(const) + ":" + str(type(const)))


@drealObj.register(RealVal)
def _(const: RealVal):
    return str(const.value)


@drealObj.register(IntVal)
def _(const: IntVal):
    return str(const.value)


@drealObj.register(BoolVal)
def _(const: BoolVal):
    if const.value == 'True':
        return 'true'
    elif const.value == 'False':
        return 'false'
    else:
        raise NotSupportedError("Z3 solver cannot translate this")


@drealObj.register(Variable)
def _(const: Variable):
    #op = {'bool': Types.bool_type(), 'real': Types.real_type(), 'int': Types.int_type()}
    #x = Terms.new_uninterpreted_term(op[const.type], str(const.id))
    if "tau_" in const.id:
        cur = const.id[const.id.find("_")+1:]
        result = Real("time_0") 
        for i in range(1, int(cur)):
            result = result + Real("time_" + str(i))
        return drealObj(result)


    return str(const.id)


@drealObj.register(Geq)
def _(const):
    #if const._range:
    #    return "true"
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(>= ' + x + ' ' + y + ')'
    return result

@drealObj.register(Gt)
def _(const):
    #if const._range:
    #    return "true"
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(> ' + x + ' ' + y + ')'
    return result


@drealObj.register(Leq)
def _(const):
    #if const._range:
    #    return "true"
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(<= ' + x + ' ' + y + ')'
    return result


@drealObj.register(Lt)
def _(const):
    #if const._range:
    #    return "true"
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(< ' + x + ' ' + y + ')'
    return result


@drealObj.register(Eq)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(= ' + x + ' ' + y + ')'
    return result


@drealObj.register(Neq)
def _(const):
    reduceNot = Not(Eq(const.left, const.right))
    return drealObj(reduceNot)


@drealObj.register(Add)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(+ ' + x + ' ' + y + ')'
    return result

@drealObj.register(Sub)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(- ' + x + ' ' + y + ')'
    return result


@drealObj.register(Pow)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)

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


@drealObj.register(Mul)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(* ' + x + ' ' + y + ')'
    return result


@drealObj.register(Div)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(/ ' + x + ' ' + y + ')'
    return result

@drealObj.register(Neg)
def _(const):
    x = drealObj(const.child)
    result = '(- ' + str(0) + ' ' + x + ')'
    return result

@drealObj.register(Sqrt)
def _(const):
    x = drealObj(const.child)
    result = '(sqrt ' + x + ')'
    return result

@drealObj.register(Sin)
def _(const):
    x = drealObj(const.child)
    result = '(sin ' + x + ')'
    return result

@drealObj.register(Cos)
def _(const):
    x = drealObj(const.child)
    result = '(cos ' + x + ')'
    return result

@drealObj.register(Tan)
def _(const):
    x = drealObj(const.child)
    result = '(/ (sin ' + x + ') (cos ' + x + '))'
    return result

@drealObj.register(Arcsin)
def _(const):
    x = drealObj(const.child)
    result = '(arcsin ' + x + ')'
    return result

@drealObj.register(Arccos)
def _(const):
    x = drealObj(const.child)
    result = '(arccos ' + x + ')'
    return result

@drealObj.register(Arctan)
def _(const):
    x = drealObj(const.child)
    result = '(/ (cos ' + x + ') (sin ' + x + '))'
    return result


@drealObj.register(And)
def _(const):
    yicesargs = [drealObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return 'true'
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        result = '(and ' + ' '.join(yicesargs) + ')'
        return result


@drealObj.register(Or)
def _(const):
    yicesargs = [drealObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return 'true'
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        result = '(or ' + ' '.join(yicesargs) + ')'
        return result


@drealObj.register(Implies)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(=> ' + x + ' ' + y + ')'
    return result


@drealObj.register(Not)
def _(const):
    x = drealObj(const.child)
    result = '(not ' + x + ')'
    return result

@drealObj.register(Integral)
def _(const: Integral):
    setting_end = "(= " + str(const.end_vector).replace(",","") + " (integral 0. "
    s = const.end_vector[0].id.find("_")
    e = const.end_vector[0].id.rfind("_")
    
    setting_end = setting_end + "time_" + const.end_vector[0].id[s+1:e] + " " + str(const.start_vector).replace(",","") + " flow_" + str(int(const.current_mode_number) + 1) + "))"

    return setting_end



@drealObj.register(Forall)
def _(const: Forall):
    cur_inv = substitution_zero2t(const.const)

    result = "(forall_t " + str(int(const.current_mode_number) + 1) + " [0 time_" + get_bound(const.const) + "] "
    result = result + "(" + drealObj(cur_inv) + "))" 
    return result

def get_bound(const):
    var_set = get_vars(const)
    cur = var_set.pop()
    
    if cur.id.find("_") == cur.id.rfind("_"):
        return cur.id[cur.id.find("_")+1:]
    else:
        return cur.id[cur.id.find("_")+1:cur.id.rfind("_")]

@singledispatch
def eval(const: Constraint):
    return const

@eval.register(Add)
def _(const: Add):
    if len(get_vars(const)) == 0:
        return RealVal(str(eval(const)))
    return "(" + eval(const.left) + " + " + eval(const.right) + ")"


@eval.register(Sub)
def _(const: Sub):
    if len(get_vars(const)) == 0:
        return RealVal(str(eval(const)))
    return "(" + eval(const.left) + " - " + eval(const.right) + ")"


@eval.register(Neg)
def _(const: Neg):
    return "(-" + eval(const.child) + ")"


@eval.register(Mul)
def _(const: Mul):
    if len(get_vars(const)) == 0:
        return RealVal(str(eval(const)))
    return "(" + eval(const.left) + " * " + eval(const.right) + ")"


@eval.register(Div)
def _(const: Div):
    if len(get_vars(const)) == 0:
        return RealVal(str(eval(const)))
    return "(" + eval(const.left) + " / " + eval(const.right) + ")"


@eval.register(Pow)
def _(const: Pow):
    if len(get_vars(const)) == 0:
        return RealVal(str(eval(const)))
    return "(" + eval(const.left) + " ** " + eval(const.right) + ")"
