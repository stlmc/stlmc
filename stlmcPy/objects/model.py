from functools import singledispatch

from stlmcPy.constraints.constraints import *

# TODO: why attribute error occured here?
from stlmcPy.constraints.operations import make_dict, substitution, make_dictionary_for_invariant, reduce_not


@singledispatch
def make_new_dynamics(dyn: Ode, bound, mode_var_dict, range_dict, constant_dict):
    new_dynamics_dict = make_dict(bound, mode_var_dict, range_dict, constant_dict, "_0")
    new_exps = list()
    for exp in dyn.exps:
        new_exp = substitution(exp, new_dynamics_dict)
        new_exps.append(new_exp)

    new_vars_dict = make_dict(bound, {}, range_dict, {}, "_0_t")
    new_vars = list()
    for var in dyn.vars:
        new_var = substitution(var, new_vars_dict)
        new_vars.append(new_var)
    return Ode(new_vars, new_exps)


@make_new_dynamics.register(Function)
def _(dyn: Function, bound, mode_var_dict, range_dict, constant_dict):
    new_dynamics_dict = make_dict(bound, mode_var_dict, range_dict, constant_dict, "_0")
    new_dynamics_dict[Real('time')] = Real('tau_' + str(bound + 1))
    new_exps = list()
    for exp in dyn.exps:
        new_exp = substitution(exp, new_dynamics_dict)
        new_exps.append(new_exp)

    new_vars_dict = make_dict(bound, {}, range_dict, {}, "_0_t")
    new_vars = list()
    for var in dyn.vars:
        new_var = substitution(var, new_vars_dict)
        new_vars.append(new_var)
    return Function(new_vars, new_exps)


class StlMC:
    def __init__(self, mode_var_dict, range_dict, const_dict, modules, init):
        # key : string, value : object
        self.mode_var_dict = mode_var_dict
        self.range_dict = range_dict
        self.const_dict = const_dict
        self.modules = modules
        self.init = init
        self.next_str = "##$%^&$%^&##'"

    @staticmethod
    def make_additional_mode_consts(bound, current_mode_num, total_mode_num):
        additional_mode_const_children = list()
        for otherModeID in range(0, current_mode_num):
            additional_mode_const_children.append(Neq(Real('currentMode_' + str(bound)), IntVal(str(otherModeID))))
        for otherModeID in range(current_mode_num + 1, total_mode_num):
            additional_mode_const_children.append(Neq(Real('currentMode_' + str(bound)), IntVal(str(otherModeID))))

        additional_mode_const_children.append(Eq(Real('currentMode_' + str(bound)), IntVal(str(current_mode_num))))
        additional_mode_const_children.append(Lt(Real('currentMode_' + str(bound)), IntVal(str(total_mode_num))))
        additional_mode_const_children.append(Geq(Real('currentMode_' + str(bound)), IntVal("0")))

        return And(additional_mode_const_children)

    @staticmethod
    def aux_make_range_const(var: Real, range):
        consts = list()
        (left_end, left, right, right_end) = range

        if left > -float('inf'):
            if left_end:
                consts.append(var >= RealVal(float(left)))
            else:
                consts.append(var > RealVal(float(left)))
        if right < float('inf'):
            if right_end:
                consts.append(var <= RealVal(float(right)))
            else:
                consts.append(var < RealVal(float(right)))
        return And(consts)

    def make_range_consts(self, bound):
        result = list()
        for k in range(bound + 1):
            for i in self.range_dict:
                init_var = Real(i.id + '_' + str(k) + '_' + '0')
                end_var = Real(i.id + '_' + str(k) + '_' + 't')

                init_const = self.aux_make_range_const(init_var, self.range_dict[i])
                end_const = self.aux_make_range_const(end_var, self.range_dict[i])

                result.append(init_const)
                result.append(end_const)
        return And(result)

    def make_flow_consts(self, bound):
        mode_number = 0
        integral_children = list()
        for mode_module in self.modules:
            dynamics = mode_module["flow"]
            start_vector = list()
            end_vector = list()

            index = 0
            for exp in dynamics.exps:
                dyn_var_id = dynamics.vars[index].id
                start_vector.append(Real(dyn_var_id + "_" + str(bound) + "_0"))
                end_vector.append(Real(dyn_var_id + "_" + str(bound) + "_t"))
            new_dynamics = make_new_dynamics(dynamics, bound, self.mode_var_dict, self.range_dict, self.const_dict)
            integral = Integral(mode_number, end_vector, start_vector, new_dynamics)
            integral_children.append(integral)
            mode_number += 1
        return Or(integral_children)

    def make_invariant_consts(self, bound, integrals):
        invariant_children = list()
        index = 0
        for mode_module in self.modules:
            invariant_constraint = mode_module["inv"]
            transformed_inv_const, inv_prop_dict = make_dictionary_for_invariant(invariant_constraint,
                                                                                 dict())
            # generate new dict for invariant constraint
            new_mode_var_dict = self.mode_var_dict.copy()
            for invariant_var in inv_prop_dict:
                new_mode_var_dict[invariant_var.id] = invariant_var
            new_substitute_dict = make_dict(bound, new_mode_var_dict, self.range_dict, self.const_dict, "_0")

            result_inv_const = substitution(transformed_inv_const, new_substitute_dict)

            # generate Forall consts for invariant
            integral = integrals[index]

            invariant_sub_children = list()
            for invariant_var in inv_prop_dict:
                const = inv_prop_dict[invariant_var]
                bound_applied_inv_var = substitution(invariant_var, new_substitute_dict)
                bound_applied_const = substitution(const, new_substitute_dict)
                invariant_sub_children.append(Or([Eq(bound_applied_inv_var, Forall(integral.current_mode_number,
                                                                                   Real('tau_' + str(bound + 1)),
                                                                                   Real('tau_' + str(bound)),
                                                                                   bound_applied_const, integral)),
                                                  Eq(Not(bound_applied_inv_var), Forall(integral.current_mode_number,
                                                                                        Real('tau_' + str(bound + 1)),
                                                                                        Real('tau_' + str(bound)),
                                                                                        reduce_not(Not(bound_applied_const)),
                                                                                        integral))]))
            invariant_sub_children.append(result_inv_const)
            invariant_children.append(And(invariant_sub_children))
            index += 1
        return Or(invariant_children)

    def make_jump_consts(self, bound):

        jump_children = list()
        substitute_dict = make_dict(bound, self.mode_var_dict, self.range_dict, self.const_dict, "_t")

        total_mode_num = len(self.modules)
        index = 0
        for mode_module in self.modules:
            mode_const = mode_module["mode"]
            additional_mode_const = self.make_additional_mode_consts(bound, index, total_mode_num)
            new_mode_const = And([mode_const, additional_mode_const])

            jump_dict = mode_module["jump"]

            jump_sub_children = list()
            for jump_pre in jump_dict:
                jump_post = jump_dict[jump_pre]
                jump_sub_children.append(And([jump_pre, jump_post]))

            # generate steady jump const
            steady_jump_const_children = list()
            op_dict = {'bool': Bool, 'int': Int, 'real': Real}

            for mode_var_id in self.mode_var_dict:
                mode_var = self.mode_var_dict[mode_var_id]
                next_var = op_dict[mode_var.type](mode_var_id + self.next_str)
                steady_jump_const_children.append(Eq(next_var, mode_var))

                # add bounded info
                substitute_dict[next_var] = op_dict[mode_var.type](mode_var_id + "_" + str(bound + 1))

            for range_var in self.range_dict:
                next_var = Real(range_var.id + self.next_str)
                steady_jump_const_children.append(Eq(next_var, range_var))

                # add bounded info
                substitute_dict[next_var] = Real(range_var.id + "_" + str(bound + 1) + "_0")

            steady_jump_const = And(steady_jump_const_children)
            jump_sub_children.append(steady_jump_const)
            jump_children.append(And([new_mode_const, Or(jump_sub_children)]))
            index += 1

        jump_const_before_subst = Or(jump_children)
        jump_const = substitution(jump_const_before_subst, substitute_dict)
        return jump_const

    # assignment specific function
    def get_flow_for_assignment(self, bound):
        flows = list()
        for k in range(bound + 1):
            flow_consts = self.make_flow_consts(k)
            flows.append(flow_consts.children)
        return flows

    # def get_bound_var_dict_list(self, bound):
    #     total_dict_list = list()
    #     for k in range(bound + 1):
    #         total_dict = dict()
    #         start_dict = make_dict(k, {}, self.range_dict, {}, "_0")
    #         end_dict = make_dict(k, {}, self.range_dict, {}, "_t")
    #         mode_dict = make_dict(k, self.mode_var_dict, {}, {})
    #         total_dict.update(mode_dict)
    #         total_dict.update(end_dict)
    #         total_dict.update(start_dict)
    #         total_dict_list.append(total_dict)
    #     return total_dict_list

    def make_consts(self, bound):
        result_child = list()

        # generate init dictionary
        init_dict = make_dict(0, self.mode_var_dict, self.range_dict, self.const_dict, "_0")
        init_consts = substitution(self.init, init_dict)

        # append the initial constraint to result constraint
        result_child.append(init_consts)

        # generate dictionary upto bound
        for k in range(bound + 1):
            # make range constraint
            # and append it to the result
            range_consts = self.make_range_consts(k)
            result_child.append(range_consts)

            flow_consts = self.make_flow_consts(k)
            result_child.append(flow_consts)

            inv_consts = self.make_invariant_consts(k, flow_consts.children)
            result_child.append(inv_consts)

            jump_consts = self.make_jump_consts(k)
            result_child.append(jump_consts)

        # TODO : For Hylaa, separate these to multiple constraints..
        # return And([rangeConsts, initConst, jumpConsts, invConsts, flowConsts])
        # return And([range_consts])
        return And(result_child)
