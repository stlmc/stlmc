import abc

from ..constraints.operations import *


class Model:
    def __init__(self):
        self.boolean_abstract = dict()
        self.range_dict = dict()

    @abc.abstractmethod
    def make_consts(self, bound):
        pass

    @abc.abstractmethod
    def k_step_consts(self, k: int, is_final=False):
        pass

    @abc.abstractmethod
    def init_consts(self):
        pass

    @abc.abstractmethod
    def gen_reach_condition(self):
        pass

    @abc.abstractmethod
    def gen_stl_condition(self):
        pass

    @abc.abstractmethod
    def is_gen_reach_condition(self):
        pass

    def clear(self):
        self.boolean_abstract = dict()


# empty model for formula_encoding
class EmptyModel(Model):
    def init_consts(self):
        return BoolVal("True")

    def make_consts(self, bound):
        # return any value
        return BoolVal("True")

    def k_step_consts(self, k: int, is_final=False):
        return BoolVal("True")

    def gen_reach_condition(self):
        pass

    def gen_stl_condition(self):
        pass

    def is_gen_reach_condition(self):
        pass


class StlMC(Model):
    def __init__(self, mode_var_dict, range_dict, const_dict, raw_prop_dict, modules, init, init_mode=None):
        super().__init__()
        # key : string, value : object
        self.mode_var_dict = mode_var_dict
        self.prop_dict = raw_prop_dict
        self.range_dict = range_dict
        self.const_dict = const_dict
        self.modules = modules
        self.init = init
        self.next_str = "##$%^&$%^&##'"
        self.is_stl_reach = False
        self.init_mode = init_mode

    def gen_reach_condition(self):
        self.is_stl_reach = True

    def gen_stl_condition(self):
        self.is_stl_reach = False

    def is_gen_reach_condition(self):
        return self.is_stl_reach

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

        return additional_mode_const_children

    @staticmethod
    def aux_make_range_const(var: Real, range):
        consts = list()
        (left_end, left, right, right_end) = range

        if left > -float('inf'):
            if left_end:
                chi = Geq(var, RealVal(float(left)), is_range=True)
            else:
                chi = Gt(var, RealVal(float(left)), is_range=True)
            consts.append(chi)
        if right < float('inf'):
            if right_end:
                chi = Leq(var, RealVal(float(right)), is_range=True)
            else:
                chi = Lt(var, RealVal(float(right)), is_range=True)
            consts.append(chi)
        return consts

    def make_range_consts(self, bound):
        result = list()
        for i in self.range_dict:
            init_var = Real(i.id + '_' + str(bound) + '_' + '0')
            end_var = Real(i.id + '_' + str(bound) + '_' + 't')

            init_const = self.aux_make_range_const(init_var, self.range_dict[i])
            end_const = self.aux_make_range_const(end_var, self.range_dict[i])

            result.extend(init_const)
            result.extend(end_const)
        range_const = And(result)
        # r@{ bound }
        track_v = Bool("r@{}".format(bound))
        track_dict = dict()
        track_dict[track_v] = range_const
        return range_const, track_dict

    def make_mode_consts(self, bound):
        track_dict = dict()
        mode_consts = list()
        substitute_dict = dict()
        op_dict = {'bool': Bool, 'int': Int, 'real': Real}

        for mode_var_id in self.mode_var_dict:
            mode_var = self.mode_var_dict[mode_var_id]
            # add bounded info
            substitute_dict[mode_var] = op_dict[mode_var.type](mode_var_id + "_" + str(bound))

        for module_index, mode_module in enumerate(self.modules):
            mode_const = mode_module["mode"]
            mode_cons_bound = substitution(mode_const, substitute_dict)

            # m_{ module index }@
            track_v = Bool("m_{}@const_{}".format(module_index, bound))
            visualize = Eq(Real('currentMode_' + str(bound)), RealVal(str(module_index)))
            mode_const = And([mode_cons_bound, visualize])

            track_dict[track_v] = mode_const
            mode_consts.append(mode_const)
        return mode_consts, track_dict

    def make_flow_consts(self, bound):
        integral_children = list()
        integral_object_list = list()
        substitute_dict = dict()
        op_dict = {'bool': Bool, 'int': Int, 'real': Real}

        for mode_var_id in self.mode_var_dict:
            mode_var = self.mode_var_dict[mode_var_id]
            # add bounded info
            substitute_dict[mode_var] = op_dict[mode_var.type](mode_var_id + "_" + str(bound))
        for module_index, mode_module in enumerate(self.modules):
            dynamics = mode_module["flow"]
            # mode_const_bound = substitution(mode_const, substitute_dict).children
            start_vector = list()
            end_vector = list()

            index = 0
            for exp in dynamics.exps:
                dyn_var_id = dynamics.vars[index].id
                start_vector.append(Real(dyn_var_id + "_" + str(bound) + "_0"))
                end_vector.append(Real(dyn_var_id + "_" + str(bound) + "_t"))
                index += 1
            new_dynamics = make_new_dynamics(dynamics, bound, self.mode_var_dict, self.range_dict, self.const_dict)
            constant_consts = list()

            if isinstance(new_dynamics, Ode):
                for cur_ode in range(len(new_dynamics.exps)):
                    cur_flow = new_dynamics.exps[cur_ode]
                    if len(get_vars(cur_flow)) == 0:
                        constant_consts.append(
                            Eq(end_vector[cur_ode], start_vector[cur_ode] + cur_flow * Real("time_" + str(bound))))
                        if bound == 0:
                            constant_consts.append(Eq(Real("time_0"), Real("tau_0")))
                        else:
                            constant_consts.append(Eq(Real("time_" + str(bound)),
                                                      (Real("tau_" + str(bound + 1)) - Real("tau_" + str(bound)))))
            integral = Integral(module_index, end_vector, start_vector, new_dynamics)
            bool_integral = Bool("newIntegral_" + str(module_index) + "_" + str(bound))
            self.boolean_abstract[bool_integral] = integral
            integral_object_list.append(integral)
            integral_children.append(bool_integral)
        return integral_children, integral_object_list

    def make_invariant_consts(self, bound, integrals):
        track_dict = dict()

        invariant_children = list()
        index = 0
        op_dict = {'bool': Bool, 'int': Int, 'real': Real}
        substitute_dict = dict()
        for mode_var_id in self.mode_var_dict:
            mode_var = self.mode_var_dict[mode_var_id]
            # add bounded info
            substitute_dict[mode_var] = op_dict[mode_var.type](mode_var_id + "_" + str(bound))

        for module_index, mode_module in enumerate(self.modules):
            invariant_constraint = mode_module["inv"]
            transformed_inv_const, inv_prop_dict = make_dictionary_for_invariant(invariant_constraint,
                                                                                 dict())
            mode_const = mode_module["mode"]
            mode_const_bound = substitution(mode_const, substitute_dict).children
            # generate new dict for invariant constraint
            new_mode_var_dict = self.mode_var_dict.copy()
            for invariant_var in inv_prop_dict:
                new_mode_var_dict[invariant_var.id] = invariant_var
            new_substitute_dict = make_dict(bound, new_mode_var_dict, self.range_dict, self.const_dict, "_0")
            new_substitute_dict_t = make_dict(bound, new_mode_var_dict, self.range_dict, self.const_dict, "_t")
            # generate Forall consts for invariant
            integral = integrals[index]

            invariant_sub_children = list()

            new_dict = dict()
            for inv_index, invariant_var in enumerate(inv_prop_dict):
                track_v = Bool("m_{}@inv^{}_{}".format(module_index, inv_index, bound))

                const = inv_prop_dict[invariant_var]
                bound_applied_inv_var = substitution(invariant_var, new_substitute_dict)
                key_index = bound_applied_inv_var.id.find("_")
                inv_boolean = bound_applied_inv_var.id[:key_index + 1] + str(index) + str(
                    bound_applied_inv_var.id[key_index + 1]) + "_" + bound_applied_inv_var.id[-1]
                bound_applied_const = substitution(const, new_substitute_dict)
                self.boolean_abstract[Bool(inv_boolean)] = Forall(integral.current_mode_number,
                                                                  Real('tau_' + str(bound + 1)),
                                                                  Real('tau_' + str(bound)),
                                                                  bound_applied_const, integral)
                # m_{ module index }@inv^{ invariant index }_{ bound }
                track_dict[track_v] = bound_applied_const
                new_dict[invariant_var] = And([Bool(inv_boolean), bound_applied_const])

                invariant_sub_children.extend([Bool(inv_boolean), bound_applied_const])

            if len(inv_prop_dict) > 0:
                pass
            if len(invariant_sub_children) > 0:
                result = substitution(transformed_inv_const, new_dict)
                invariant_children.append(result)
            else:
                invariant_children.append(And([BoolVal("True")]))
            index += 1
        return invariant_children, track_dict

    def make_jump_consts(self, bound):

        all_jumps = list()
        track_dict = dict()
        substitute_dict = make_dict(bound, self.mode_var_dict, self.range_dict, self.const_dict, "_t")

        total_mode_num = len(self.modules)
        index = 0
        for module_index, mode_module in enumerate(self.modules):
            mode_const_list = list()
            mode_const_list.extend(mode_module["mode"].children)
            new_mode_const = And(mode_const_list)

            jump_dict = mode_module["jump"]

            jump_sub_children = list()

            for jump_pre in jump_dict:
                jump_flat = list()
                jump_flat.append(jump_pre)
                jump_post = jump_dict[jump_pre]
                jump_flat.extend(jump_post.children)
                jump_sub_children.append(And(jump_flat))

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
            if not self.is_stl_reach:
                jump_sub_children.append(steady_jump_const)

            jumps = list()
            for jump_index, jump in enumerate(jump_sub_children):
                # m_{ module index }@jump^{ jump index }_{ bound }
                track_v = Bool("m_{}@jump^{}_{}".format(module_index, jump_index, bound))
                jump_const = substitution(jump, substitute_dict)
                track_dict[track_v] = jump_const
                jumps.append(jump_const)

            all_jumps.append(Or(jumps))
            index += 1
        return all_jumps, track_dict

    # assignment specific function
    def get_flow_for_assignment(self, bound):
        flows = list()
        for k in range(bound + 1):
            flow_consts = self.make_flow_consts(k)
            flows.append(flow_consts.children)
        return flows

    def make_consts(self, bound):
        result_child = list()
        result_track_child = list()

        # generate init dictionary
        init_const, init_track_const = self.init_consts()

        # append the initial constraint to result constraint
        result_child.append(init_const)
        result_track_child.append(init_track_const)

        # generate dictionary upto bound
        for k in range(bound):
            # make range constraint
            # and append it to the result
            k_step_const, track_const = self.k_step_consts(k)
            result_child.append(k_step_const)
            result_track_child.append(track_const)
        # add final constraints
        last_const, last_track_const = self.k_step_consts(bound, is_final=True)
        result_child.append(last_const)
        result_track_child.append(last_track_const)

        return And(result_child)

    def init_consts(self):
        init_dict = make_dict(0, self.mode_var_dict, self.range_dict, self.const_dict, "_0")
        init_const = substitution(self.init, init_dict)
        track_v = Bool("init")
        return init_const, Eq(track_v, init_const)

    def k_step_consts(self, k: int, is_final=False):
        result_child = list()
        track_dict = dict()

        range_const, range_track_dict = self.make_range_consts(k)
        track_dict.update(range_track_dict)
        result_child.append(range_const)

        mode_consts, mode_track_dict = self.make_mode_consts(k)
        track_dict.update(mode_track_dict)

        flow_consts, integral_object_list = self.make_flow_consts(k)
        inv_consts, inv_track_dict = self.make_invariant_consts(k, integral_object_list)
        track_dict.update(inv_track_dict)
        if is_final:
            jump_consts = None
        else:
            jump_consts, jump_track_dict = self.make_jump_consts(k)
            track_dict.update(jump_track_dict)

        module_consts_children = list()
        for module_index, _ in enumerate(self.modules):
            sub_result = list()
            sub_result.append(mode_consts[module_index])
            sub_result.append(flow_consts[module_index])
            sub_result.append(inv_consts[module_index])
            if jump_consts is not None:
                sub_result.append(jump_consts[module_index])
            module_consts_children.append(And(sub_result))

        result_child.append(Or(module_consts_children))

        track_const = And([Eq(v, track_dict[v]) for v in track_dict])
        return And(result_child), track_const
