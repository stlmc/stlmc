import abc
from abc import ABC

from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import substitution, get_vars, clause
from stlmcPy.hybrid_automaton.utils import add_mode, make_mode_from_formula, encode_possible_path_as_formula
from stlmcPy.solver.abstract_solver import BaseSolver, OdeSolver
from stlmcPy.solver.ode_utils import make_boolean_abstract, make_tau_guard, gen_net_assignment, get_bound
from stlmcPy.solver.strategy import UnsatCoreBuilder, DeltaDebugBuilder, NaiveBuilder
from stlmcPy.solver.z3 import Z3Solver, z3Obj
from stlmcPy.tree.operations import size_of_tree
from stlmcPy.util.print import Printer


# basic wrapper interface for ode strategy
class CommonOdeStrategy:
    @abc.abstractmethod
    def add(self, consts):
        pass

    @abc.abstractmethod
    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict, reduction_flag):
        pass


class CommonSolvingStrategy:
    def __init__(self, solving_function):
        self.solving_function = solving_function

    @abc.abstractmethod
    def perform_solving(self, options: dict) -> dict:
        pass


class CommonOdeSolver(OdeSolver, ABC):
    def __init__(self, strategy_manager: CommonOdeStrategy, solving_manager: CommonSolvingStrategy):
        BaseSolver.__init__(self)
        self.hylaa_core = None
        self.time_optimize = False
        self.strategy_manager = strategy_manager
        self.solving_manager = solving_manager
        self.time_dict["smt_solving_time"] = 0
        self.time_dict["solving_time"] = 0
        self.size = 0

    def solve(self, all_consts=None, info_dict=None, mapping_info=None):
        def _prepare_dicts(_info_dict: dict, _mapping_info: dict):
            option_dict = self.conf_dict.copy()
            if _info_dict is None:
                _info_dict = dict()

            if _mapping_info is None:
                _mapping_info = dict()

            tau_info = dict()
            for k in _mapping_info:
                if "newTau" in k.id:
                    tau_info[k] = _mapping_info[k]

            option_dict["info_dict"] = _info_dict
            option_dict["mapping_info"] = _mapping_info
            option_dict["tau_info"] = tau_info
            option_dict["caller"] = self

            option_dict["all_consts"] = all_consts
            return option_dict

        option = _prepare_dicts(info_dict, mapping_info)
        solving_result = self.solving_manager.perform_solving(option)
        assert "size" in solving_result
        assert "result" in solving_result
        assert "time" in solving_result
        return solving_result["result"], solving_result["size"]

    @abc.abstractmethod
    def run(self, s_f_list, max_bound, sigma):
        pass


class NaiveStrategyManager(CommonOdeStrategy):
    def __init__(self):
        self.builder = NaiveBuilder()

    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict, reduction_flag):
        info_dict = dict()
        info_dict["alpha"] = alpha
        info_dict["assignment"] = assignment
        info_dict["max_bound"] = max_bound
        info_dict["c"] = c
        info_dict["optimize"] = optimize
        info_dict["z3_boolean_consts"] = z3_boolean_consts
        info_dict["boolean_sub_dict"] = boolean_sub_dict

        self.builder.prepare(info_dict)
        return self.builder.perform()


class ReductionStrategyManager(CommonOdeStrategy):
    def __init__(self):
        self.builder = DeltaDebugBuilder()

    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict, reduction_flag):
        info_dict = dict()
        info_dict["alpha"] = alpha
        info_dict["assignment"] = assignment
        info_dict["max_bound"] = max_bound
        info_dict["c"] = c
        info_dict["optimize"] = optimize
        info_dict["z3_boolean_consts"] = z3_boolean_consts
        info_dict["boolean_sub_dict"] = boolean_sub_dict

        self.builder.prepare(info_dict)
        return self.builder.perform()


class UnsatCoreStrategyManager(CommonOdeStrategy):
    def __init__(self):
        self.builder = UnsatCoreBuilder()
        self.cache = set()

    def add(self, consts):
        self.cache.add(z3Obj(consts))

    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict, reduction_flag):
        info_dict = dict()
        info_dict["alpha"] = alpha
        info_dict["assignment"] = assignment
        info_dict["max_bound"] = max_bound
        #info_dict["new_abstracted_consts"] = new_abstracted_consts
        info_dict["new_abstracted_consts"] = self.cache
        info_dict["c"] = c
        info_dict["optimize"] = optimize
        info_dict["reduction_flag"] = reduction_flag

        self.builder.prepare(info_dict)
        return self.builder.perform()


class NormalSolvingStrategy(CommonSolvingStrategy):
    def __init__(self, solving_function):
        super().__init__(solving_function)

    def perform_solving(self, options: dict) -> dict:
        assert "info_dict" in options
        assert "mapping_info" in options
        assert "tau_info" in options
        assert "caller" in options
        assert "all_consts" in options

        info_dict = options["info_dict"]
        mapping_info = options["mapping_info"]
        tau_info = options["tau_info"]
        caller = options["caller"]
        all_consts = options["all_consts"]

        caller.set_time("solving timer", 0)

        # pre-processing
        # boolean_start = timer()
        # heuristic: removing mapping constraint part.
        trans_all_consts = list()
        trans_all_consts.append(all_consts.children[0])

        bef = all_consts.children[1]
        tau_condition_sub = substitution(bef.children[-1], tau_info)
        aft = bef.children[0:-1]
        aft.append(tau_condition_sub)
        trans_all_consts.append(And(aft))

        abstracted_consts = And(trans_all_consts)
        new_added_consts = abstracted_consts

        # get stlmc type constraints and transform
        z3_boolean_consts, boolean_sub_dict = make_boolean_abstract(abstracted_consts)
        # boolean_end = timer()

        max_bound = get_bound(mapping_info)

        solver = Z3Solver()
        solver.append_logger(caller.logger)
        solver.add(abstracted_consts)

        solver_result = True
        counter_consts = None

        cur_index = 0

        result_dict = dict()
        result_dict["result"] = "True"
        result_dict["size"] = 0
        result_dict["time"] = 0

        while solver_result:
            cur_index += 1
            if counter_consts is not None:
                children_list = list()
                for chi in abstracted_consts.children:
                    children_list.append(chi)
                new_added_consts = Or(counter_consts)
                children_list.append(new_added_consts)
                abstracted_consts = And(children_list)
                solver.add(Or(counter_consts))

            # 2. Perform process #2 from note
            result, formula_size = solver.solve()
            caller.set_time("smt solving timer", solver.get_time("solving timer"))
            print("loop: {}, smt: {}".format(cur_index, solver.get_time("solving timer")), end="", flush=True)
            result_dict["size"] += formula_size

            if result:
                # smt solver level result
                print(", ode: {}".format(result_dict["time"]), flush=True)
                result_dict["result"], result_dict["time"] = "True", caller.get_time("solving timer")
                return result_dict

            assignment = solver.make_assignment()
            alpha = assignment.get_assignments()

            for mp in mapping_info:
                if isinstance(mapping_info[mp], Or):
                    mapping_info[mp] = mapping_info[mp].children[0]

            net_dict = info_dict.copy()
            net_dict.update(mapping_info)
            new_alpha = gen_net_assignment(alpha, net_dict)
            new_abstracted_consts = abstracted_consts
            c = clause(new_abstracted_consts)

            caller.strategy_manager.add(new_added_consts)

            caller.logger.start_timer("max literal timer")
            max_literal_set_list, alpha_delta = caller.strategy_manager.perform_strategy(alpha, assignment, max_bound,
                                                                                         new_abstracted_consts,
                                                                                         c,
                                                                                         caller.time_optimize,
                                                                                         z3_boolean_consts,
                                                                                         boolean_sub_dict,
                                                                                         caller.get_optimize_flag(
                                                                                             "formula"))
            caller.logger.stop_timer("max literal timer")
            # logger.add_info("preparing max literal set", logger.get_duration_time("max literal timer"))

            remove_mode_clauses = list()
            for clause_bound in max_literal_set_list:
                s_diff = set()
                for elem in clause_bound:
                    if isinstance(elem, Bool):
                        if "reach_goal" in elem.id:
                            s_diff.add(elem)
                    if isinstance(elem, Neq):
                        s_diff.add(elem)
                    vs = get_vars(elem)
                    if len(vs) == 0:
                        s_diff.add(elem)
                    for v in vs:
                        if v in new_alpha:
                            s_diff.add(elem)
                clause_bound = clause_bound.difference(s_diff)
                remove_mode_clauses.append(clause_bound)

            max_literal_set_list = remove_mode_clauses

            counter_consts_set = set()
            max_bound = -1
            for s in max_literal_set_list:
                for c in s:
                    if isinstance(c, Bool):
                        if "newIntegral" in c.id:
                            index = int(c.id.rfind("_")) + 1
                            bound = int(c.id[index:])
                            if bound > max_bound:
                                max_bound = bound
                    # counter_consts_set.add(Not(c))
                    if str(alpha_delta[c]) == "True":
                        counter_consts_set.add(Not(c))
                    else:
                        counter_consts_set.add(c)

            counter_consts = list(counter_consts_set)

            solver_result, result_dict["time"] = caller.run(max_literal_set_list, max_bound, mapping_info)
            caller.set_time("solving timer", result_dict["time"])
            print(", ode: {}, total: {}".format(result_dict["time"], caller.get_time("solving timer")), flush=True)
            caller.logger.reset_timer_without("goal timer")
        result_dict["result"] = "False"
        return result_dict


class MergeSolvingStrategy(CommonSolvingStrategy):
    def __init__(self, solving_function):
        super().__init__(solving_function)

    def perform_solving(self, options: dict) -> dict:
        assert "info_dict" in options
        assert "mapping_info" in options
        assert "tau_info" in options
        assert "caller" in options
        assert "all_consts" in options

        info_dict = options["info_dict"]
        mapping_info = options["mapping_info"]
        tau_info = options["tau_info"]
        caller = options["caller"]
        all_consts = options["all_consts"]

        caller.set_time("solving timer", 0)

        # pre-processing
        # boolean_start = timer()
        # heuristic: removing mapping constraint part.
        trans_all_consts = list()
        trans_all_consts.append(all_consts.children[0])

        bef = all_consts.children[1]
        tau_condition_sub = substitution(bef.children[-1], tau_info)
        aft = bef.children[0:-1]
        aft.append(tau_condition_sub)
        trans_all_consts.append(And(aft))

        abstracted_consts = And(trans_all_consts)
        new_added_consts = abstracted_consts

        # get stlmc type constraints and transform
        z3_boolean_consts, boolean_sub_dict = make_boolean_abstract(abstracted_consts)
        # boolean_end = timer()

        max_bound = get_bound(mapping_info)

        solver = Z3Solver()
        solver.append_logger(caller.logger)
        solver.add(abstracted_consts)

        counter_consts = None
        hybrid_automata_queue = list()

        cur_index = 0

        result_dict = dict()
        result_dict["result"] = "True"
        result_dict["size"] = 0
        merge_counter = 0

        while True:
            cur_index += 1
            merge_counter += 1
            if counter_consts is not None:
                children_list = list()
                for chi in abstracted_consts.children:
                    children_list.append(chi)
                new_added_consts = Or(counter_consts)
                children_list.append(new_added_consts)
                abstracted_consts = And(children_list)
                solver.add(Or(counter_consts))

            # 2. Perform process #2 from note
            result, formula_size = solver.solve()
            caller.set_time("smt solving timer", solver.get_time("solving timer"))
            print("loop: {}, smt: {}".format(cur_index, solver.get_time("solving timer")), flush=True)
            result_dict["size"] += formula_size

            if result:
                # smt solver level result
                result_dict["result"], result_dict["time"] = self.solving_function(hybrid_automata_queue)
                caller.set_time("solving timer", result_dict["time"])
                return result_dict

            assignment = solver.make_assignment()
            alpha = assignment.get_assignments()

            for mp in mapping_info:
                if isinstance(mapping_info[mp], Or):
                    mapping_info[mp] = mapping_info[mp].children[0]

            net_dict = info_dict.copy()
            net_dict.update(mapping_info)
            new_alpha = gen_net_assignment(alpha, net_dict)
            new_abstracted_consts = abstracted_consts
            c = clause(new_abstracted_consts)

            caller.strategy_manager.add(new_added_consts)

            caller.logger.start_timer("max literal timer")
            max_literal_set_list, alpha_delta = caller.strategy_manager.perform_strategy(alpha, assignment, max_bound,
                                                                                         new_abstracted_consts,
                                                                                         c,
                                                                                         caller.time_optimize,
                                                                                         z3_boolean_consts,
                                                                                         boolean_sub_dict,
                                                                                         caller.get_optimize_flag(
                                                                                             "formula"))
            caller.logger.stop_timer("max literal timer")
            # logger.add_info("preparing max literal set", logger.get_duration_time("max literal timer"))

            remove_mode_clauses = list()
            for clause_bound in max_literal_set_list:
                s_diff = set()
                for elem in clause_bound:
                    if isinstance(elem, Bool):
                        if "reach_goal" in elem.id:
                            s_diff.add(elem)
                    if isinstance(elem, Neq):
                        s_diff.add(elem)
                    vs = get_vars(elem)
                    if len(vs) == 0:
                        s_diff.add(elem)
                    for v in vs:
                        if v in new_alpha:
                            s_diff.add(elem)
                clause_bound = clause_bound.difference(s_diff)
                remove_mode_clauses.append(clause_bound)

            max_literal_set_list = remove_mode_clauses

            counter_consts_set = set()
            max_bound = -1
            for s in max_literal_set_list:
                for c in s:
                    if isinstance(c, Bool):
                        if "newIntegral" in c.id:
                            index = int(c.id.rfind("_")) + 1
                            bound = int(c.id[index:])
                            if bound > max_bound:
                                max_bound = bound
                    # counter_consts_set.add(Not(c))
                    if str(alpha_delta[c]) == "True":
                        counter_consts_set.add(Not(c))
                    else:
                        counter_consts_set.add(c)

            counter_consts = list(counter_consts_set)

            ha, conf_dict, l_v, new_bound_box_list = caller.run(max_literal_set_list, max_bound, mapping_info)
            hybrid_automata_queue.append((ha, conf_dict, l_v, new_bound_box_list))
            # if merge_counter == 350:
            #     maybe_merged_ha = self.solving_function(hybrid_automata_queue, True)
            #     hybrid_automata_queue.clear()
            #     hybrid_automata_queue.append(maybe_merged_ha)
            #     merge_counter = 0
            caller.logger.reset_timer_without("goal timer")
