import abc
from abc import ABC

from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import substitution, get_vars, clause
from stlmcPy.hybrid_automaton.utils import add_mode, make_mode_from_formula, encode_possible_path_as_formula
from stlmcPy.solver.abstract_solver import BaseSolver, OdeSolver
from stlmcPy.solver.ode_utils import make_boolean_abstract, make_tau_guard, gen_net_assignment, get_bound
from stlmcPy.solver.strategy import UnsatCoreBuilder, DeltaDebugBuilder, NaiveBuilder
from stlmcPy.solver.z3 import Z3Solver
from stlmcPy.tree.operations import size_of_tree
from stlmcPy.util.print import Printer


# basic wrapper interface for ode strategy
class CommonOdeStrategy:
    @abc.abstractmethod
    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict, reduction_flag):
        pass


class CommonOdeSolver(OdeSolver, ABC):
    def __init__(self, strategy_manager: CommonOdeStrategy):
        BaseSolver.__init__(self)
        self.hylaa_core = None
        self.time_optimize = False
        self.strategy_manager = strategy_manager
        self.time_dict["smt_solving_time"] = 0
        self.time_dict["solving_time"] = 0
        self.size = 0

    def solve(self, all_consts=None, info_dict=None, mapping_info=None):
        assert self.logger is not None
        if info_dict is None:
            info_dict = dict()
        if mapping_info is None:
            mapping_info = dict()

        logger = self.logger
        self.set_time("solving timer", 0)
        tau_info = dict()
        for k in mapping_info:
            if "newTau" in k.id:
                tau_info[k] = mapping_info[k]

        printer = Printer()
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

        # get stlmc type constraints and transform
        z3_boolean_consts, boolean_sub_dict = make_boolean_abstract(abstracted_consts)
        # boolean_end = timer()

        max_bound = get_bound(mapping_info)

        solver = Z3Solver()
        solver.append_logger(logger)
        solver.add(abstracted_consts)

        hylaa_result = True
        counter_consts = None

        cur_index = 0

        hybrid_automata_queue = list()
        while hylaa_result:
            # logging
            logger.add_info("loop", cur_index)

            # size = size_of_tree(abstracted_consts)
            # logger.add_info("constraint size", abst_size)

            # printer.print_verbose("loop : {}, size of constraints : {}".format(cur_index, abst_size))
            #
            # logger.start_timer("loop timer")
            # logger.start_timer("smt solving timer")

            cur_index += 1
            if counter_consts is not None:
                children_list = list()
                for chi in abstracted_consts.children:
                    children_list.append(chi)
                children_list.append(Or(counter_consts))
                abstracted_consts = And(children_list)
                solver.add(Or(counter_consts))

            # 2. Perform process #2 from note
            result, size = solver.solve()
            self.set_time("smt solving timer", solver.get_time("solving timer"))
            self.size += size
            # logger.stop_timer("smt solving timer")
            # logger.add_info("smt solving time", logger.get_duration_time("smt solving timer"))

            if result:
                # printer.print_normal_dark("Smt solver level result!")
                # logger.write_to_csv()
                # print("The number of loop : " + str(cur_index))
                # solving_res = self.specific(hybrid_automata_queue)
                # print(solving_res)
                # self.add_log_info("SMT solver level result!")
                # return solving_res, 0
                return True, self.size
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

            logger.start_timer("max literal timer")
            max_literal_set_list, alpha_delta = self.strategy_manager.perform_strategy(alpha, assignment, max_bound,
                                                                                       new_abstracted_consts,
                                                                                       c,
                                                                                       self.time_optimize,
                                                                                       z3_boolean_consts,
                                                                                       boolean_sub_dict,
                                                                                       self.get_optimize_flag(
                                                                                           "formula"))
            logger.stop_timer("max literal timer")
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

            # print(max_literal_set_list)
            counter_consts_set = set()
            max_bound = -1
            # print(alpha_delta)
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
            # print(max_literal_set_list)

            # childrenssss = list()
            # for cccc in max_literal_set_list:
            #     for ssss in cccc:
            #         childrenssss.append(ssss)
            # newwwww = And(childrenssss)
            # self.kiki(newwwww, max_bound, mapping_info)

            try:
                hylaa_result = self.run(max_literal_set_list, max_bound, mapping_info)
                # ha, conf_dict, l_v, new_bound_box_list = self.run(max_literal_set_list, max_bound, mapping_info)
                # hybrid_automata_queue.append((ha, conf_dict, l_v, new_bound_box_list))
                # hylaa_result = self.run(max_literal_set_list, max_bound, mapping_info,
                #                         tau_guard_list)
                # hylaa_result = True
                # logger.add_info("hylaa time", logger.get_duration_time("hylaa timer"))

                # logger.stop_timer("loop timer")
                # logger.add_info("loop total", logger.get_duration_time("loop timer"))
                # logger.write_to_csv()
                # logger.reset_timer_without("goal timer")

            except RuntimeError as re:
                # negate the error state
                hylaa_result = True

                import sys
                import traceback
                exc_type, exc_value, exc_traceback = sys.exc_info()
                traceback.print_tb(exc_traceback, file=sys.stdout)
                printer.print_normal_dark("retry because of {}".format(re))
                # logger.write_to_csv()
                logger.reset_timer_without("goal timer")

        # get overviewed file name
        # output_file_name = logger.get_output_file_name()
        # bound_index = output_file_name.rfind("_")
        # overview_file_name = output_file_name[:bound_index]

        # logger.add_info("bound", max_bound)
        # logger.add_info("loop", cur_index)
        # logger.add_info("constraint size", first_abst_size)
        # logger.write_to_csv(file_name=overview_file_name, cols=["bound", "loop", "constraint size"])

        # TODO: replace -1 to formula size
        return hylaa_result, self.size

    def solve2(self, all_consts=None, info_dict=None, mapping_info=None):
        assert self.logger is not None
        if info_dict is None:
            info_dict = dict()
        if mapping_info is None:
            mapping_info = dict()
        is_first = True
        logger = self.logger

        tau_info = dict()
        for k in mapping_info:
            if "newTau" in k.id:
                tau_info[k] = mapping_info[k]

        printer = Printer()
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
        first_abst_size = size_of_tree(abstracted_consts)

        # get stlmc type constraints and transform
        z3_boolean_consts, boolean_sub_dict = make_boolean_abstract(abstracted_consts)
        # boolean_end = timer()

        max_bound = get_bound(mapping_info)

        solver = Z3Solver()
        solver.append_logger(logger)
        solver.add(abstracted_consts)

        hylaa_result = True
        counter_consts = None
        original_consts = None
        is_contain_original_consts = False

        cur_index = 0

        hybrid_automata_queue = list()
        depth = 1
        ha = None
        while hylaa_result:
            # logging
            logger.add_info("loop", cur_index)

            abst_size = size_of_tree(abstracted_consts)
            logger.add_info("constraint size", abst_size)

            # printer.print_verbose("loop : {}, size of constraints : {}".format(cur_index, abst_size))
            #
            logger.start_timer("loop timer")
            logger.start_timer("smt solving timer")

            cur_index += 1
            if counter_consts is not None:
                if not is_contain_original_consts:
                    solver.add(original_consts)
                    is_contain_original_consts = True
                solver.add(counter_consts)
            # if counter_consts is not None:
            #     children_list = list()
            #     for chi in abstracted_consts.children:
            #         children_list.append(chi)
            #     children_list.append(Or(counter_consts))
            #     abstracted_consts = And(children_list)
            #     solver.add(Or(counter_consts))

            # 2. Perform process #2 from note
            result, size = solver.solve()
            # print("smt solving result : {}, {}".format(result, solver.cache()))

            logger.stop_timer("smt solving timer")
            logger.add_info("smt solving time", logger.get_duration_time("smt solving timer"))

            if result:
                printer.print_normal_dark("Smt solver level result!")
                logger.write_to_csv()
                # print("The number of loop : " + str(cur_index))
                # solving_res = self.specific(hybrid_automata_queue)
                # print(solving_res)
                # self.add_log_info("SMT solver level result!")
                # return solving_res, 0
                return True, 0
            assignment = solver.make_assignment()
            alpha = assignment.get_assignments()
            # print(alpha)
            for mp in mapping_info:
                if isinstance(mapping_info[mp], Or):
                    mapping_info[mp] = mapping_info[mp].children[0]

            net_dict = info_dict.copy()
            net_dict.update(mapping_info)
            new_alpha = gen_net_assignment(alpha, net_dict)
            new_abstracted_consts = abstracted_consts
            c = clause(new_abstracted_consts)

            logger.start_timer("max literal timer")
            max_literal_set_list, alpha_delta = self.strategy_manager.perform_strategy(alpha, assignment, max_bound,
                                                                                       new_abstracted_consts,
                                                                                       c,
                                                                                       self.time_optimize,
                                                                                       z3_boolean_consts,
                                                                                       boolean_sub_dict,
                                                                                       self.get_optimize_flag(
                                                                                           "formula"))
            logger.stop_timer("max literal timer")
            logger.add_info("preparing max literal set", logger.get_duration_time("max literal timer"))

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
            #
            # def _path_prefix(_max_literal_set_list: list):
            #     _path_prefix_set = set()
            #     for i, max_literal_set in enumerate(max_literal_set_list):
            #         if i < len(max_literal_set_list) - 1:
            #             for literal in max_literal_set:
            #                 _path_prefix_set.add(literal)
            #     return _path_prefix_set
            #
            # path_prefix_set = _path_prefix(max_literal_set_list)

            # counter_consts_set = set()
            # max_bound = -1
            # for s in max_literal_set_list:
            #     for c in s:
            #         if isinstance(c, Bool):
            #             if "newIntegral" in c.id:
            #                 index = int(c.id.rfind("_")) + 1
            #                 bound = int(c.id[index:])
            #                 if bound > max_bound:
            #                     max_bound = bound
            #         # counter_consts_set.add(Not(c))
            #         if str(alpha_delta[c]) == "True":
            #             counter_consts_set.add(Not(c))
            #         else:
            #             counter_consts_set.add(c)

            # counter_consts = list(counter_consts_set)
            path_length = len(max_literal_set_list)
            mode_to_be_generated = path_length - depth
            # print("path length {}, mode to be generated {}".format(path_length, mode_to_be_generated))
            new_mode = None
            if path_length > mode_to_be_generated >= 0:
                new_mode = make_mode_from_formula(And(list(max_literal_set_list[mode_to_be_generated])),
                                                  mode_to_be_generated, max_bound, mapping_info)
                original_consts, counter_consts = encode_possible_path_as_formula(
                    And(list(max_literal_set_list[mode_to_be_generated])), mode_to_be_generated, alpha)
                # print("generate mode \n{}\n\n".format(new_mode))
            # depth += 1
            # reset at regeneration of ha
            try:
                logger.start_timer("hylaa timer")
                if is_first:
                    ha, conf_dict, l_v, new_bound_box_list = self.run(max_literal_set_list, max_bound, mapping_info)
                    is_first = False
                    # print("first one \n{}\n\n".format(ha))
                else:
                    if new_mode is not None and ha is not None:
                        add_mode(ha, mode_to_be_generated, new_mode)
                        # print("add new mode \n {}\n\n".format(ha))
                    # print(add_mode(ha, 1))
                # ha, conf_dict, l_v, new_bound_box_list = self.run(max_literal_set_list, max_bound, mapping_info)
                # hybrid_automata_queue.append((ha, conf_dict, l_v, new_bound_box_list))
                # hylaa_result = self.run(max_literal_set_list, max_bound, mapping_info,
                #                         tau_guard_list)
                hylaa_result = True
                logger.stop_timer("hylaa timer")
                logger.add_info("hylaa time", logger.get_duration_time("hylaa timer"))

                logger.stop_timer("loop timer")
                logger.add_info("loop total", logger.get_duration_time("loop timer"))
                logger.write_to_csv()
                logger.reset_timer_without("goal timer")

            except RuntimeError as re:
                # negate the error state
                hylaa_result = True

                import sys
                import traceback
                exc_type, exc_value, exc_traceback = sys.exc_info()
                traceback.print_tb(exc_traceback, file=sys.stdout)
                printer.print_normal_dark("retry because of {}".format(re))
                logger.write_to_csv()
                logger.reset_timer_without("goal timer")

        # get overviewed file name
        output_file_name = logger.get_output_file_name()
        bound_index = output_file_name.rfind("_")
        overview_file_name = output_file_name[:bound_index]

        logger.add_info("bound", max_bound)
        logger.add_info("loop", cur_index)
        logger.add_info("constraint size", first_abst_size)
        logger.write_to_csv(file_name=overview_file_name, cols=["bound", "loop", "constraint size"])

        # TODO: replace -1 to formula size
        return hylaa_result, -1

    @abc.abstractmethod
    def run(self, s_f_list, max_bound, sigma):
        pass

    @abc.abstractmethod
    def specific(self, l: list):
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

    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict, reduction_flag):
        info_dict = dict()
        info_dict["alpha"] = alpha
        info_dict["assignment"] = assignment
        info_dict["max_bound"] = max_bound
        info_dict["new_abstracted_consts"] = new_abstracted_consts
        info_dict["c"] = c
        info_dict["optimize"] = optimize
        info_dict["reduction_flag"] = reduction_flag

        self.builder.prepare(info_dict)
        return self.builder.perform()
