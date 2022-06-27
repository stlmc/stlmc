from abc import ABC

# basic wrapper interface for ode strategy
from ..objects.configuration import *
from ..util.logger import Logger

from ..constraints.constraints import *
from ..constraints.operations import get_vars, clause
from ..hybrid_automaton.converter import *
from ..hybrid_automaton.utils import *
from ..solver.abstract_solver import BaseSolver, OdeSolver
from ..solver.ode_utils import make_boolean_abstract, gen_net_assignment, get_bound
from ..solver.strategy import UnsatCoreBuilder, DeltaDebugBuilder, NaiveBuilder
from ..solver.z3 import Z3Solver, z3Obj


class CommonOdeStrategy:
    @abc.abstractmethod
    def add(self, consts):
        pass

    @abc.abstractmethod
    def clear(self):
        pass

    @abc.abstractmethod
    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict, reduction_flag):
        pass


class CommonSolvingStrategy:
    def __init__(self, converter: AbstractConverter):
        self.converter = converter

    @abc.abstractmethod
    def perform_solving(self, options: dict) -> dict:
        pass


class CommonOdeSolver(OdeSolver, ABC):
    def make_assignment(self):
        pass

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
            # option_dict = self.conf_dict.copy()
            option_dict = dict()
            if _info_dict is None:
                _info_dict = dict()

            if _mapping_info is None:
                _mapping_info = dict()

            tau_info = dict()
            opt_var_info = dict()
            for k in _mapping_info:
                if "newTau" in k.id:
                    tau_info[k] = _mapping_info[k]
                if "opt_var" in k.id:
                    opt_var_info[k] = _mapping_info[k]

            option_dict["info_dict"] = _info_dict
            option_dict["mapping_info"] = _mapping_info
            option_dict["tau_info"] = tau_info
            option_dict["opt_var_info"] = opt_var_info
            option_dict["caller"] = self

            option_dict["all_consts"] = all_consts
            return option_dict

        option = _prepare_dicts(info_dict, mapping_info)
        option["configuration"] = self.config
        solving_result = self.solving_manager.perform_solving(option)
        assert "size" in solving_result
        assert "result" in solving_result
        assert "time" in solving_result
        return solving_result["result"], solving_result["size"]


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

    def clear(self):
        self.cache.clear()

    def add(self, consts):
        self.cache.add(z3Obj(consts))

    def perform_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c, optimize, z3_boolean_consts,
                         boolean_sub_dict, reduction_flag):
        info_dict = dict()
        info_dict["alpha"] = alpha
        info_dict["assignment"] = assignment
        info_dict["max_bound"] = max_bound
        # info_dict["new_abstracted_consts"] = new_abstracted_consts
        info_dict["new_abstracted_consts"] = self.cache
        info_dict["c"] = c
        info_dict["optimize"] = optimize
        info_dict["reduction_flag"] = reduction_flag

        self.builder.prepare(info_dict)
        return self.builder.perform()


class NormalSolvingStrategy(CommonSolvingStrategy):
    def perform_solving(self, options: dict) -> dict:
        assert "info_dict" in options
        assert "mapping_info" in options
        assert "tau_info" in options
        assert "caller" in options
        assert "all_consts" in options

        info_dict = options["info_dict"]
        mapping_info = options["mapping_info"]
        tau_info = options["tau_info"]
        opt_var_info = options["opt_var_info"]
        caller = options["caller"]
        all_consts = options["all_consts"]

        caller.set_time("solving timer", 0)

        # pre-processing
        # boolean_start = timer()
        # heuristic: removing mapping constraint part.
        trans_all_consts = list()
        trans_all_consts.extend(all_consts.children[0:2])

        for tchi in tau_info:
            trans_all_consts.append(Eq(tchi, tau_info[tchi]))
        for opt_chi in opt_var_info:
            trans_all_consts.append(Eq(opt_chi, opt_var_info[opt_chi]))

        abstracted_consts = And(trans_all_consts)
        new_added_consts = abstracted_consts

        # get stlmc type constraints and transform
        z3_boolean_consts, boolean_sub_dict = make_boolean_abstract(abstracted_consts)
        # boolean_end = timer()

        max_bound = get_bound(mapping_info)

        solver = Z3Solver()
        solver_logger = Logger()
        # dummy config
        dummy_config = Configuration()
        section = Section()
        section.name = "z3"
        section.arguments["logic"] = "QF_LRA"
        dummy_config.add_section(section)
        solver.set_config(dummy_config)

        solver.append_logger(solver_logger)
        solver.add(abstracted_consts)

        solver_result = True
        counter_consts = None

        cur_index = 0

        result_dict = dict()
        result_dict["result"] = "True"
        result_dict["size"] = 0
        result_dict["time"] = 0

        caller.logger.start_timer("solving timer")
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
            solver_logger.reset_timer()
            result, formula_size = solver.solve()
            caller.set_time("smt solving timer", solver.get_time("solving timer"))
            # print("loop: {}, smt: {}".format(cur_index, solver.get_time("solving timer")), end="", flush=True)
            result_dict["size"] += formula_size
            if result == "True":
                # smt solver level result
                print(", ode: {}".format(result_dict["time"]), flush=True)
                caller.logger.stop_timer("solving timer")
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
            max_literal_set_list = caller.strategy_manager.perform_strategy(alpha, assignment, max_bound,
                                                                            new_abstracted_consts,
                                                                            c,
                                                                            caller.time_optimize,
                                                                            z3_boolean_consts,
                                                                            boolean_sub_dict,
                                                                            caller.get_optimize_flag(
                                                                                "formula"))
            caller.logger.stop_timer("max literal timer")

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
                    counter_consts_set.add(Not(c))

            counter_consts = list(counter_consts_set)

            # generate hybrid automaton
            hg = HaGenerator()
            hg.set(max_literal_set_list, max_bound, mapping_info)
            ha, bound_box, l_v = hg.generate()

            # convert and solve
            solver_specific_converter = self.converter
            solver_specific_converter.convert(ha, options, l_v, bound_box)
            solver_result, result_dict["time"] = solver_specific_converter.solve(options["configuration"])
            # caller.set_time("solving timer", result_dict["time"])
            # print(", ode: {}, total: {}".format(result_dict["time"], caller.get_time("solving timer")), flush=True)
            caller.logger.reset_timer_without("goal timer", "solving timer")
        result_dict["result"] = "False"
        caller.logger.stop_timer("solving timer")
        return result_dict


class MergeSolvingStrategy(CommonSolvingStrategy):
    def perform_solving(self, options: dict) -> dict:
        # gets representative l_v and list of bound_box_list
        # returns representative bound_box
        def _make_bound_box(_l_v, _bound_box_list):
            new_bound_box = list()
            for i, _ in enumerate(_l_v):
                max_left_value = float("inf")
                max_right_value = -float("inf")
                for bbl in _bound_box_list:
                    if bbl[i][0] < max_left_value:
                        max_left_value = bbl[i][0]
                    if bbl[i][1] > max_right_value:
                        max_right_value = bbl[i][1]
                assert max_left_value != float("inf")
                assert max_right_value != -float("inf")
                new_bound_box.append([max_left_value, max_right_value])
            return new_bound_box

        def _find_representative_l_v(_l_vs):
            if len(_l_vs) <= 1:
                return _l_vs[0]
            _l_v_set = set(_l_vs[0])
            representative_l_v = _l_vs[0]
            for _i, _l_v in enumerate(_l_vs[1:]):
                _l_v_s = set(_l_v)
                if _l_v_s.issuperset(_l_v_set):
                    representative_l_v = _l_v
            return representative_l_v

        def _unifying_bound_box(_representative_l_v, _l_vs, _bound_box_list):
            _new_bound_box_list = list()
            for bbi, bb in enumerate(_bound_box_list):
                _new_bound_box = list()
                for _v_i, _v in enumerate(_representative_l_v):
                    _given_l_v = _l_vs[bbi]
                    if _v in _given_l_v:
                        _index = _given_l_v.index(_v)
                        _new_bound_box.append(bb[_index])
                    else:
                        _new_bound_box.append([0.0, 0.0])
                _new_bound_box_list.append(_new_bound_box)
            return _new_bound_box_list

        def _merging_ha(_ha_list: list, is_mini_merging=False):
            ha_list = list()
            bound_box_list = list()

            # for integrity, l_vs are all the same
            list_of_l_v = list()
            if len(_ha_list) > 0:
                for i, (ha, l_v, new_bound_box_list) in enumerate(_ha_list):
                    ha.name = "{}_{}".format(ha.name, i)
                    ha_list.append(ha)
                    bound_box_list.append(new_bound_box_list)
                    list_of_l_v.append(l_v)

                representative_l_v = _find_representative_l_v(list_of_l_v)
                unified_bb = _unifying_bound_box(representative_l_v, list_of_l_v, bound_box_list)
                representative_bb = _make_bound_box(representative_l_v, unified_bb)

                if is_mini_merging:
                    print("mini merging ...")
                # nha = merge(*ha_list, chi_optimization=False, syntatic_merging=True)
                nha = new_merge(*ha_list, syntatic_merging=True)
                print(
                    "# HA: {}, modes: {}, transitions: {}".format(len(_ha_list), len(nha.modes), len(nha.transitions)),
                    flush=True)
                return nha, representative_l_v, representative_bb

        assert "info_dict" in options
        assert "mapping_info" in options
        assert "tau_info" in options
        assert "caller" in options
        assert "all_consts" in options

        info_dict = options["info_dict"]
        mapping_info = options["mapping_info"]
        tau_info = options["tau_info"]
        opt_var_info = options["opt_var_info"]
        caller = options["caller"]
        all_consts = options["all_consts"]

        caller.set_time("solving timer", 0)

        # pre-processing
        # boolean_start = timer()
        # heuristic: removing mapping constraint part.
        trans_all_consts = list()
        trans_all_consts.extend(all_consts.children[0:2])

        for tchi in tau_info:
            trans_all_consts.append(Eq(tchi, tau_info[tchi]))
        for opt_chi in opt_var_info:
            trans_all_consts.append(Eq(opt_chi, opt_var_info[opt_chi]))

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
                merged_ha, merged_l_v, merged_bb = _merging_ha(hybrid_automata_queue)
                solver_specific_converter = self.converter
                solver_specific_converter.convert(merged_ha, options, merged_l_v, merged_bb)
                result_dict["result"], result_dict["time"] = solver_specific_converter.solve()
                # result_dict["result"], result_dict["time"] = self.solving_function(hybrid_automata_queue)
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
            max_literal_set_list = caller.strategy_manager.perform_strategy(alpha, assignment, max_bound,
                                                                            new_abstracted_consts,
                                                                            c,
                                                                            caller.time_optimize,
                                                                            z3_boolean_consts,
                                                                            boolean_sub_dict,
                                                                            caller.get_optimize_flag(
                                                                                "formula"))
            caller.logger.stop_timer("max literal timer")

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
                    counter_consts_set.add(Not(c))

            counter_consts = list(counter_consts_set)

            hg = HaGenerator()
            hg.set(max_literal_set_list, max_bound, mapping_info)
            ha, bound_box, l_v = hg.generate()
            # ha, conf_dict, l_v, new_bound_box_list = caller.run(max_literal_set_list, max_bound, mapping_info)
            hybrid_automata_queue.append((ha, l_v, bound_box))
            caller.logger.reset_timer_without("goal timer")
