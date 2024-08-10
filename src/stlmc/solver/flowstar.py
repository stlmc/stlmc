import asyncio
import random
from functools import singledispatch
from typing import *

from sympy import simplify, Equality

from ..constraints.constraints import *
from ..exception.exception import *
from ..hybrid_automaton.converter import AbstractConverter
from ..hybrid_automaton.hybrid_automaton import HybridAutomaton
from ..hybrid_automaton.utils import calc_initial_terminal_modes, vars_in_ha
from ..objects.configuration import Configuration
from ..solver.assignment import Assignment
from ..solver.ode_solver import *
from ..solver.ode_utils import expr_to_sympy, expr_to_sympy_inequality
from ..util.logger import Logger


class FlowStar:
    def __init__(self):
        self.result = None
        self.logger = Logger()

    def _check_if_string_in_file(self, file_name, string_to_search):
        """ Check if any line in the file contains given string """
        # Open the file in read only mode
        with open(file_name, 'r') as read_obj:
            # Read all lines in the file one by one
            for line in read_obj:
                # For each line, check if line contains the string
                if string_to_search in line:
                    return True
        return False

    async def _run_command(self, model_string):
        model_file = "./fs_model{}.model".format(random.random())
        outputs = "./outputs"
        images = "./images"
        counterexamples = "./counterexamples"

        f = open(model_file, 'w')
        f.write(model_string)
        f.close()

        proc = await asyncio.create_subprocess_exec(
            './3rd_party/flowstar', model_file,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE)

        # self.logger.start_timer("solving timer")
        stdout, stderr = await proc.communicate()
        # self.logger.stop_timer("solving timer")
        # print(f'[exited with {proc.returncode}]')
        # if stdout:
        #    print(f'[stdout]\n{stdout.decode()}')
        # if stderr:
        #    print(f'[stderr]\n{stderr.decode()}')

        # if os.path.isdir(outputs):
        #     shutil.rmtree(outputs)
        #
        # if os.path.isdir(counterexamples):
        #     shutil.rmtree(counterexamples)
        #
        # if os.path.isdir(images):
        #     shutil.rmtree(images)

        #if os.path.isfile(model_file):
        #    os.remove(model_file)
        std_str = str(stdout.decode())
        err_str = str(stderr.decode())
        out_str = std_str + err_str

        if "Error" in out_str:
            raise OperationError(out_str)

        if "Computation not completed" in out_str:
            log_id = random.random()
            print("result is not guaranteed, flowstar cannot finish computation for more information see {}.log".format(log_id))
            f = open("{}.log".format(log_id), "w")
            f.write(out_str)
            f.close()

        if "UNSAFE" in out_str:
            self.result = True
        else:
            self.result = False
        # if os.path.isfile(result_file):
        #     self.result = self._check_if_string_in_file(result_file, "error")

        return stdout.decode().strip()

    async def _run(self, model_string, time_out):
        try:
            await asyncio.wait_for(self._run_command(model_string), timeout=time_out)
        except asyncio.TimeoutError:
            print('timeout!')

    def run(self, model_string, time_out):
        asyncio.run(self._run(model_string, time_out))



class FlowStarConverter(AbstractConverter):
    def preprocessing(self, ha: HybridAutomaton):
        initial_modes, _ = calc_initial_terminal_modes(ha)
        # add unique init mode
        start_mode = ha.new_mode("start")

        for init_mode in initial_modes:
            ha.new_transition("start_2_{}__id_{}".format(init_mode.name, id(init_mode)), start_mode, init_mode)

        ff = Real("ff")
        zero = RealVal("0")

        # ff > 0
        ff_inv = Gt(ff, zero)

        for mode in ha.modes:
            mode.set_dynamic(ff, zero)
            mode.set_invariant(ff_inv)

    def solve(self, config: Configuration):
        flowstar_core_solver = FlowStar()

        reach_section = config.get_section("reachable-solver")
        time_out = reach_section.get_value("time-out")

        flowstar_core_solver.run(self.convert_result, float(time_out))
        # solving_time = flowstar_core_solver.logger.get_duration_time("solving timer")
        if flowstar_core_solver.result:
            return False, 0.0
        else:
            return True, 0.0

    def convert(self, ha: HybridAutomaton, setting: Dict, lv: List, bound_box: List):
        self.preprocessing(ha)
        initial_modes, terminal_modes = calc_initial_terminal_modes(ha)

        modes_str_list = list()
        for mode in ha.modes:
            mode_str = "{}__id_{}{{\n".format(mode.name, id(mode))
            mode_str += "poly ode 1\n{"

            for (var, exp) in mode.dynamics:
                mode_str += "{}\' = {}\n".format(var, str(simplify(expr_to_sympy(exp)))).replace("**", "^")
            mode_str += "}\n"

            mode_str += "inv {\n"
            for inv in mode.invariant:
                mode_str += "{}\n".format(expr_to_sympy_inequality(inv)).replace(">", ">=").replace("<",
                                                                                                    "<=").replace(
                    ">==", ">=").replace("<==", "<=").replace("**", "^")
            mode_str += "}\n}"
            modes_str_list.append(mode_str)

        modes_str = "modes {{\n {}\n}}\n".format("\n".join(modes_str_list))

        var_set = vars_in_ha(ha)
        var_str = "state var "
        for i, v in enumerate(var_set):
            if i == len(var_set) - 1:
                var_str += v.id
            else:
                var_str += v.id + ", "

        # setting_child_str = ""

        # setting_ordering = ["fixed steps", "time", "remainder estimation", "identity precondition", "gnuplot octagon",
        #                     "adaptive orders", "cutoff", "precision", "no output", "max jumps"]

        config = setting["configuration"]
        common_section = config.get_section("common")
        gen_result = common_section.get_value("visualize")

        flowstar_section = config.get_section("flowstar")

        if not flowstar_section.is_argument_in("output-variables"):
            raise NotSupportedError("output variables must be specified")

        variables = flowstar_section.get_value("output-variables")
        # var_list = list(var_set)
        var_list = variables.split(",")

        if len(var_list) != 2:
            raise NotSupportedError("there must be 2 output variables")
        variables = "{}, {}".format(var_list[0], var_list[1])

        is_fixed_order = flowstar_section.is_argument_in("fixed-order")
        is_adaptive_step_min = flowstar_section.is_argument_in("adaptive-step-min")
        is_adaptive_step_max = flowstar_section.is_argument_in("adaptive-step-max")

        is_opt1 = is_fixed_order and is_adaptive_step_max and is_adaptive_step_min


        is_fixed_step = flowstar_section.is_argument_in("fixed-step")
        is_adaptive_order_min = flowstar_section.is_argument_in("adaptive-order-min")
        is_adaptive_order_max = flowstar_section.is_argument_in("adaptive-order-max")


        is_opt2 = is_fixed_step and is_adaptive_order_min and is_adaptive_order_max

        if not is_opt1 and not is_opt2:
            raise NotSupportedError("must choose one of option 1 and option 2")

        setting_str = list()
        if is_opt1:

            step_min = flowstar_section.get_value("adaptive-step-min")
            step_max = flowstar_section.get_value("adaptive-step-max")

            setting_str.append("adaptive steps {{ min {}, max {} }}".format(step_min, step_max))
            setting_str.append("time {}".format(flowstar_section.get_value("max-time")))
            setting_str.append("remainder estimation {}".format(flowstar_section.get_value("remainder-estimation")))

            method = flowstar_section.get_value("precondition-method")
            method = method.replace("-", " ")
            setting_str.append("{}".format(method))
            setting_str.append("gnuplot octagon {}".format(variables))

            setting_str.append("fixed orders {}".format(flowstar_section.get_value("fixed-order")))
            setting_str.append("cutoff {}".format(flowstar_section.get_value("cutoff")))
            setting_str.append("precision {}".format(flowstar_section.get_value("precision")))

            output = flowstar_section.get_value("output")

            if gen_result == "on":
                if output == "":
                    setting_str.append("no output")
                else:
                    setting_str.append("output {}".format(output))
            else:
                setting_str.append("no output")
            setting_str.append("max jumps {}".format(flowstar_section.get_value("max-jump")))

        else:
            # adaptive - order - min = 5
            # adaptive - order - max = 10
            # fixed - step = 0.01
            setting_str.append("fixed steps {}".format(flowstar_section.get_value("fixed-step")))
            setting_str.append("time {}".format(flowstar_section.get_value("max-time")))
            setting_str.append("remainder estimation {}".format(flowstar_section.get_value("remainder-estimation")))

            method = flowstar_section.get_value("precondition-method")
            method = method.replace("-", " ")
            setting_str.append("{}".format(method))
            setting_str.append("gnuplot octagon {}".format(variables))

            order_min = flowstar_section.get_value("adaptive-order-min")
            order_max = flowstar_section.get_value("adaptive-order-max")
            setting_str.append("adaptive orders {{ min {}, max {} }}".format(order_min, order_max))
            setting_str.append("cutoff {}".format(flowstar_section.get_value("cutoff")))
            setting_str.append("precision {}".format(flowstar_section.get_value("precision")))

            output = flowstar_section.get_value("output")

            if gen_result == "on":
                if output == "":
                    setting_str.append("no output")
                else:
                    setting_str.append("output {}".format(output))
            else:
                setting_str.append("no output")

            setting_str.append("max jumps {}".format(flowstar_section.get_value("max-jump")))

        # conf_dict["fixed steps"] = "0.01"
        # conf_dict["time"] = "1"
        # conf_dict["remainder estimation"] = "1e-2"
        # conf_dict["identity precondition"] = ""
        # conf_dict["gnuplot octagon"] = ""
        # conf_dict["adaptive orders"] = "{ min 4 , max 8 }"
        # conf_dict["cutoff"] = "1e-12"
        # conf_dict["precision"] = "53"
        # conf_dict["no output"] = ""
        # conf_dict["max jumps"] = "10"

        # remainder - estimation = 1e-2
        # precondition - method = "identity-precondition"  # "qr-precondition"
        # cutoff = 1e-15
        # precision = 100
        # output = "no-output"  # "output-file-name"
        # out - variables =
        # print = "on"  # "off"
        # max - time = 100
        #
        # # option 1) fixed order + adaptive step
        # fixed - order = 10
        # adaptive - step - min = 5
        # adaptive - step - max = 10
        #
        # # option 2) adaptive order + fixed step
        # adaptive - order - min = 5
        # adaptive - order - max = 10
        # fixed - step = 0.01
        #
        # # "off":option 1, "on": option 2
        # variant - order = "on"  # "off"

        setting_str = "setting {{\n {}\n print on \n}}\n".format("\n".join(setting_str))

        trans_str_list = list()
        for transition in ha.transitions:
            t_str = "{}__id_{} -> {}__id_{}\n".format(transition.src.name,
                                                      id(transition.src),
                                                      transition.trg.name,
                                                      id(transition.trg))

            t_str += "guard {\n"
            for guard in transition.guard:
                simplified_guard = expr_to_sympy_inequality(guard)
                _str = ""
                if isinstance(simplified_guard, Equality):
                    _str = "{} = {}\n".format(simplified_guard.lhs, simplified_guard.rhs)
                else:
                    _str = "{}\n".format(simplified_guard)
                t_str += _str.replace(">", ">=").replace("<", "<=").replace(">==", ">=").replace("<==", "<=").replace("**", "^")
            t_str += "}\n"

            # reset
            t_str += "reset {\n"
            for reset in transition.reset:
                t_str += "{}\n".format(flowStarinfixReset(reset))
            t_str += "}\n"

            t_str += "parallelotope aggregation { }\n"
            trans_str_list.append(t_str)
            #         whole_r_str = flowStarinfixReset(t.reset)
            #         for r_str in whole_r_str.split("&"):
            #             t_str += "{}\n".format(r_str)
            #         t_str += "}\n"
        # for i, t in enumerate(ha.transitions):
        #     t_str = "{}__id_{} -> {}__id_{}\n".format(t.src.name, id(t.src), t.trg.name, id(t.trg))
        #     guard = t.guard
        #     if guard is not None:
        #         t_str += "guard {\n"
        #         if isinstance(guard, And):
        #             for g in guard.children:
        #                 etsi = expr_to_sympy_inequality(g)
        #                 etsi_str = "{}".format(etsi)
        #                 if isinstance(etsi, Equality):
        #                     etsi_str = "{} = {}".format(etsi.lhs, etsi.rhs)
        #                 t_str += "{}\n".format(etsi_str).replace(">", ">=").replace("<",
        #                                                                             "<=").replace(
        #                     ">==", ">=").replace("<==", "<=").replace("**", "^")
        #         else:
        #             etsi = expr_to_sympy_inequality(guard)
        #             etsi_str = "{}".format(etsi)
        #             if isinstance(etsi, Equality):
        #                 etsi_str = "{} = {}".format(etsi.lhs, etsi.rhs)
        #             t_str += "{}\n".format(etsi_str).replace(">", ">=").replace("<",
        #                                                                         "<=").replace(
        #                 ">==", ">=").replace("<==", "<=").replace("**", "^")
        #         # whole_g_str = infix(ha.trans[t].guard)
        #         # for g_str in whole_g_str.split("&"):
        #         #     t_str += "{}\n".format(g_str)
        #         t_str += "}\n"
        #     else:
        #         t_str += "guard {}"
        #
        #     if t.reset is not None:
        #         t_str += "reset {\n"
        #         whole_r_str = flowStarinfixReset(t.reset)
        #         for r_str in whole_r_str.split("&"):
        #             t_str += "{}\n".format(r_str)
        #         t_str += "}\n"
        #     else:
        #         t_str += "reset {}"
        #     t_str += "parallelotope aggregation { }\n"
        #     trans_str_list.append(t_str)

        trans_str = "jumps {{\n {} \n }}\n".format("\n".join(trans_str_list))

        init_child_str = ""
        for start_mode in initial_modes:
            init_child_str += "{}__id_{} {{".format(start_mode.name, id(start_mode))
            for iv, v in enumerate(lv):
                init_child_str += "{} in [{}, {}]\n".format(v, bound_box[iv][0], bound_box[iv][1])
            init_child_str += " ff in [1.0, 1.0]}\n"

        init_str = "init {{\n {}\n}}\n".format(init_child_str)
        # for iv, v in enumerate(self.var_list_ordering):
        #     init_str += "{} in [{}, {}]\n".format(v, self.init_bound[iv][0], self.init_bound[iv][1])
        # init_str += " ff in [2.0, 2.0]}\n}\n"

        unsafe_str = ""

        terminal_modes_str = list()
        for m in terminal_modes:
            terminal_modes_str.append("{}__id_{}".format(m.name, id(m)))

        # print(terminal_modes_str)
        for m in ha.modes:
            real_name = "{}__id_{}".format(m.name, id(m))
            if real_name in terminal_modes_str:
                unsafe_str += "{}{{}}\n".format(real_name)
            else:
                unsafe_str += "{}{{ ff  <= 0 }}\n".format(real_name)

        self.convert_result = "hybrid reachability {{\n {}\n {}\n {}\n {}\n {}\n}}\n unsafe {{\n {} \n }}\n".format(
            var_str,
            setting_str,
            modes_str,
            trans_str,
            init_str,
            unsafe_str)


class FlowStarSolverNaive(CommonOdeSolver):
    def __init__(self):
        assert "merging_strategy" in self.conf_dict
        underlying_solver = NormalSolvingStrategy(flowstar_solver)
        if self.conf_dict["merging_strategy"]:
            underlying_solver = MergeSolvingStrategy(flowstar_merging_solver)
        CommonOdeSolver.__init__(self, NaiveStrategyManager(), underlying_solver)

    def make_assignment(self):
        pass

    def clear(self):
        pass


class FlowStarSolverReduction(CommonOdeSolver):
    def __init__(self):
        assert "merging_strategy" in self.conf_dict
        underlying_solver = NormalSolvingStrategy(flowstar_solver)
        if self.conf_dict["merging_strategy"]:
            underlying_solver = MergeSolvingStrategy(flowstar_merging_solver)
        CommonOdeSolver.__init__(self, ReductionStrategyManager(), underlying_solver)

    def make_assignment(self):
        pass

    def clear(self):
        pass


class FlowStarSolverUnsatCoreMerging(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager(), MergeSolvingStrategy(FlowStarConverter()))

    def clear(self):
        self.strategy_manager.clear()


class FlowStarSolverUnsatCore(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager(), NormalSolvingStrategy(FlowStarConverter()))

    def clear(self):
        self.strategy_manager.clear()


class FlowStarAssignment(Assignment):
    def __init__(self, flowstar_counterexample):
        self.counterexample = flowstar_counterexample

    def get_assignments(self):
        print(self.counterexample)

    def eval(self, const):
        pass


@singledispatch
def flowStarinfixReset(const: Constraint):
    return str(const)


@flowStarinfixReset.register(Variable)
def _(const: Variable):
    return const.id


@flowStarinfixReset.register(And)
def _(const: And):
    return '&'.join([flowStarinfixReset(c) for c in const.children])


@flowStarinfixReset.register(Geq)
def _(const: Geq):
    return flowStarinfixReset(const.left) + " >= " + flowStarinfixReset(const.right)


@flowStarinfixReset.register(Gt)
def _(const: Gt):
    return flowStarinfixReset(const.left) + " >= " + flowStarinfixReset(const.right)


@flowStarinfixReset.register(Leq)
def _(const: Leq):
    return flowStarinfixReset(const.left) + " <= " + flowStarinfixReset(const.right)


@flowStarinfixReset.register(Lt)
def _(const: Geq):
    return flowStarinfixReset(const.left) + " <= " + flowStarinfixReset(const.right)


@flowStarinfixReset.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Real):
        return "{}\' := {}".format(const.left.id, flowStarinfixReset(const.right))
    elif isinstance(const.left, Int):
        return "{}\' := {}".format(const.left.id, flowStarinfixReset(const.right))
    else:
        raise NotSupportedError()


# cannot support this
@flowStarinfixReset.register(Neq)
def _(const: Geq):
    return flowStarinfixReset(const.left) + " >= " + flowStarinfixReset(const.right) + " & " + flowStarinfixReset(
        const.left) + " <= " + flowStarinfixReset(
        const.right)


@flowStarinfixReset.register(Add)
def _(const: Add):
    return "(" + flowStarinfixReset(const.left) + " + " + flowStarinfixReset(const.right) + ")"


@flowStarinfixReset.register(Sub)
def _(const: Sub):
    return "(" + flowStarinfixReset(const.left) + " - " + flowStarinfixReset(const.right) + ")"


@flowStarinfixReset.register(Neg)
def _(const: Neg):
    return "(-" + flowStarinfixReset(const.child) + ")"


@flowStarinfixReset.register(Mul)
def _(const: Mul):
    return "(" + flowStarinfixReset(const.left) + " * " + flowStarinfixReset(const.right) + ")"


@flowStarinfixReset.register(Div)
def _(const: Div):
    return "(" + flowStarinfixReset(const.left) + " / " + flowStarinfixReset(const.right) + ")"


# maybe not supported
@flowStarinfixReset.register(Pow)
def _(const: Pow):
    return "(" + flowStarinfixReset(const.left) + " ** " + flowStarinfixReset(const.right) + ")"


@flowStarinfixReset.register(Forall)
def _(const: Forall):
    return flowStarinfixReset(const.const)
