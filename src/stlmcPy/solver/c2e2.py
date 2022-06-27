import asyncio
import os
import shutil

from ..util.logger import Logger
from functools import singledispatch
from typing import *

from sympy import simplify, Equality

from ..constraints.constraints import *
from ..exception.exception import NotSupportedError
from ..hybrid_automaton.converter import AbstractConverter
from ..hybrid_automaton.hybrid_automaton import HybridAutomaton
from ..hybrid_automaton.utils import calc_initial_terminal_modes, vars_in_ha
from ..solver.assignment import Assignment
from ..solver.ode_solver import CommonOdeSolver, NaiveStrategyManager, ReductionStrategyManager, \
    UnsatCoreStrategyManager, NormalSolvingStrategy
from ..solver.ode_utils import expr_to_sympy, expr_to_sympy_inequality


class C2E2:
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
        model_file = "##tmptmp##c2e2model.hyxml"
        work_dir = "../work-dir"

        f = open(model_file, 'w')
        f.write(model_string)
        f.close()

        if not os.path.isdir(work_dir):
            os.mkdir(work_dir)

        proc = await asyncio.create_subprocess_exec(
            'python3', './c2e2/c2e2/src/main.py', '-f', model_file, '-a', 'verify',
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE)

        # print(type(proc))
        self.logger.start_timer("solving timer")
        stdout, stderr = await proc.communicate()
        self.logger.stop_timer("solving timer")

        print(f'[exited with {proc.returncode}]')
        if stdout:
            print(f'[stdout]\n{stdout.decode()}')
        if stderr:
            print(f'[stderr]\n{stderr.decode()}')

        # call_c2e2(["wow", "-f", model_file, "-a", "verify"])
        # if os.path.isfile(model_file):
        #     os.remove(model_file)

        res = ""
        if os.path.isdir(work_dir):
            f = open("{}/log.txt".format(work_dir), "r")
            res = f.read()
            shutil.rmtree(work_dir)

        if "Unsafe" in res:
            self.result = True
        else:
            self.result = False

    async def _run(self, model_string):
        try:
            return await asyncio.wait_for(self._run_command(model_string), timeout=100.0)
        except asyncio.TimeoutError:
            print('timeout!')

    def run(self, model_string):
        return asyncio.run(self._run(model_string))


class C2E2Converter(AbstractConverter):
    def solve(self):
        c2e2_core_solver = C2E2()
        c2e2_core_solver.run(self.convert_result)
        solving_time = c2e2_core_solver.logger.get_duration_time("solving timer")
        if c2e2_core_solver.result:
            return False, solving_time
        else:
            return True, solving_time

    def preprocessing(self, ha: HybridAutomaton):

        ffggee = Real("ffggee")
        zero = RealVal("0")
        one = RealVal("1")

        for mode in ha.modes:
            mode.set_dynamic(ffggee, zero)

        initial_modes, terminal_modes = calc_initial_terminal_modes(ha)

        # ffggee < 0
        non_error_const = Lt(ffggee, zero)
        # ffggee > 0
        error_const = Gt(ffggee, zero)
        # ffggee = 1 : reset
        error_on = Eq(ffggee, one)

        for init_mode in initial_modes:
            init_mode.set_invariant(non_error_const)

            for init_trans in init_mode.outgoing:
                init_trans.set_guard(non_error_const)

        for term_mode in terminal_modes:
            term_mode.set_invariant(error_const)

            for term_trans in term_mode.incoming:
                term_trans.set_reset(error_on)

        for transition in ha.transitions:
            to_be_removed_reset = set()
            for reset in transition.reset:
                assert isinstance(reset, Eq)
                if reset.left == reset.right:
                    to_be_removed_reset.add(reset)
            transition.remove_resets(to_be_removed_reset)

        _, terminal_modes = calc_initial_terminal_modes(ha)
        var_set = vars_in_ha(ha)

        # modes in c2e2 always have dynamics
        for term_mode in terminal_modes:
            for v in var_set:
                term_mode.set_dynamic(v, RealVal("0"))

    def convert(self, ha: HybridAutomaton, setting: Dict, variable_ordering: List, bound_box: List):
        def _make_conf_dict(_setting: dict):
            _dict = dict()
            keywords = ["step", "time", "kvalue"]
            for keyword in keywords:
                if keyword in _setting:
                    _dict[keyword] = _setting[keyword]
            return _dict

        self.preprocessing(ha)
        print("after preprocessing")
        print(ha)
        modes_str_list = list()

        initial_modes, terminal_modes = calc_initial_terminal_modes(ha)

        # there should be only one initial mode
        # assert len(initial_modes) == 1

        # get all variables and specify their types
        for mode in ha.modes:
            mode_str = " <mode id=\"{}\" initial=\"False\" name=\"{}\">\n".format(id(mode), mode.name)
            if mode in initial_modes:
                mode_str = " <mode id=\"{}\" initial=\"True\" name=\"{}\">\n".format(id(mode), mode.name)

            for (var, exp) in mode.dynamics:
                mode_str += "  <dai equation=\"{}_dot = {}\"/>\n".format(var, simplify(expr_to_sympy(exp)))

            for inv in mode.invariant:
                simplified_inv = simplify(expr_to_sympy_inequality(inv))
                _str = ""
                if isinstance(simplified_inv, Equality):
                    _str = "{} &lt;= {} &amp;&amp; {} &gt;= {}".format(simplified_inv.lhs, simplified_inv.rhs,
                                                                       simplified_inv.lhs, simplified_inv.rhs)
                else:
                    _str = "{}".format(simplified_inv)
                _mode_str = _str.replace(">", "&gt;").replace(">=", "&gt;=").replace("<", "&lt;").replace("<=", "&lt;=")
                mode_str += "  <invariant equation=\"{}\"/>\n".format(_mode_str)
            mode_str += " </mode>\n"
            modes_str_list.append(mode_str)

        modes_str = "\n".join(modes_str_list)

        var_str_list = list()
        var_set = vars_in_ha(ha)
        for v in var_set:
            var_str_list.append("  <variable name=\"{}\" scope=\"LOCAL_DATA\" type=\"Real\"/>".format(v.id))
        var_str = "\n".join(var_str_list)

        trans_str_list = list()
        for i, transition in enumerate(ha.transitions):
            t_str = "  <transition destination=\"{}\" id=\"{}\" source=\"{}\">\n".format(id(transition.trg), i,
                                                                                         id(transition.src))
            for guard in transition.guard:
                simplified_guard = simplify(expr_to_sympy_inequality(guard))
                _str = ""
                if isinstance(simplified_guard, Equality):
                    _str = "{} &lt;= {} &amp;&amp; {} &gt;= {}".format(simplified_guard.lhs, simplified_guard.rhs,
                                                                       simplified_guard.lhs, simplified_guard.rhs)
                else:
                    _str = "{}".format(simplified_guard)
                g_str = _str.replace(">", "&gt;").replace(">=", "&gt;=").replace("<", "&lt;").replace("<=", "&lt;=")
                t_str += "   <guard equation=\"{}\"/>\n".format(g_str)

            for reset in transition.reset:
                assert isinstance(reset, Eq)
                assert isinstance(reset.left, Variable)

                t_str += "   <action equation=\"{}\"/>\n".format(C2E2infixReset(reset))
            t_str += "  </transition>"
            trans_str_list.append(t_str)

        trans_str = "\n".join(trans_str_list)

        # get unique initial mode
        # init_mode = initial_modes.pop()

        init_str_list = list()
        for i, v in enumerate(variable_ordering):
            init_str_list.append("{} &gt;= {} &amp;&amp; {} &lt;= {}".format(v, bound_box[i][0], v, bound_box[i][1]))
        init_str = "&amp;&amp;".join(init_str_list)

        c2e2_setting = _make_conf_dict(setting)

        prop_str = ""
        for i, init_mode in enumerate(initial_modes):
            prop_str += '''<property initialSet = \"{}: {} &amp;&amp; ffggee == -1\" name = \"error_cond_{}\" type = \"0\" unsafeSet = \"ffggee &gt; 0\">
            <parameters kvalue = \"{}\" timehorizon = \"{}\" timestep = \"{}\"/>
            </property>
            '''.format(init_mode.name, init_str, i, c2e2_setting["kvalue"], c2e2_setting["time"], c2e2_setting["step"])

        self.convert_result = "<?xml version='1.0' encoding='utf-8'?>\n<!DOCTYPE hyxml>\n<hyxml type=\"Model\">\n <automaton name=\"{}\">\n{}\n{}\n{}\n </automaton>\n <composition automata=\"{}\"/>\n{}\n</hyxml>".format(
            ha.name, var_str, modes_str, trans_str, ha.name, prop_str)



class C2E2SolverNaive(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, NaiveStrategyManager())

    def run(self, s_f_list, max_bound, sigma):
        return c2e2_run(s_f_list, max_bound, sigma)

    def make_assignment(self):
        pass

    def clear(self):
        pass


class C2E2SolverReduction(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, ReductionStrategyManager())

    def make_assignment(self):
        pass

    def clear(self):
        pass


class C2E2SolverUnsatCore(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager(), NormalSolvingStrategy(C2E2Converter()))

    def make_assignment(self):
        pass

    def clear(self):
        pass


class C2E2Assignment(Assignment):
    def __init__(self, spaceex_counterexample):
        self.spaceex_counterexample = spaceex_counterexample

    def get_assignments(self):
        print(self.spaceex_counterexample)

    def eval(self, const):
        pass


@singledispatch
def C2E2infix(const: Constraint):
    return str(const)


@C2E2infix.register(Variable)
def _(const: Variable):
    return const.id


@C2E2infix.register(And)
def _(const: And):
    return '&amp;&amp;'.join([C2E2infix(c) for c in const.children])


@C2E2infix.register(Geq)
def _(const: Geq):
    return C2E2infix(const.left) + " &gt;= " + C2E2infix(const.right)


@C2E2infix.register(Gt)
def _(const: Geq):
    return C2E2infix(const.left) + " &gt; " + C2E2infix(const.right)


@C2E2infix.register(Leq)
def _(const: Geq):
    return C2E2infix(const.left) + " &lt;= " + C2E2infix(const.right)


@C2E2infix.register(Lt)
def _(const: Geq):
    return C2E2infix(const.left) + " &lt; " + C2E2infix(const.right)


@C2E2infix.register(Eq)
def _(const: Eq):
    return C2E2infix(const.left) + " == " + C2E2infix(const.right)


# cannot support this
@C2E2infix.register(Neq)
def _(const: Geq):
    return C2E2infix(const.left) + " &gt;= " + C2E2infix(const.right) + " &amp;&amp; " + C2E2infix(
        const.left) + " &lt; " + C2E2infix(
        const.right)


@C2E2infix.register(Add)
def _(const: Add):
    return "(" + C2E2infix(const.left) + " + " + C2E2infix(const.right) + ")"


@C2E2infix.register(Sub)
def _(const: Sub):
    return "(" + C2E2infix(const.left) + " - " + C2E2infix(const.right) + ")"


@C2E2infix.register(Neg)
def _(const: Neg):
    return "(-" + C2E2infix(const.child) + ")"


@C2E2infix.register(Mul)
def _(const: Mul):
    return "(" + C2E2infix(const.left) + " * " + C2E2infix(const.right) + ")"


@C2E2infix.register(Div)
def _(const: Div):
    return "(" + C2E2infix(const.left) + " / " + C2E2infix(const.right) + ")"


# maybe not supported
@C2E2infix.register(Pow)
def _(const: Pow):
    return "(" + C2E2infix(const.left) + " ** " + C2E2infix(const.right) + ")"


@C2E2infix.register(Forall)
def _(const: Forall):
    return C2E2infix(const.const)


### start


@singledispatch
def C2E2infixReset(const: Constraint):
    return str(const)


@C2E2infixReset.register(Variable)
def _(const: Variable):
    return const.id


@C2E2infixReset.register(And)
def _(const: And):
    return '&amp;&amp;'.join([C2E2infixReset(c) for c in const.children])


@C2E2infixReset.register(Geq)
def _(const: Geq):
    return C2E2infixReset(const.left) + " &gt;= " + C2E2infixReset(const.right)


@C2E2infixReset.register(Gt)
def _(const: Geq):
    return C2E2infixReset(const.left) + " &gt; " + C2E2infixReset(const.right)


@C2E2infixReset.register(Leq)
def _(const: Geq):
    return C2E2infixReset(const.left) + " &lt;= " + C2E2infixReset(const.right)


@C2E2infixReset.register(Lt)
def _(const: Geq):
    return C2E2infixReset(const.left) + " &lt; " + C2E2infixReset(const.right)


@C2E2infixReset.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Real):
        r_str = C2E2infixReset(const.right)
        if const.left.id == r_str:
            return ""
        return "{} = {}".format(const.left.id, r_str)
    elif isinstance(const.left, Int):
        r_str = C2E2infixReset(const.right)
        if const.left.id == r_str:
            return ""
        return "{} = {}".format(const.left.id, r_str)
    else:
        raise NotSupportedError()


# cannot support this
@C2E2infixReset.register(Neq)
def _(const: Geq):
    return C2E2infixReset(const.left) + " &gt;= " + C2E2infixReset(const.right) + " &amp;&amp; " + C2E2infixReset(
        const.left) + " &lt; " + C2E2infixReset(
        const.right)


@C2E2infixReset.register(Add)
def _(const: Add):
    return "(" + C2E2infixReset(const.left) + " + " + C2E2infixReset(const.right) + ")"


@C2E2infixReset.register(Sub)
def _(const: Sub):
    return "(" + C2E2infixReset(const.left) + " - " + C2E2infixReset(const.right) + ")"


@C2E2infixReset.register(Neg)
def _(const: Neg):
    return "(-" + C2E2infixReset(const.child) + ")"


@C2E2infixReset.register(Mul)
def _(const: Mul):
    return "(" + C2E2infixReset(const.left) + " * " + C2E2infixReset(const.right) + ")"


@C2E2infixReset.register(Div)
def _(const: Div):
    return "(" + C2E2infixReset(const.left) + " / " + C2E2infixReset(const.right) + ")"


# maybe not supported
@C2E2infixReset.register(Pow)
def _(const: Pow):
    return "(" + C2E2infixReset(const.left) + " ** " + C2E2infixReset(const.right) + ")"


@C2E2infixReset.register(Forall)
def _(const: Forall):
    return C2E2infixReset(const.const)

# start
