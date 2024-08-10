import asyncio
import random
from functools import singledispatch

from ..exception.exception import NotSupportedError
from ..hybrid_automaton.hybrid_automaton import HybridAutomaton
from ..solver.assignment import Assignment
from ..solver.ode_solver import *
from ..util.logger import Logger


class SpaceEx:
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

    async def _run_command(self, model_string, conf_string):
        file_id = random.random()
        model_file = "spaceex_tmp_model{}.xml".format(file_id)
        config_file = "spaceex_tmp_conf{}.cfg".format(file_id)
        result_file = 'spaceex_tmp_result{}'.format(file_id)

        f = open(model_file, 'w')
        f.write(model_string)
        f.close()

        f = open(config_file, 'w')
        f.write(conf_string)
        f.close()

        proc = await asyncio.create_subprocess_exec(
            './3rd_party/bin/spaceex', '-g', config_file, '-m', model_file, '-o', result_file,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE)

        self.logger.start_timer("solving timer")
        stdout, stderr = await proc.communicate()
        self.logger.stop_timer("solving timer")

        # print(f'[exited with {proc.returncode}]')
        # if stdout:
        #     print(f'[stdout]\n{stdout.decode()}')
        # if stderr:
        #     print(f'[stderr]\n{stderr.decode()}')

        error_msg = str(stderr.decode())
        if "ERROR" in error_msg:
            raise NotSupportedError("spaceex error ({})".format(error_msg))
        # if os.path.isfile(model_file):
        #     os.remove(model_file)

        # if os.path.isfile(config_file):
        #     os.remove(config_file)

        # if os.path.isfile(result_file):
        #     self.result = self._check_if_string_in_file(result_file, "error")
        #     os.remove(result_file)

        result_str = str(stdout.decode().strip())
        unsat_str = "Forbidden states are not reachable."
        sat_str = "Forbidden states are reachable."
        if sat_str in result_str:
            self.result = True

        if unsat_str in result_str:
            self.result = False

    async def _run(self, model_string, conf_string, time_out):
        try:
            await asyncio.wait_for(self._run_command(model_string, conf_string), timeout=time_out)
        except asyncio.TimeoutError:
            print('timeout!')

    def run(self, model_string, conf_string, time_out):
        asyncio.run(self._run(model_string, conf_string, time_out))




class SpaceExConverter(AbstractConverter):
    def solve(self, config: Configuration):
        spaceex_core_solver = SpaceEx()
        assert len(self.convert_result) == 2
        reach_section = config.get_section("reachable-solver")
        time_out = reach_section.get_value("time-out")

        spaceex_core_solver.run(self.convert_result[0], self.convert_result[1], float(time_out))
        solving_time = spaceex_core_solver.logger.get_duration_time("solving timer")
        if spaceex_core_solver.result:
            return False, solving_time
        else:
            return True, solving_time

    def preprocessing(self, ha: HybridAutomaton):
        pass

    def convert(self, ha: HybridAutomaton, setting: Dict, variable_ordering: List, bound_box: List):
        def _make_init_string(_variable_ordering: List, _bound_box: List):
            _const_set = set()
            for _var_index, _var in enumerate(_variable_ordering):
                # _lower = Geq(_var, _bound_box[_var_index][0])
                # _upper = Leq(_var, _bound_box[_var_index][1])
                # _eq = str(_var) + "==" + str(_bound_box[_var_index][1])
                _lower = str(_var) + ">=" + str(_bound_box[_var_index][0])
                _upper = str(_var) + "<=" + str(_bound_box[_var_index][1])

                _const_set.add(_lower)
                _const_set.add(_upper)
                # _const_set.add(_eq)

            _const_str_list = list()
            for _const in _const_set:
                _const_str_list.append(_const)

            return "&".join(_const_str_list)

        # set variable declaration string
        var_set = vars_in_ha(ha)

        var_str_list = list()
        map_str_list = list()
        for _var in var_set:
            var_str_list.append(
                "\t\t<param name=\"{}\" type=\"{}\" local=\"false\" "
                "d1=\"1\" d2=\"1\" dynamics=\"any\" />\n".format(_var.id, _var.type)
            )

            map_str_list.append(
                "<map key=\"{}\">{}</map>\n".format(_var.id, _var.id)
            )

        mode_str_list = list()
        mode_id_dict = dict()
        mode_num = 0
        for mode in ha.modes:
            mode_id_dict[id(mode)] = str(mode_num)
            loc_str_begin = "<location id=\"{}\" name=\"mode_id_{}\" x=\"100\" y=\"100\" " \
                            "width=\"50\" height=\"50\">\n".format(mode_num, mode_num)

            # flows
            flow_str_list = list()
            for (var, exp) in mode.dynamics:
                flow_str_list.append("{}\' == {}".format(var, spaceExinfix(exp)))
            flow_str = "<flow>{}</flow>\n".format("&amp;".join(flow_str_list))

            # invs
            inv_str_list = list()
            for inv in mode.invariant:
                inv_str_list.append(spaceExinfix(inv))
            inv_str = "<invariant>{}</invariant> \n".format("&amp;".join(inv_str_list))

            loc_str_end = "</location>\n"

            mode_str_list.append(loc_str_begin + inv_str + flow_str + loc_str_end)
            mode_num += 1

        #trans_label_str_list = list()
        trans_str_list = list()

        for transition in ha.transitions:
            #trans_label_str_list.append(
            #    "\t\t<param name=\"{}\" type=\"label\" local=\"false\" />".format(transition.name)
            #)

            t_str_begin = "<transition source=\"{}\" target=\"{}\">\n".format(mode_id_dict[id(transition.src)],
                                                                              mode_id_dict[id(transition.trg)])
            #t_label = "<label>{}</label>\n".format(transition.name)
            t_label_position = "<labelposition x=\"200\" y=\"200\" width=\"20\" height=\"10\"/>\n"

            # guard
            guard_str_list = list()
            for guard in transition.guard:
                guard_str_list.append(spaceExinfix(guard))
            guard_str = "<guard>{}</guard>\n".format("&amp;".join(guard_str_list))

            # reset
            reset_str_list = list()
            for reset in transition.reset:
                reset_str_list.append(spaceExinfixReset(reset))
            reset_str = "<assignment>{}</assignment>\n".format("&amp;".join(reset_str_list))

            t_str_end = "</transition>\n"
            trans_str_list.append(t_str_begin + guard_str + reset_str + t_label_position + t_str_end)

        hybrid_automaton_component = '''<component id=\"{}\">
        {}{}{}
        </component>
        '''.format(ha.name, "\n".join(var_str_list), "\n".join(mode_str_list), "\n".join(trans_str_list))


        system_component = '''<component id=\"system\">
        {}
        <bind component=\"{}\" as=\"{}_system\" x=\"300\" y=\"200\">
        {}
        </bind>
        </component>
        '''.format("\n".join(var_str_list), ha.name, ha.name, "\n".join(map_str_list))

        model_string = '''<?xml version="1.0" encoding="UTF-8"?>
<sspaceex xmlns="http://www-verimag.imag.fr/xml-namespaces/sspaceex" version="0.2" math="SpaceEx"> 
{}
{}
</sspaceex>
        '''.format(hybrid_automaton_component, system_component)

        initial_modes, terminal_modes = calc_initial_terminal_modes(ha)

        initial_state_str = list()
        for m in initial_modes:
            initial_state_str.append("loc({}_system) == mode_id_{}".format(ha.name, mode_id_dict[id(m)]))

        forbidden_state_str = list()
        for m in terminal_modes:
            forbidden_state_str.append("loc({}_system) == mode_id_{}".format(ha.name, mode_id_dict[id(m)]))


        assert len(variable_ordering) > 1
        init_str = _make_init_string(variable_ordering, bound_box)

        config = setting["configuration"]
        common_section = config.get_section("common")
        spaceex_section = config.get_section("spaceex")

        variables = spaceex_section.get_value("output-variables")
        if variables == "":
            variables = "\"{}, {}\"".format(variable_ordering[0], variable_ordering[1])




        net_dict = dict()
        net_dict["system"] = "\"system\""
        net_dict["initially"] = "\"{} & ({})\"".format(init_str, " || ".join(initial_state_str))
        net_dict["forbidden"] = "\"{}\"".format(" || ".join(forbidden_state_str))
        net_dict["scenario"] = "\"{}\"".format(spaceex_section.get_value("scenario"))
        net_dict["directions"] = "\"{}\"".format(spaceex_section.get_value("directions"))
        net_dict["iter-max"] = "\"{}\"".format(spaceex_section.get_value("iter-max"))
        net_dict["output-variables"] = variables
        net_dict["output-format"] = "\"{}\"".format(spaceex_section.get_value("output-format"))
        net_dict["rel-err"] = "{}".format(spaceex_section.get_value("rel-err"))
        net_dict["abs-err"] = "{}".format(spaceex_section.get_value("abs-err"))
        net_dict["time-horizon"] = "{}".format(spaceex_section.get_value("time-horizon"))

        gen_result = common_section.get_value("visualize")
        output = spaceex_section.get_value("output")
        if gen_result == "on":
            if output != "":
                output_format = spaceex_section.get_value("output-format")
                net_dict["output-file"] = "{}.{}".format(output, output_format.lower())

        conf_str_list = list()
        for k in net_dict:
            conf_str_list.append("{} = {}".format(k, net_dict[k]))

        conf_string = "\n".join(conf_str_list)

        #
        self.convert_result = [model_string, conf_string]


class SpaceExSolverNaive(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, NaiveStrategyManager())

    def make_assignment(self):
        pass

    def clear(self):
        pass


class SpaceExSolverReduction(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, ReductionStrategyManager())

    def make_assignment(self):
        pass

    def clear(self):
        pass


class SpaceExSolverUnsatCore(CommonOdeSolver):
    def __init__(self):
        CommonOdeSolver.__init__(self, UnsatCoreStrategyManager(), NormalSolvingStrategy(SpaceExConverter()))

    def make_assignment(self):
        pass

    def clear(self):
        pass


class SpaceExAssignment(Assignment):
    def __init__(self, spaceex_counterexample):
        self.spaceex_counterexample = spaceex_counterexample

    def get_assignments(self):
        print(self.spaceex_counterexample)

    def eval(self, const):
        pass


@singledispatch
def spaceExinfix(const: Constraint):
    return str(const)


@spaceExinfix.register(Variable)
def _(const: Variable):
    return const.id


@spaceExinfix.register(And)
def _(const: And):
    return '&amp;'.join([spaceExinfix(c) for c in const.children])


@spaceExinfix.register(Geq)
def _(const: Geq):
    return spaceExinfix(const.left) + " &gt;= " + spaceExinfix(const.right)

@spaceExinfix.register(TimeBoundConst)
def _(const: TimeBoundConst):
    return spaceExinfix(const.left) + " &gt;= " + spaceExinfix(const.right)


@spaceExinfix.register(Gt)
def _(const: Geq):
    return spaceExinfix(const.left) + " &gt; " + spaceExinfix(const.right)


@spaceExinfix.register(Leq)
def _(const: Geq):
    return spaceExinfix(const.left) + " &lt;= " + spaceExinfix(const.right)


@spaceExinfix.register(Lt)
def _(const: Geq):
    return spaceExinfix(const.left) + " &lt; " + spaceExinfix(const.right)


@spaceExinfix.register(Eq)
def _(const: Eq):
    return spaceExinfix(const.left) + " == " + spaceExinfix(const.right)


# cannot support this
@spaceExinfix.register(Neq)
def _(const: Neq):
    return spaceExinfix(const.left) + " &gt;= " + spaceExinfix(const.right) + " &amp; " + spaceExinfix(
        const.left) + " &lt; " + spaceExinfix(
        const.right)


@spaceExinfix.register(Add)
def _(const: Add):
    return "(" + spaceExinfix(const.left) + " + " + spaceExinfix(const.right) + ")"


@spaceExinfix.register(Sub)
def _(const: Sub):
    return "(" + spaceExinfix(const.left) + " - " + spaceExinfix(const.right) + ")"


@spaceExinfix.register(Neg)
def _(const: Neg):
    return "(-" + spaceExinfix(const.child) + ")"


@spaceExinfix.register(Mul)
def _(const: Mul):
    return "(" + spaceExinfix(const.left) + " * " + spaceExinfix(const.right) + ")"


@spaceExinfix.register(Div)
def _(const: Div):
    return "(" + spaceExinfix(const.left) + " / " + spaceExinfix(const.right) + ")"


# maybe not supported
@spaceExinfix.register(Pow)
def _(const: Pow):
    return "(" + spaceExinfix(const.left) + " ** " + spaceExinfix(const.right) + ")"


@spaceExinfix.register(Forall)
def _(const: Forall):
    return spaceExinfix(const.const)


### start


@singledispatch
def spaceExinfixReset(const: Constraint):
    return str(const)


@spaceExinfixReset.register(Variable)
def _(const: Variable):
    return const.id


@spaceExinfixReset.register(And)
def _(const: And):
    return '&amp;'.join([spaceExinfixReset(c) for c in const.children])


@spaceExinfixReset.register(Geq)
def _(const: Geq):
    return spaceExinfixReset(const.left) + " &gt;= " + spaceExinfixReset(const.right)

@spaceExinfixReset.register(TimeBoundConst)
def _(const: TimeBoundConst):
    return spaceExinfixReset(const.left) + " &gt;= " + spaceExinfixReset(const.right)


@spaceExinfixReset.register(Gt)
def _(const: Geq):
    return spaceExinfixReset(const.left) + " &gt; " + spaceExinfixReset(const.right)


@spaceExinfixReset.register(Leq)
def _(const: Geq):
    return spaceExinfixReset(const.left) + " &lt;= " + spaceExinfixReset(const.right)


@spaceExinfixReset.register(Lt)
def _(const: Geq):
    return spaceExinfixReset(const.left) + " &lt; " + spaceExinfixReset(const.right)


@spaceExinfixReset.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Real):
        return "{}\' == {}".format(const.left.id, spaceExinfixReset(const.right))
    elif isinstance(const.left, Int):
        return "{}\' == {}".format(const.left.id, spaceExinfixReset(const.right))
    else:
        raise NotSupportedError()


# cannot support this
@spaceExinfixReset.register(Neq)
def _(const: Geq):
    return spaceExinfixReset(const.left) + " &gt;= " + spaceExinfixReset(const.right) + " &amp; " + spaceExinfixReset(
        const.left) + " &lt; " + spaceExinfixReset(
        const.right)


@spaceExinfixReset.register(Add)
def _(const: Add):
    return "(" + spaceExinfixReset(const.left) + " + " + spaceExinfixReset(const.right) + ")"


@spaceExinfixReset.register(Sub)
def _(const: Sub):
    return "(" + spaceExinfixReset(const.left) + " - " + spaceExinfixReset(const.right) + ")"


@spaceExinfixReset.register(Neg)
def _(const: Neg):
    return "(-" + spaceExinfixReset(const.child) + ")"


@spaceExinfixReset.register(Mul)
def _(const: Mul):
    return "(" + spaceExinfixReset(const.left) + " * " + spaceExinfixReset(const.right) + ")"


@spaceExinfixReset.register(Div)
def _(const: Div):
    return "(" + spaceExinfixReset(const.left) + " / " + spaceExinfixReset(const.right) + ")"


# maybe not supported
@spaceExinfixReset.register(Pow)
def _(const: Pow):
    return "(" + spaceExinfixReset(const.left) + " ** " + spaceExinfixReset(const.right) + ")"


@spaceExinfixReset.register(Forall)
def _(const: Forall):
    return spaceExinfixReset(const.const)
