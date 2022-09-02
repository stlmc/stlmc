import abc

from .flowstar import *
from .spaceex import *
from .hybrid_automaton import *
from .utils import get_ha_vars, get_jumps


class Converter:
    @abc.abstractmethod
    def convert(self, ha: HybridAutomaton, time_bound: float):
        pass

    @abc.abstractmethod
    def get_model_string(self) -> str:
        pass

    @abc.abstractmethod
    def get_config_string(self) -> str:
        pass

    @abc.abstractmethod
    def write(self, file_name: str):
        pass


class SpaceExConverter(Converter):
    def __init__(self):
        self.model_string = ""
        self.config_string = ""

    def convert(self, ha: HybridAutomaton, time_bound: float):
        # set variable declaration string
        var_set = get_ha_vars(ha)

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
        for uid, mode in enumerate(ha.modes):
            mode_id_dict[mode] = uid
            loc_str_begin = "<location id=\"{}\" name=\"mode_id_{}\" x=\"100\" y=\"100\" " \
                            "width=\"50\" height=\"50\">\n".format(uid, uid)

            # flows
            flow_str_list = list()
            for (var, exp) in mode.dynamics:
                flow_str_list.append("{}\' == {}".format(var, obj2se(exp, is_reset=False)))
            flow_str = "<flow>{}</flow>\n".format("&amp;".join(flow_str_list))

            # invs
            inv_str_list = list()
            for inv in mode.invariant:
                inv_str_list.append(obj2se(inv, is_reset=False))
            inv_str = "<invariant>{}</invariant> \n".format("&amp;".join(inv_str_list))

            loc_str_end = "</location>\n"

            mode_str_list.append(loc_str_begin + inv_str + flow_str + loc_str_end)

        # trans_label_str_list = list()
        trans_str_list = list()

        for transition in ha.transitions:
            # trans_label_str_list.append(
            #    "\t\t<param name=\"{}\" type=\"label\" local=\"false\" />".format(transition.name)
            # )

            t_str_begin = "<transition source=\"{}\" target=\"{}\">\n".format(mode_id_dict[transition.src],
                                                                              mode_id_dict[transition.trg])
            # t_label = "<label>{}</label>\n".format(transition.name)
            t_label_position = "<labelposition x=\"200\" y=\"200\" width=\"20\" height=\"10\"/>\n"

            # guard
            guard_str_list = list()
            for guard in transition.guard:
                guard_str_list.append(obj2se(guard, is_reset=False))
            guard_str = "<guard>{}</guard>\n".format("&amp;".join(guard_str_list))

            # reset
            reset_str_list = list()
            for reset in transition.reset:
                reset_str_list.append(obj2se(reset, is_reset=True))
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

        initial_state_str = list()
        for m in ha.initial_modes:
            initial_state_str.append("loc({}_system) == mode_id_{}".format(ha.name, mode_id_dict[m]))

        forbidden_state_str = list()
        for m in ha.final_modes:
            forbidden_state_str.append("loc({}_system) == mode_id_{}".format(ha.name, mode_id_dict[m]))

        init_cond_list = list()
        for init_cond in ha.initial_conditions:
            init_cond_list.append(obj2se(init_cond, is_reset=False, is_initial=True))

        assert len(var_set) > 0
        random_var = var_set.copy().pop()

        net_dict = dict()
        net_dict["system"] = "\"system\""
        net_dict["initially"] = "\"{} & ({})\"".format(" & ".join(init_cond_list), " || ".join(initial_state_str))
        net_dict["forbidden"] = "\"{}\"".format(" || ".join(forbidden_state_str))
        net_dict["scenario"] = "\"stc\""
        net_dict["directions"] = "\"oct\""
        net_dict["set-aggregation"] = "chull"
        net_dict["flowpipe-tolerance"] = "1"
        net_dict["flowpipe-tolerance-rel"] = "0"
        net_dict["time-horizon"] = "{}".format(time_bound)
        net_dict["iter-max"] = "-1"
        net_dict["output-variables"] = "\"{}, {}\"".format(random_var, random_var)
        net_dict["output-format"] = "\"INTV\""

        conf_str_list = list()
        for k in net_dict:
            conf_str_list.append("{} = {}".format(k, net_dict[k]))

        conf_string = "\n".join(conf_str_list)

        #
        self.model_string, self.config_string = model_string, conf_string

    def get_model_string(self) -> str:
        return self.model_string

    def get_config_string(self) -> str:
        return self.config_string

    def write(self, file_name: str):
        f = open("{}_se.xml".format(file_name), "w")
        f.write(self.model_string)
        f.close()

        f = open("{}_se.cfg".format(file_name), "w")
        f.write(self.config_string)
        f.close()


class FlowStarConverter(Converter):
    def __init__(self):
        self.model_string = ""
        self.config_string = ""

    def preprocessing(self, ha: HybridAutomaton):
        # add unique, dummy init mode
        # initials = ha.initial_modes.copy()
        #
        # start_mode = ha.add_mode("start")
        # for init_mode in initials:
        #     ha.add_transition("start_{}__id_{}".format(init_mode.name, id(init_mode)), start_mode, init_mode)

        # ha.initial_modes.clear()
        # ha.mark_initial(start_mode)
        ff = Real("ff")
        zero = RealVal("0")

        # ff > 0
        ff_inv = ff > zero

        for mode in ha.modes:
            mode.add_dynamic((ff, zero))
            mode.add_invariant(ff_inv)

        initials = set()
        for mode in ha.modes:
            if mode.is_initial():
                initials.add(mode)
                mode.set_as_non_initial()

        initial_mode = Mode(0)
        initial_mode.set_as_initial()
        ha.add_mode(initial_mode)

        for mode in initials:
            make_jump(initial_mode, mode)

    def convert(self, ha: HybridAutomaton, time_bound: float):
        self.preprocessing(ha)

        modes_str_list = list()
        for mode in ha.modes:
            mode_str = "mode_{}{{\n".format(mode.id)
            mode_str += "poly ode 1\n{"

            for v in mode.dynamics:
                e = mode.dynamics[v]
                mode_str += "{}\' = {}\n".format(v, str(obj2fs(e))).replace("**", "^")
            mode_str += "}\n"

            mode_str += "inv {\n"
            for inv in mode.invariant:
                mode_str += "{}\n".format(obj2fs(inv)) \
                    .replace(">", ">=").replace("<", "<=") \
                    .replace(">==", ">=").replace("<==", "<=").replace("**", "^")
            mode_str += "}\n}"
            modes_str_list.append(mode_str)
        modes_str = "modes {{\n {}\n}}\n".format("\n".join(modes_str_list))

        trans_str_list = list()
        jumps = get_jumps(ha)
        for transition in jumps:
            t_str = "mode_{} -> mode_{}\n".format(transition.src.id, transition.trg.id)
            t_str += "guard {\n"
            for guard in transition.guard:
                _str = "{}\n".format(obj2fs(guard))
                t_str += _str.replace(">", ">=").replace("<", "<=").replace(">==", ">=").replace("<==", "<=").replace(
                    "**", "^")
            t_str += "}\n"

            # reset
            t_str += "reset {\n"
            for le, ri in transition.reset:
                # simplified_reset = expr2sympy(reset, is_reset=True)
                # _str = ""
                # if isinstance(simplified_reset, Equality):
                #     _str = "{}\' := {}\n".format(simplified_reset.lhs, simplified_reset.rhs)
                # else:
                #     _str = "{}\n".format(simplified_reset)
                assert isinstance(le, Variable)
                _str = "{}\' := {}\n".format(le, obj2fs(ri))
                t_str += _str.replace("**", "^").replace("True", "")
            t_str += "}\n"

            t_str += "parallelotope aggregation { }\n"
            trans_str_list.append(t_str)

        trans_str = "jumps {{\n {} \n }}\n".format("\n".join(trans_str_list))

        var_set = get_ha_vars(ha)
        # add initial conditions for special variables: ff = 1, t = 0
        ha.add_init(Real("ff") == RealVal("1.0"))

        bound_box = ha.get_bound_bound()
        initial_modes = set(filter(lambda x: x.is_initial(), ha.modes))
        final_modes = set(filter(lambda x: x.is_final(), ha.modes))

        init_cond_str = ""
        for variable in var_set:
            assert variable in bound_box
            bb = bound_box[variable]
            init_cond_str += "{} in [{}, {}]\n".format(variable, bb.left, bb.right)

        init_child_str = ""
        assert len(initial_modes) == 1
        for start_mode in initial_modes:
            init_child_str += "mode_{} {{".format(start_mode.id)
            init_child_str += init_cond_str
            init_child_str += "}"

        init_str = "init {{\n {}\n}}\n".format(init_child_str)

        unsafe_str = ""
        terminal_modes_str = list()
        for final_mode in final_modes:
            terminal_modes_str.append("mode_{}".format(final_mode.id))

        for m in ha.modes:
            real_name = "mode_{}".format(m.id)
            if real_name in terminal_modes_str:
                unsafe_str += "{}{{}}\n".format(real_name)
            else:
                unsafe_str += "{}{{ ff <= 0 }}\n".format(real_name)

        var_str = "state var "
        for i, v in enumerate(var_set):
            if i == len(var_set) - 1:
                var_str += v.id
            else:
                var_str += v.id + ", "

        assert len(var_set) > 0
        picked = var_set.pop()

        # config
        net_dict = dict()
        net_dict["adaptive steps"] = "{min 0.01, max 0.05}"
        net_dict["time"] = "15"
        net_dict["remainder estimation"] = "1e-2"
        net_dict["identity precondition"] = ""
        net_dict["gnuplot octagon"] = "{},{} fixed orders 2".format(picked, picked)
        net_dict["cutoff"] = "1e-12"
        net_dict["precision"] = "53"
        net_dict["no output"] = ""
        net_dict["max jumps"] = "5"
        net_dict["print on"] = ""

        conf_str_list = list()
        for k in net_dict:
            conf_str_list.append("{} {}".format(k, net_dict[k]))

        setting_str = "setting {{\n {} \n}}\n".format("\n".join(conf_str_list))

        self.model_string = "hybrid reachability {{\n {}\n {}\n {}\n {}\n {}\n}}\n unsafe {{\n {} \n }}\n".format(
            var_str,
            setting_str,
            modes_str,
            trans_str,
            init_str,
            unsafe_str)

    def get_model_string(self) -> str:
        return self.model_string

    def get_config_string(self) -> str:
        return self.config_string

    def write(self, file_name: str):
        f = open("{}_fs.model".format(file_name), "w")
        f.write(self.model_string)
        f.close()


class ConverterFactory:
    SE = 10
    FS = 11

    @staticmethod
    def generate_converter(converter_type: int) -> Converter:
        assert ConverterFactory.SE <= converter_type <= ConverterFactory.FS
        if converter_type == ConverterFactory.SE:
            return SpaceExConverter()
        elif converter_type == ConverterFactory.FS:
            return FlowStarConverter()
        else:
            raise NotImplementedError("unsupported converter type")
