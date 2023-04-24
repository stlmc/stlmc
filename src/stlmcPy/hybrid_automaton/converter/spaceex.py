from functools import singledispatch
from typing import Union

from .converter import Converter
from ..hybrid_automaton import *
from ..utils import *
from ...constraints.constraints import *
from ...objects.configuration import Configuration


class SpaceExConverter(Converter):
    def __init__(self, config: Configuration):
        self._model_string = ""
        self._config_string = ""
        self.config: Configuration = config

    def convert(self, ha: HybridAutomaton):
        self._reset()
        # set variable declaration string
        self._model_string = _make_model(ha)
        self._config_string = _make_conf(ha, self.config)

    def write(self, file_name: str):
        common_section = self.config.get_section("common")
        g_n, b = common_section.get_value("goal"), common_section.get_value("bound")

        m_n = "{}_{}_b{}_se.xml".format(file_name, g_n, b)
        c_n = "{}_{}_b{}_se.cfg".format(file_name, g_n, b)

        f = open(m_n, "w")
        f.write(self._model_string)
        f.close()

        f = open(c_n, "w")
        f.write(self._config_string)
        f.close()
        print("write hybrid automaton to {} and {}".format(m_n, c_n))

    def _reset(self):
        self._model_string = ""
        self._config_string = ""


def _make_model(ha: HybridAutomaton):
    v_set = get_ha_vars(ha)
    jp_s = get_jumps(ha)

    var_str_list, map_str_list = _decl_var(v_set)
    mode_str_list = "\n".join([_make_loc(mode) for mode in ha.get_modes()])
    trans_str_list = "\n".join([_make_jp(jp) for jp in jp_s])

    # make component
    ha_id = id(ha)
    ha_comp_header = "<component id=\"{}\">".format(ha_id)
    ha_comp_footer = "</component>"

    ha_comp = "\n".join([ha_comp_header, var_str_list, mode_str_list, trans_str_list, ha_comp_footer])

    # make system
    sys_comp_header = "<component id=\"system\">"
    sys_comp_footer = "</component>"
    bind_header = "<bind component=\"{}\" as=\"subsystem\" x=\"300\" y=\"200\">".format(ha_id, ha_id)
    bind_footer = "</bind>"
    sys_comp = "\n".join([sys_comp_header, var_str_list, bind_header, map_str_list, bind_footer, sys_comp_footer])

    xml_header = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
    xml_version = "version=\"0.2\""
    xml_url = "xmlns=\"http://www-verimag.imag.fr/xml-namespaces/sspaceex\""
    xml_info = "{} {} math=\"SpaceEx\"".format(xml_url, xml_version)

    model_header = "<sspaceex {}>".format(xml_info)
    model_footer = "</sspaceex>"
    return "\n".join([xml_header, model_header, ha_comp, sys_comp, model_footer])


def _make_conf(ha: HybridAutomaton, config: Configuration):
    common_section = config.get_section("common")
    time_horizon = common_section.get_value("time-horizon")

    v_set = get_ha_vars(ha)

    init_state, final_state = list(), list()
    for mode in ha.get_modes():
        if mode.is_initial():
            init_state.append("loc(subsystem) == mode_id_{}".format(mode.id))

        if mode.is_final():
            final_state.append("loc(subsystem) == mode_id_{}".format(mode.id))

    init_const = [obj2se(c, is_initial=True) for c in ha.init]

    assert len(v_set) > 0
    random_var = v_set.copy().pop()

    conf_dict = dict()
    conf_dict["system"] = "\"system\""
    conf_dict["initially"] = "\"{} & ({})\"".format(" & ".join(init_const), " || ".join(init_state))
    conf_dict["forbidden"] = "\"{}\"".format(" || ".join(final_state))
    conf_dict["scenario"] = "\"stc\""
    conf_dict["directions"] = "\"oct\""
    conf_dict["set-aggregation"] = "chull"
    conf_dict["flowpipe-tolerance"] = "1"
    conf_dict["flowpipe-tolerance-rel"] = "0"
    conf_dict["time-horizon"] = "{}".format(time_horizon)
    conf_dict["iter-max"] = "-1"
    conf_dict["output-variables"] = "\"{}, {}\"".format(random_var, random_var)
    conf_dict["output-format"] = "\"INTV\""

    conf_str_list = ["{} = {}".format(cf, conf_dict[cf]) for cf in conf_dict]
    return "\n".join(conf_str_list)


def _decl_var(v_set: Set[Variable]):
    var_str_list = list()
    def name_f(x): return "name=\"{}\"".format(x.id)
    def type_f(x): return "type=\"{}\"".format(x.type)
    other = "local=\"false\" d1=\"1\" d2=\"1\" dynamics=\"any\""

    v_str = ["<param {} {} {} />".format(name_f(v), type_f(v), other) for v in v_set]
    m_str = ["<map key=\"{}\">{}</map>".format(v.id, v.id) for v in v_set]
    return "\n".join(v_str), "\n".join(m_str)


def _make_loc(mode: Mode):
    loc_id, loc_name = "id=\"{}\"".format(mode.id), "name=\"mode_id_{}\"".format(mode.id)
    x, y = "x=\"100\"", "y=\"100\""
    w, h = "width=\"50\"", "height=\"50\""

    header = "<location {} {} {} {} {} {}>".format(loc_id, loc_name, x, y, w, h)
    footer = "</location>"
    f, inv = _make_flow(mode), _make_inv(mode)

    return "\n".join([header, f, inv, footer])


def _make_flow(mode: Mode):
    flows = ["{}\' == {}".format(v, obj2se(mode.dynamics[v])) for v in mode.dynamics]
    return "<flow>{}</flow>".format("&amp;\n".join(flows))


def _make_inv(mode: Mode):
    inv_s = [obj2se(inv) for inv in mode.invariant]
    return "<invariant>{}</invariant>".format("&amp;\n".join(inv_s))


def _make_jp(jp: Transition):
    src = "source=\"{}\"".format(jp.get_src().id)
    trg = "target=\"{}\"".format(jp.get_trg().id)
    g, r = _make_guard(jp), _make_reset(jp)
    other = "<labelposition x=\"200\" y=\"200\" width=\"20\" height=\"10\"/>"

    header = "<transition {} {}>".format(src, trg)
    footer = "</transition>"
    return "\n".join([header, g, r, other, footer])


def _make_guard(jp: Transition):
    guard_s = [obj2se(guard) for guard in jp.guard]
    return "<guard>{}</guard>\n".format("&amp;\n".join(guard_s))


def _make_reset(jp: Transition):
    reset_s = [obj2se(v == e, is_reset=True) for v, e in jp.reset]
    return "<assignment>{}</assignment>".format("&amp;\n".join(reset_s))


@singledispatch
def obj2se(const: Union[Formula, Expr]):
    raise Exception("cannot support translation of {} for spaceex".format(const))


@obj2se.register(Variable)
def _(const: Variable):
    return const.id


@obj2se.register(Constant)
def _(const: Constant):
    return const.value


@obj2se.register(And)
def _(const: And):
    return ' & '.join([obj2se(c) for c in const.children])


@obj2se.register(Geq)
def _(const: Geq):
    return obj2se(const.left) + " >= " + obj2se(const.right)


@obj2se.register(Gt)
def _(const: Gt):
    return obj2se(const.left) + " > " + obj2se(const.right)


@obj2se.register(Leq)
def _(const: Leq):
    return obj2se(const.left) + " <= " + obj2se(const.right)


@obj2se.register(Lt)
def _(const: Lt):
    return obj2se(const.left) + " < " + obj2se(const.right)


@obj2se.register(Eq)
def _(const: Eq):
    return obj2se(const.left) + " == " + obj2se(const.right)


# cannot support this
@obj2se.register(Neq)
def _(const: Neq):
    raise Exception("neq not supported {}".format(const))


@obj2se.register(Add)
def _(const: Add):
    return "(" + obj2se(const.left) + " + " + obj2se(const.right) + ")"


@obj2se.register(Sub)
def _(const: Sub):
    return "(" + obj2se(const.left) + " - " + obj2se(const.right) + ")"


@obj2se.register(Neg)
def _(const: Neg):
    return "(-" + obj2se(const.child) + ")"


@obj2se.register(Mul)
def _(const: Mul):
    return "(" + obj2se(const.left) + " * " + obj2se(const.right) + ")"


@obj2se.register(Div)
def _(const: Div):
    return "(" + obj2se(const.left) + " / " + obj2se(const.right) + ")"


# maybe not supported
@obj2se.register(Pow)
def _(const: Pow):
    return "(" + obj2se(const.left) + " ** " + obj2se(const.right) + ")"


def xml_pretty_print(current, parent=None, index=-1, depth=0):
    for i, node in enumerate(current):
        xml_pretty_print(node, current, i, depth + 1)
    if parent is not None:
        if index == 0:
            parent.text = '\n' + ('\t' * depth)
        else:
            parent[index - 1].tail = '\n' + ('\t' * depth)
        if index == len(parent) - 1:
            current.tail = '\n' + ('\t' * (depth - 1))