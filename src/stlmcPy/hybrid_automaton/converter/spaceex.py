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
        f = open("{}_se.xml".format(file_name), "w")
        f.write(self._model_string)
        f.close()

        f = open("{}_se.cfg".format(file_name), "w")
        f.write(self._config_string)
        f.close()

    def _reset(self):
        self._model_string = ""
        self._config_string = ""


def _make_model(ha: HybridAutomaton):
    v_set = get_ha_vars(ha)
    jp_s = get_jumps(ha)

    var_str_list, map_str_list = _decl_var(v_set)
    mode_str_list = [_make_loc(mode) for mode in ha.modes]
    trans_str_list = [_make_jp(jp) for jp in jp_s]

    # make component
    ha_id = id(ha)
    ha_comp_header = "<component id=\"{}\">".format(ha_id)
    ha_comp_footer = "</component>"
    ha_comp = "\n".join([ha_comp_header, var_str_list, mode_str_list, trans_str_list, ha_comp_footer])

    # make system
    sys_comp_header = "<component id=\"system\">"
    sys_comp_footer = "</component>"
    bind_header = "<bind component=\"{}\" as=\"{}_system\" x=\"300\" y=\"200\">".format(ha_id, ha_id)
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
    time_bound = common_section.get_value("time-bound")

    ha_id = id(ha)
    v_set = get_ha_vars(ha)

    init_state, final_state = list(), list()
    for mode in ha.modes:
        if mode.is_initial():
            init_state.append("loc({}_system) == mode_id_{}".format(ha_id, mode.id))

        if mode.is_final():
            final_state.append("loc({}_system) == mode_id_{}".format(ha_id, mode.id))

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
    conf_dict["time-horizon"] = "{}".format(time_bound)
    conf_dict["iter-max"] = "-1"
    conf_dict["output-variables"] = "\"{}, {}\"".format(random_var, random_var)
    conf_dict["output-format"] = "\"INTV\""

    conf_str_list = ["{} = {}".format(cf, conf_dict[cf]) for cf in conf_dict]
    return "\n".join(conf_str_list)


def _decl_var(v_set: Set[Variable]):
    var_str_list = list()
    def name_f(x): "name=\"{}\"".format(x.id)
    def type_f(x): "type=\"{}\"".format(x.type)
    other = "local=\"false\" d1=\"1\" d2=\"1\" dynamics=\"any\""

    v_str = ["<param {} {} {} />".format(name_f(v), type_f(v), other) for v in v_set]
    m_str = ["<map key=\"{}\">{}</map>".format(v.id, v.id) for v in v_set]
    return v_str, m_str


def _make_loc(mode: Mode):
    loc_id, loc_name = "id=\"{}\"".format(mode.id), "name=\"mode_id_{}\"".format(mode.id)
    x, y = "x=\"100\"", "y=\"100\""
    w, h = "width=\"50\"", "height=\"50\""

    header = "<location {} {} {} {} {} {}>".format(loc_id, loc_name, x, y, w, h)
    footer = "</location>"
    f, inv = _make_flow(mode), _make_inv(mode)

    return "\n".join([header, f, inv, footer])


def _make_flow(mode: Mode):
    flows = ["{}\' == {}".format(v, obj2se(e)) for v, e in mode.dynamics]
    return "<flow>{}</flow>".format("&amp;\n".join(flows))


def _make_inv(mode: Mode):
    inv_s = [obj2se(inv) for inv in mode.invariant]
    return "<invariant>{}</invariant>".format("&amp;\n".join(inv_s))


def _make_jp(jp: Transition):
    src = "source=\"{}\"".format(jp.src.id)
    trg = "target=\"{}\"".format(jp.trg.id)
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
def obj2se(const: Union[Formula, Expr], is_reset=False, is_initial=False):
    # return str(const)
    raise Exception("cannot support translation of {} for spaceex".format(const))


@obj2se.register(Variable)
def _(const: Variable, is_reset=False, is_initial=False):
    return const.id


@obj2se.register(Constant)
def _(const: Constant, is_reset=False, is_initial=False):
    return const.value


@obj2se.register(And)
def _(const: And, is_reset=False, is_initial=False):
    if is_initial:
        return ' & '.join([obj2se(c, is_reset, True) for c in const.children])
    return '&amp;'.join([obj2se(c, is_reset) for c in const.children])


@obj2se.register(Geq)
def _(const: Geq, is_reset=False, is_initial=False):
    if is_initial:
        return obj2se(const.left, is_reset, True) + " >= " + obj2se(const.right, is_reset, True)
    return obj2se(const.left, is_reset) + " &gt;= " + obj2se(const.right, is_reset)


@obj2se.register(Gt)
def _(const: Gt, is_reset=False, is_initial=False):
    if is_initial:
        return obj2se(const.left, is_reset, True) + " > " + obj2se(const.right, is_reset, True)
    return obj2se(const.left, is_reset) + " &gt; " + obj2se(const.right, is_reset)


@obj2se.register(Leq)
def _(const: Leq, is_reset=False, is_initial=False):
    if is_initial:
        return obj2se(const.left, is_reset, True) + " <= " + obj2se(const.right, is_reset, True)
    return obj2se(const.left, is_reset) + " &lt;= " + obj2se(const.right, is_reset)


@obj2se.register(Lt)
def _(const: Lt, is_reset=False, is_initial=False):
    if is_initial:
        return obj2se(const.left, is_reset, True) + " < " + obj2se(const.right, is_reset, True)
    return obj2se(const.left, is_reset) + " &lt; " + obj2se(const.right, is_reset)


@obj2se.register(Eq)
def _(const: Eq, is_reset=False, is_initial=False):
    if is_reset and not is_initial:
        if isinstance(const.left, Real):
            return "{}\' == {}".format(const.left.id, obj2se(const.right, True))
        elif isinstance(const.left, Int):
            return "{}\' == {}".format(const.left.id, obj2se(const.right, True))
        else:
            raise Exception("not supported {}".format(const.left.id))
    return obj2se(const.left, False, is_initial) + " == " + obj2se(const.right, False, is_initial)


# cannot support this
@obj2se.register(Neq)
def _(const: Neq, is_reset=False, is_initial=False):
    if is_initial:
        return obj2se(const.left, is_reset, True) + " >= " + obj2se(const.right, is_reset, True) + " & " \
               + obj2se(const.left, is_reset, True) + " < " + obj2se(const.right, is_reset, True)
    return obj2se(const.left, is_reset) + " &gt;= " + obj2se(const.right, is_reset) + " &amp; " \
           + obj2se(const.left, is_reset) + " &lt; " + obj2se(const.right, is_reset)


@obj2se.register(Add)
def _(const: Add, is_reset=False, is_initial=False):
    return "(" + obj2se(const.left, is_reset, is_initial) + " + " + obj2se(const.right, is_reset, is_initial) + ")"


@obj2se.register(Sub)
def _(const: Sub, is_reset=False, is_initial=False):
    return "(" + obj2se(const.left, is_reset, is_initial) + " - " + obj2se(const.right, is_reset, is_initial) + ")"


@obj2se.register(Neg)
def _(const: Neg, is_reset=False, is_initial=False):
    return "(-" + obj2se(const.child, is_reset, is_initial) + ")"


@obj2se.register(Mul)
def _(const: Mul, is_reset=False, is_initial=False):
    return "(" + obj2se(const.left, is_reset, is_initial) + " * " + obj2se(const.right, is_reset, is_initial) + ")"


@obj2se.register(Div)
def _(const: Div, is_reset=False, is_initial=False):
    return "(" + obj2se(const.left, is_reset, is_initial) + " / " + obj2se(const.right, is_reset, is_initial) + ")"


# maybe not supported
@obj2se.register(Pow)
def _(const: Pow, is_reset=False, is_initial=False):
    return "(" + obj2se(const.left, is_reset, is_initial) + " ** " + obj2se(const.right, is_reset, is_initial) + ")"

# @obj2se.register(Forall)
# def _(const: Forall):
#     return obj2se(const.const)
