from functools import singledispatch
from typing import List

from ..utils import get_ha_vars, get_jumps, remove_equal_jumps
from ...hybrid_automaton.hybrid_automaton import *
from ...objects.configuration import Configuration


class JuliaReachConverter:
    def __init__(self, config: Configuration):
        self._string = ""
        self.config: Configuration = config
        common_section = self.config.get_section("common")
        self.time_bound = float(common_section.get_value("time-bound"))
        self.bound = int(common_section.get_value("bound"))

    def convert(self, ha: HybridAutomaton):
        preprocessing(ha)
        bound_box = ha.get_bound_box()
        sys_var, v_decl = _prepare_var(ha)
        jp_s = get_jumps(ha)

        m_d = list()
        mode_id: Dict[Mode, int] = dict()
        for idx, mode in enumerate(ha.get_modes()):
            m_d.append(_mode_decl(mode, sys_var))
            mode_id[mode] = idx + 1

        ha_decl = _make_automaton(ha, jp_s, mode_id)

        m_s, t_m_s = list(), list()
        for mode in ha.get_modes():
            m_s.append(_make_mode(mode, sys_var))
            t_m_s.append(_mode_var(mode))
        m_decl = "\n".join(m_s)
        m_ha = "modes = [{}]".format(", ".join(t_m_s))

        jp_r, n_jp_s = list(), list()
        for jp in jp_s:
            jp_r.append(_make_jp(jp, sys_var, bound_box))
            n_jp_s.append(_jp_var(jp))
        jp_decl = "\n".join(jp_r)
        jp_ha = "resets = [{}]".format(", ".join(n_jp_s))

        main_ha_begin = "function main_automaton()"
        main_ha_end = "end"
        f_ha = "return HybridSystem(automaton, modes, resets, [AutonomousSwitching()])"

        main_ha = [main_ha_begin, ha_decl, m_decl, m_ha, jp_decl, jp_ha, f_ha, main_ha_end]

        header = "using ReachabilityAnalysis, ModelingToolkit, LazySets, CDDLib"
        model = ["function model(X0)", "H = main_automaton()", "return IVP(H, X0)", "end"]
        init = _make_init(ha, sys_var, mode_id, bound_box)
        prob = "prob = model(init)"
        analysis = _analysis(
            "TMJets(abstol=1e-15, orderT=10, orderQ=2, maxsteps=50_000)",
            "BoxClustering(100)",
            self.bound, self.time_bound
        )

        final = _unsafe_check(ha, mode_id)

        self._string = "\n".join([header, v_decl, "\n".join(m_d), "\n".join(main_ha),
                                  "\n".join(model), init, prob, analysis, final])

    def write(self, file_name: str):
        common_section = self.config.get_section("common")
        g_n, b = common_section.get_value("goal"), common_section.get_value("bound")

        jl_n = "{}_{}_b{}_jl.jl".format(file_name, g_n, b)
        f = open(jl_n, "w")
        f.write(self._string)
        f.close()

        print("write hybrid automaton to {}".format(jl_n))


def preprocessing(ha: HybridAutomaton):
    remove_equal_jumps(ha)


def _prepare_var(ha: HybridAutomaton) -> Tuple[Dict[Variable, int], str]:
    sys_var: Dict[Variable, int] = dict()
    vs = get_ha_vars(ha)
    v_decl = list()

    for idx, v in enumerate(vs):
        sys_var[v] = idx + 1
        v_decl.append(str(v))

    return sys_var, "vars = @variables {}".format(", ".join(v_decl))


def _mode_name(mode: Mode):
    return "mode_{}!".format(mode.id)


def _mode_var(mode: Mode):
    return "mode{}".format(mode.id)


def _jp_var(jp: Transition):
    return "jp{}".format(id(jp))


def _analysis(alg, clustering, bound: int, time_bound: float):
    return "@time sol = solve(prob, tspan=(0.0, {}), alg={}, clustering_method={}, max_jumps={})".format(time_bound, alg, clustering, bound)


def _make_init(ha: HybridAutomaton, sys_var: Dict[Variable, int], mode_id: Dict[Mode, int], bound_box: BoundBox):
    initials = set()
    for mode in ha.get_modes():
        if mode.is_initial():
            initials.add(mode)

    # get bound box
    s_v = list(sorted(sys_var.keys(), key=lambda x: sys_var[x]))
    l_b, u_b = list(), list()

    for v in s_v:
        # upper bound should be greater than 0
        # otherwise juliareach throws warning
        if "tau" in v.id:
            l_b.append("0.0")
            u_b.append("0.01")
        else:
            bb = bound_box[v]
            l_b.append(bb.left.value)
            u_b.append(bb.right.value)

    l_b_s, u_b_s = ", ".join(l_b), ", ".join(u_b)

    init_rectangle = list()
    for init_mode in initials:
        assert init_mode in mode_id
        init_m_id = mode_id[init_mode]
        init_rectangle.append("({}, Hyperrectangle(low=[{}], high=[{}]))".format(init_m_id, l_b_s, u_b_s))

    return "init = [{}]".format(", ".join(init_rectangle))


def _unsafe_check(ha: HybridAutomaton, mode_id: Dict[Mode, int]):
    final_m_s = set()
    for mode in ha.get_modes():
        if mode.is_final():
            final_m_s.add(mode)

    unsafe_checking = list()
    for idx, final_m in enumerate(final_m_s):
        header = "if" if idx == 0 else "elseif"
        f_block = [
            "{} location(fp) == {}".format(header, mode_id[final_m]),
            "unsafe = {}".format(formula2julia(*final_m.invariant)),
            "if !isdisjoint(unsafe, set(fp))",
            "println(\"counterexample found\")",
            "global ce_found = true",
            "end"
        ]
        unsafe_checking.append("\n".join(f_block))
    unsafe_checking.append("\n".join(["else", "continue", "end"]))

    return "\n".join(["ce_found = false",
                      "for fp in flowpipe(sol)",
                      "if ce_found", "break", "end",
                      "\n".join(unsafe_checking), "end",
                      "if !ce_found", "println(\"no counterexample found\")", "end"])


def _mode_decl(mode: Mode, sys_var: Dict[Variable, int]):
    es = list()

    if len(mode.dynamics) > 0:
        for v in mode.dynamics:
            assert v in sys_var
            es.append(dyn2julia(v, mode.dynamics[v], sys_var))
    else:
        for v in sys_var:
            es.append("dx[{}] = zero(x[{}])".format(sys_var[v], sys_var[v]))

    begin = "@taylorize function {}(dx, x, params, t)".format(_mode_name(mode))
    dyns = "\n".join(es)
    end = "end"

    return "\n".join([begin, dyns, end])


def _make_automaton(ha: HybridAutomaton, jp_s, mode_id: Dict[Mode, int]):
    decl = "automaton = GraphAutomaton({})".format(len(ha.get_modes()))

    jp_decl = list()
    for idx, jp in enumerate(jp_s):
        assert isinstance(jp, Transition)
        jp_decl.append("add_transition!(automaton,{},{},{})".format(mode_id[jp.get_src()],
                                                                    mode_id[jp.get_trg()], idx + 1))
    return "\n".join([decl, "\n".join(jp_decl)])


def _make_mode(mode: Mode, sys_var: Dict[Variable, int]):
    inv_decl, inv = _make_inv(mode, len(sys_var))
    m = "{} = @system(x' = {}(x), dim:{}{})".format(_mode_var(mode), _mode_name(mode), len(sys_var), inv)
    return "\n".join([inv_decl, m])


def _make_inv(mode: Mode, num_vars: int):
    inv_name = "inv_{}".format(_mode_var(mode))
    if len(mode.invariant) > 0:
        inv = formula2julia(*mode.invariant)
    else:
        inv = "Universe({})".format(num_vars)
    return "{} = {}".format(inv_name, inv), ", x ∈ {}".format(inv_name)


def _make_jp(jp: Transition, sys_var: Dict[Variable, int], bound_box: BoundBox) -> str:
    no_guard = len(jp.guard) == 0
    no_reset = len(jp.reset) == 0

    # identity map
    if not no_guard and no_reset:
        g = formula2julia(*jp.guard)
        return "{} = ConstrainedIdentityMap({}, {})".format(_jp_var(jp), len(sys_var), g)

    if not no_guard and not no_reset:
        g = formula2julia(*jp.guard)
        a, b = reset(sys_var, *jp.reset)
        return "{} = ConstrainedAffineMap({},{},{})".format(_jp_var(jp), a, b, g)

    if no_guard and not no_reset:
        picked = list(sys_var.keys())[0]
        g = formula2julia(picked >= bound_box[picked].left)
        a, b = reset(sys_var, *jp.reset)
        return "{} = ConstrainedAffineMap({},{},{})".format(_jp_var(jp), a, b, g)

    if no_guard and no_reset:
        picked = list(sys_var.keys())[0]
        g = formula2julia(picked >= bound_box[picked].left)
        a, b = reset(sys_var)
        return "{} = ConstrainedAffineMap({},{},{})".format(_jp_var(jp), a, b, g)

    raise Exception("currently not supported jump types (guard: {}, reset: {})".format(len(jp.guard), len(jp.reset)))


def dyn2julia(v: Variable, e: Union[Expr, Variable], sys_var_dict: Dict[Variable, int]):
    v_idx = sys_var_dict[v]
    if isinstance(e, RealVal):
        if float(e.value) == 0:
            return "dx[{}] = zero(x[{}])".format(v_idx, v_idx)
        elif float(e.value) == 1:
            return "dx[{}] = one(x[{}])".format(v_idx, v_idx)
        else:
            return "dx[{}] = {}*one(x[{}])".format(v_idx, e, v_idx)
    else:
        return "dx[{}] = {}".format(v_idx, exp2julia(e, sys_var_dict))


@singledispatch
def exp2julia(const: Union[Expr, Variable], sys_var_dict: Dict[Variable, int]):
    raise Exception("fail to translate to julia reach object ({})".format(const))


@exp2julia.register(Variable)
def _(const: Variable, sys_var_dict: Dict[Variable, int]):
    assert const in sys_var_dict
    return "x[{}]".format(sys_var_dict[const])


@exp2julia.register(Constant)
def _(const: Constant, sys_var_dict: Dict[Variable, int]):
    return "{}".format(const.value, const.value)


@exp2julia.register(Add)
def _(const: Add, sys_var_dict: Dict[Variable, int]):
    return "(" + exp2julia(const.left, sys_var_dict) + " + " + exp2julia(const.right, sys_var_dict) + ")"


@exp2julia.register(Sub)
def _(const: Sub, sys_var_dict: Dict[Variable, int]):
    return "(" + exp2julia(const.left, sys_var_dict) + " - " + exp2julia(const.right, sys_var_dict) + ")"


@exp2julia.register(Neg)
def _(const: Neg, sys_var_dict: Dict[Variable, int]):
    return "(-" + exp2julia(const.child, sys_var_dict) + ")"


@exp2julia.register(Mul)
def _(const: Mul, sys_var_dict: Dict[Variable, int]):
    return "(" + exp2julia(const.left, sys_var_dict) + " * " + exp2julia(const.right, sys_var_dict) + ")"


@exp2julia.register(Div)
def _(const: Div, sys_var_dict: Dict[Variable, int]):
    return "(" + exp2julia(const.left, sys_var_dict) + " / " + exp2julia(const.right, sys_var_dict) + ")"


@exp2julia.register(Pow)
def _(const: Pow, sys_var_dict: Dict[Variable, int]):
    return "(" + exp2julia(const.left, sys_var_dict) + "^" + exp2julia(const.right, sys_var_dict) + ")"


@exp2julia.register(Sin)
def _(const: Sin, sys_var_dict: Dict[Variable, int]):
    return "sin(" + exp2julia(const.child, sys_var_dict) + ")"


def formula2julia(*const):
    if len(const) <= 0:
        # raise Exception("cannot translate empty const to julia object")
        return "EmptySet()"

    consts = _flatten(*const)

    c_s = set()
    for c in consts:
        if not isinstance(c, Proposition):
            raise Exception("constraint must be a proposition (given: {})".format(c))

        if isinstance(c, Eq):
            assert isinstance(c.left, Expr) and isinstance(c.right, Expr)
            # c_s.add("Hyperplane({}, vars)".format(_f2julia(c)))
            c_s.add("HalfSpace({}, vars)".format(_f2julia(c.left <= c.right)))
            c_s.add("HalfSpace({}, vars)".format(_f2julia(c.left >= c.right)))
        else:
            c_s.add("HalfSpace({}, vars)".format(_f2julia(c)))

    if len(c_s) > 1:
        return "HPolyhedron([{}])".format(", ".join(c_s))
    else:
        # return "HalfSpace({}, vars)".format("".join(c_s))
        return c_s.pop()


def _flatten(*const):
    children = set()
    for c in const:
        if isinstance(c, And):
            children.update(c.children)
        else:
            children.add(c)
    return children


@singledispatch
def _f2julia(const: Union[Formula, Expr]):
    raise Exception("fail to translate to julia object ({})".format(const))


@_f2julia.register(Variable)
def _(const: Variable):
    return const.id


@_f2julia.register(Constant)
def _(const: Constant):
    return const.value


@_f2julia.register(And)
def _(const: And):
    return '\n'.join([_f2julia(c) for c in const.children])


@_f2julia.register(Geq)
def _(const: Geq):
    return "{} >= {}".format(_f2julia(const.left), _f2julia(const.right))


@_f2julia.register(Gt)
def _(const: Gt):
    return "{} > {}".format(_f2julia(const.left), _f2julia(const.right))


@_f2julia.register(Leq)
def _(const: Leq):
    return "{} <= {}".format(_f2julia(const.left), _f2julia(const.right))


@_f2julia.register(Lt)
def _(const: Geq):
    return "{} < {}".format(_f2julia(const.left), _f2julia(const.right))


@_f2julia.register(Add)
def _(const: Add):
    return "(" + _f2julia(const.left) + " + " + _f2julia(const.right) + ")"


@_f2julia.register(Sub)
def _(const: Sub):
    return "(" + _f2julia(const.left) + " - " + _f2julia(const.right) + ")"


@_f2julia.register(Neg)
def _(const: Neg):
    return "(-" + _f2julia(const.child) + ")"


@_f2julia.register(Mul)
def _(const: Mul):
    return "(" + _f2julia(const.left) + " * " + _f2julia(const.right) + ")"


@_f2julia.register(Div)
def _(const: Div):
    return "(" + _f2julia(const.left) + " / " + _f2julia(const.right) + ")"


# maybe not supported
@_f2julia.register(Pow)
def _(const: Pow):
    return "(" + _f2julia(const.left) + "^" + _f2julia(const.right) + ")"


def reset(sys_var: Dict[Variable, int], *rst):
    c_s = [0.0 for _ in range(len(sys_var))]
    v_s = [0.0 for _ in range(len(sys_var))]

    r_map: Dict[Variable, List] = _identity_map(sys_var)
    for v, e in rst:
        nv_s = _reset(v, e, sys_var, v_s, c_s)
        r_map[v] = nv_s

    s_k = list(sorted(sys_var.keys(), key=lambda x: sys_var[x]))

    a = "[{}]".format("; ".join([" ".join([str(e) for e in r_map[k]]) for k in s_k]))
    b = c_s
    return a, b


def _identity_map(sys_var: Dict[Variable, int]):
    identity_map: Dict[Variable, List] = dict()
    for v in sys_var:
        identity = list()
        for p in range(len(sys_var)):
            if sys_var[v] - 1 == p:
                identity.append(1.0)
            else:
                identity.append(0.0)

        identity_map[v] = identity
    return identity_map


def _reset(v, expr: Expr, sys_var: Dict[Variable, int], v_s, c_s):
    v_sn = v_s.copy()
    if isinstance(expr, Real):
        v_sn[sys_var[v] - 1] = 0.0
        v_sn[sys_var[expr] - 1] = 1.0
    elif isinstance(expr, RealVal):
        # b
        c_s[sys_var[v] - 1] = float(expr.value)
    elif isinstance(expr, Add):
        # ax + b
        assert isinstance(expr.left, Mul)
        assert isinstance(expr.right, RealVal)

        v_inside = expr.left.right
        assert isinstance(v_inside, Real)

        if isinstance(expr.left.left, Neg):
            coefficient = -float(exp2julia(expr.left.left.child, dict()))
        elif isinstance(expr.left.left, RealVal):
            coefficient = float(exp2julia(expr.left.left, dict()))
        else:
            raise Exception("current reset is not supported")

        v_sn[sys_var[v_inside] - 1] = coefficient
        c_s[sys_var[v]] = float(expr.right.value)
    else:
        raise Exception("cannot translate {} in julia matrix".format(expr))
    return v_sn
