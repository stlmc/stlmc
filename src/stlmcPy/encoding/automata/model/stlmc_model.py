from typing import Iterable

from ....constraints.aux.generator import variable
from ....constraints.aux.operations import Substitution, clause, get_vars
from ....hybrid_automaton.hybrid_automaton import *
from ....objects.model import Model


class STLmcModel(Model):
    def __init__(self, modules, init, next_str, variable_decl: Dict,
                 range_info: Dict, constant_info: Dict, prop_dict: Dict,
                 init_mode, threshold: float):
        super().__init__()
        self.modules = modules
        self.init = init
        self.next_str = next_str
        self.mode_var_name = "modeId"

        # key : string, value : set
        self.variable_decl = variable_decl.copy()
        self.prop_dict = prop_dict.copy()
        self.range_info = range_info.copy()
        self.const_info = constant_info.copy()
        self.init_mode = init_mode

        # encoding related
        self._cur_bound = 0
        self._threshold = threshold
        self._track_dict: Dict[Bool, Formula] = dict()

        # cache - key : bound, value : list of constraint dictionary
        self._cache = dict()

    def encode(self):
        ha = HybridAutomaton()

        # make init
        init_m_c = self._make_init(ha)

        # key: module_index
        mode_id_dict: Dict[int, hash] = dict()
        mode_dict: Dict[hash, Mode] = dict()

        # make modes
        for module_index, _ in enumerate(self.modules):
            mode, mode_id = self._make_mode(module_index, ha, init_m_c)

            mode_dict[mode_id] = mode
            mode_id_dict[module_index] = mode_id

        # make jumps
        for module_index, _ in enumerate(self.modules):
            self._make_jump(module_index, ha, mode_dict, mode_id_dict)

        return ha

    def _make_init(self, ha: HybridAutomaton):
        self._check_valid()

        # build substitution
        subst = Substitution()
        for c_v in self.variable_decl["constant"]:
            subst.add(c_v, self.const_info[c_v])

        # mode_variable
        m_v = Int(self.mode_var_name)

        init_consts = {subst.substitute(c) for c in self.init}
        init_cont_c = set(filter(lambda c: m_v not in get_vars(c), init_consts))
        init_mode_c = set(filter(lambda c: m_v in get_vars(c), init_consts))

        ha.add_init(*init_cont_c)

        assert len(init_mode_c) == 1
        return init_mode_c

    def _make_mode(self, module_index: int, ha: HybridAutomaton, init_mode_c: Set[Formula]):
        m_c_children = self.modules[module_index]["mode"]

        mode_id = calc_hash(m_c_children)
        mode = Mode(mode_id)
        ha.add_mode(mode)

        # matches initial condition
        if init_mode_c.issubset(m_c_children):
            mode.set_as_initial()

        # for default all modes are finals
        mode.set_as_final()

        self._add_dynamics(module_index, mode)
        self._add_invariant(module_index, mode)

        return mode, mode_id

    def _make_jump(self, module_index: int, ha: HybridAutomaton, mode_dict, mode_id_dict):
        jumps_raw = self.modules[module_index]["jump"]
        src_m_id = mode_id_dict[module_index]
        src_mode = mode_dict[src_m_id]

        # build substitution
        subst = Substitution()
        for c_v in self.variable_decl["constant"]:
            subst.add(c_v, self.const_info[c_v])

        jumps = [(subst.substitute(pre), subst.substitute(post)) for pre, post in jumps_raw]

        # build substitution
        subst_n = Substitution()
        # add next variable substitution
        for m_v in self.variable_decl["mode"]:
            match_v = variable("{}{}".format(m_v.id, self.next_str), m_v.type)
            subst_n.add(match_v, m_v)

        for c_v in self.variable_decl["continuous"]:
            match_v = variable("{}{}".format(c_v.id, self.next_str), c_v.type)
            subst_n.add(match_v, c_v)

        # steady jump
        # transition = ha.add_transition("t_{}_{}".format(src_m_id, src_m_id), src_mode, src_mode)
        # for c_v in self.variable_decl["continuous"]:
        #     # assume left is a next variable
        #     transition.set_reset((c_v, c_v))

        # mode_variable
        m_v = Int(self.mode_var_name)

        for pre_jp, post_jp in jumps:
            jp_pre_cl, jp_post_cl = clause(pre_jp), clause(subst_n.substitute(post_jp))

            jp_post_cont = set(filter(lambda c: m_v not in get_vars(c), jp_post_cl))
            jp_post_mode = set(filter(lambda c: m_v in get_vars(c), jp_post_cl))

            trg_m_id = calc_hash(jp_post_mode)

            if trg_m_id not in mode_dict:
                raise Exception("cannot find a target mode")

            trg_mode = mode_dict[trg_m_id]

            transition = make_jump(src_mode, trg_mode)
            transition.add_guard(*jp_pre_cl)

            for r in jp_post_cont:
                assert isinstance(r, Eq)
                # assume left is a next variable
                transition.add_reset((r.left, r.right))

    def _add_dynamics(self, module_index: int, mode: Mode):
        f_c = self.modules[module_index]["flow"]

        # build substitution
        subst = Substitution()
        for c_v in self.variable_decl["constant"]:
            subst.add(c_v, self.const_info[c_v])

        # currently support ode only
        assert isinstance(f_c, Ode)
        for v, e in zip(f_c.vars, f_c.exps):
            mode.add_dynamic((subst.substitute(v), subst.substitute(e)))

    def _add_invariant(self, module_index: int, mode: Mode):
        i_c_children_raw = self.modules[module_index]["inv"]

        # build substitution
        subst = Substitution()
        for c_v in self.variable_decl["constant"]:
            subst.add(c_v, self.const_info[c_v])

        i_c_children = [subst.substitute(i_c) for i_c in i_c_children_raw]

        for inv in i_c_children:
            mode.add_invariant(inv)

    def _check_valid(self):
        m_v = Int(self.mode_var_name)
        if m_v not in self.variable_decl["mode"]:
            raise Exception("cannot find a necessary mode variable")

    def get_abstraction(self):
        pass


def calc_hash(iterable: Iterable) -> hash:
    return hash(frozenset(iterable))
