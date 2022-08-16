from typing import Dict, Tuple

from .aux import *
from ..robust.relaxing import weakening
from ....constraints.constraints import *
from ....objects.model import Model
from ....util.printer import pprint


class STLmcModel(Model):
    def __init__(self, modules, init, next_str, variable_decl: Dict,
                 range_info: Dict, constant_info: Dict, prop_dict: Dict,
                 init_mode, threshold: float):
        super().__init__()
        self.modules = modules
        self.init = init
        self.next_str = next_str

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

        # keyword of abstraction track variable
        self._abs_keyword = dict()
        self._abs_keyword["range"] = "&abs#range"
        self._abs_keyword["mode"] = "&abs#mode"
        self._abs_keyword["inv"] = "&abs#inv"
        self._abs_keyword["flow"] = "&abs#integral"
        self._abs_keyword["jump"] = "&abs#jp"
        self._abs_keyword["steady-jump"] = "&abs#sjp"

    def encode(self):
        while True:
            yield self._encode()

    def _encode(self):
        b = self._cur_bound
        if b in self._cache:
            return self._generate_const(is_final=False), self._generate_const(is_final=True)

        const_dict = dict()

        # make range consts using the range_info
        r_const = self._make_range_const()
        const_dict["range"] = r_const
        const_dict["const"] = list()

        for module_index, _ in enumerate(self.modules):
            m_c = self._make_mode_const(module_index, is_abs=False)
            i_c = self._make_invariant_const(module_index)
            f_c = self._make_flow_const(module_index)
            j_c = self._make_jump_const(module_index, is_abs=False)
            v_c = self._make_visualize_const(module_index)

            m_const_dict = dict()
            m_const_dict["mode"] = m_c
            m_const_dict["inv"] = i_c
            m_const_dict["flow"] = f_c
            m_const_dict["jump"] = j_c
            m_const_dict["visualize"] = v_c

            const_dict["const"].append(m_const_dict)

        self._cache[b] = const_dict

        # print
        # self._print_const(is_final=False)
        # self._print_const(is_final=True)
        # self._print_track_dict()

        # generate const
        t_c, t_c_f = self._generate_const(is_final=False), self._generate_const(is_final=True)

        # increase bound
        self._cur_bound += 1

        return t_c, t_c_f

    def _generate_const(self, is_final):
        b = self._cur_bound
        assert b in self._cache

        const_dict = self._cache[b]
        r_c = const_dict["range"]
        m_cs = const_dict["const"]

        m_c_list = list()

        for module_c in m_cs:
            m_c = module_c["mode"]
            i_c = module_c["inv"]
            f_c = module_c["flow"]
            j_c = module_c["jump"]
            v_c = module_c["visualize"]

            if not is_final:
                t_c = And([v_c, m_c, i_c, f_c, j_c])
            else:
                t_c = And([v_c, m_c, i_c, f_c])

            m_c_list.append(t_c)

        # track_c = self._generate_track_const(is_final)

        total_c = [self._make_init_const()] if b == 0 else []
        total_c.extend([r_c, Or(m_c_list)])

        return And(total_c)

    def _generate_track_const(self, is_final):
        b = self._cur_bound

        m_track_v = self._abs_keyword["mode"]
        # i_track_v = self._abs_keyword["inv"]
        # f_track_v = self._abs_keyword["flow"]
        j_track_v = self._abs_keyword["jump"]
        sj_track_v = self._abs_keyword["steady-jump"]

        total_c = list()

        # generate track constraints
        for track_v in self._track_dict:
            is_mode_abs = is_track_var(track_v, m_track_v, b)

            # no need to generate track consts for invariant and flow
            # is_inv_abs = is_track_var(track_v, i_track_v, b)
            # is_flow_abs = is_track_var(track_v, f_track_v, b)

            is_jp_abs = is_track_var(track_v, j_track_v, b)
            is_steady_jp_abs = is_track_var(track_v, sj_track_v, b)

            if is_mode_abs:
                total_c.append(track_v == self._track_dict[track_v])

            if not is_final:
                if is_jp_abs or is_steady_jp_abs:
                    total_c.append(track_v == self._track_dict[track_v])

        return And(total_c)

    def _print_const(self, is_final):
        b = self._cur_bound
        assert b in self._cache

        const_dict = self._cache[b]
        r_c = const_dict["range"]
        m_cs = const_dict["const"]

        print("  range const:")
        pprint(r_c, 4)
        for module_index, module_c in enumerate(m_cs):
            print("  module#{}".format(module_index))
            m_c = module_c["mode"]
            i_c = module_c["inv"]
            f_c = module_c["flow"]
            j_c = module_c["jump"]

            print("    mode:")
            pprint(m_c, 6)
            print("    flow:")
            pprint(f_c, 6)
            print("    inv:")
            pprint(i_c, 6)

            if not is_final:
                print("    jump:")
                pprint(j_c, 6)

    def _print_track_dict(self):
        print("[ abstraction ]")
        for track_v in self._track_dict:
            print("  {}:".format(track_v))
            pprint(self._track_dict[track_v], 4)
        print("[ =========== ]")

    def _make_init_const(self):
        # build substitution
        subst = Substitution()
        for m_v in self.variable_decl["mode"]:
            subst.add(m_v, indexed_mode_var(m_v, 0))

        for c_v in self.variable_decl["constant"]:
            subst.add(c_v, self.const_info[c_v])

        for c_v in self.variable_decl["continuous"]:
            subst.add(c_v, indexed_var_0(c_v, 0))

        initial = And(self.init)
        return subst.substitute(initial)

    def _make_range_const(self, is_abs=False):
        # current bound
        b = self._cur_bound

        # generate range consts
        r_consts = list()
        for cont_var in self.range_info.keys():
            r_consts.extend(range_consts(cont_var, b, self.range_info))

        if len(r_consts) > 0:
            t_c = And(r_consts)

            # abstraction
            if is_abs:
                # get abstraction keyword
                range_abs_name = self._abs_keyword["range"]

                # range@{ bound }
                track_v = Bool("{}@{}".format(range_abs_name, b))
                self._track_dict[track_v] = t_c
                return track_v
            else:
                return t_c
        else:
            # do not add Boolean variable
            return BoolVal("True")

    def _make_mode_const(self, module_index: int, is_abs=False):
        b = self._cur_bound

        # get abstraction keyword
        m_abs_keyword = self._abs_keyword["mode"]

        # build substitution
        subst = Substitution()
        for m_v in self.variable_decl["mode"]:
            subst.add(m_v, indexed_mode_var(m_v, b))

        for c_v in self.variable_decl["constant"]:
            subst.add(c_v, self.const_info[c_v])

        # get mode constraints
        m_c_children = self.modules[module_index]["mode"]
        if len(m_c_children) > 0:
            m_c = subst.substitute(And(m_c_children))

            # abstraction
            if is_abs:
                # mode${ module index }@{ bound }
                track_v = Bool("{}${}@{}".format(m_abs_keyword, module_index, b))
                self._track_dict[track_v] = m_c
                return track_v
            else:
                return m_c
        else:
            # do not add Boolean variable
            return BoolVal("True")

    def _make_flow_const(self, module_index: int):
        b = self._cur_bound

        # build substitution
        subst = Substitution()
        subst_0 = Substitution()
        subst_t = Substitution()
        for m_v in self.variable_decl["mode"]:
            subst.add(m_v, indexed_mode_var(m_v, b))

        for c_v in self.variable_decl["constant"]:
            subst.add(c_v, self.const_info[c_v])

        for c_v in self.variable_decl["continuous"]:
            v_0, v_t = indexed_var_0(c_v, b), indexed_var_t(c_v, b)
            subst_0.add(c_v, v_0)
            subst_t.add(c_v, v_t)

        dyns: Dynamics = self.modules[module_index]["flow"]

        # start vector, end_vector (variable vectors)
        dyn_v_vec_0 = [subst_0.substitute(v) for v in dyns.vars]
        dyn_v_vec_t = [subst_t.substitute(v) for v in dyns.vars]

        integral = subst.substitute(Integral(module_index, dyn_v_vec_t, dyn_v_vec_0, dyns))

        abs_keyword = self._abs_keyword["flow"]
        # integral${ module index }@{ bound }
        track_v = Bool("{}${}@{}".format(abs_keyword, module_index, b))
        self._track_dict[track_v] = integral

        return track_v

    def _make_invariant_const(self, module_index: int):
        b = self._cur_bound

        # build substitution
        subst = Substitution()
        for m_v in self.variable_decl["mode"]:
            subst.add(m_v, indexed_mode_var(m_v, b))

        for c_v in self.variable_decl["constant"]:
            subst.add(c_v, self.const_info[c_v])

        # get invariant
        inv_c_list = self.modules[module_index]["inv"]

        if len(inv_c_list) > 0:
            # from tau_{ bound } to tau_{ bound + 1 }, invariant holds
            inv_c = Forall(module_index, tau(b + 1), tau(b), weakening(And(inv_c_list), self._threshold))

            abs_keyword = self._abs_keyword["inv"]
            # inv${ module index }@{ bound }
            track_v = Bool("{}${}@{}".format(abs_keyword, module_index, b))
            self._track_dict[track_v] = inv_c
            return track_v
        else:
            return BoolVal("True")

    def _make_jump_const(self, module_index: int, is_abs=False):
        b = self._cur_bound

        # --- get abstraction keyword ---
        jp_abs_keyword = self._abs_keyword["jump"]
        sjp_abs_keyword = self._abs_keyword["steady-jump"]

        # --- common substitution ---
        # build substitution
        subst = Substitution()
        for m_v in self.variable_decl["mode"]:
            subst.add(m_v, indexed_mode_var(m_v, b))

        for c_v in self.variable_decl["constant"]:
            subst.add(c_v, self.const_info[c_v])

        # add next variable substitution
        for m_v in self.variable_decl["mode"]:
            match_v, next_v = variable("{}{}".format(m_v.id, self.next_str), m_v.type), next_mode_var(m_v, b)
            subst.add(match_v, next_v)

        for c_v in self.variable_decl["continuous"]:
            match_v, next_v = variable("{}{}".format(c_v.id, self.next_str), c_v.type), next_continuous_var(c_v, b)
            subst.add(match_v, next_v)

        # ---
        subst_0 = Substitution()
        subst_t = Substitution()
        for c_v in self.variable_decl["continuous"]:
            subst_0.add(c_v, indexed_var_0(c_v, b))
            subst_t.add(c_v, indexed_var_t(c_v, b))

        # get jump constraint
        jumps = self.modules[module_index]["jump"]

        # --- encode jump conditions ---

        jump_consts = list()

        # flat jump condition
        for jp_index, (pre_jp, post_jp) in enumerate(jumps):
            jp = And([subst_0.substitute(pre_jp), subst_t.substitute(post_jp)])

            # abstraction
            if is_abs:
                # jp_{ jump index }${ module index }@{ bound }
                jp_track_v = Bool("{}_{}${}@{}".format(jp_abs_keyword, jp_index, module_index, b))
                self._track_dict[jp_track_v] = jp

                # add to consts
                jump_consts.append(jp_track_v)
            else:
                jump_consts.append(jp)

        # steady jump
        steady_jp_consts = list()
        for m_v in self.variable_decl["mode"]:
            steady_jp_consts.append(next_mode_var(m_v, b) == indexed_mode_var(m_v, b))

        for c_v in self.variable_decl["continuous"]:
            steady_jp_consts.append(next_continuous_var(c_v, b) == indexed_var_t(c_v, b))

        steady_jp_c = And(steady_jp_consts) if len(steady_jp_consts) > 0 else BoolVal("True")

        if is_abs:
            # sjp${ module index }@{ bound }
            jp_track_v = Bool("{}${}@{}".format(sjp_abs_keyword, module_index, b))
            self._track_dict[jp_track_v] = steady_jp_c

            # add to consts
            jump_consts.append(jp_track_v)
        else:
            jump_consts.append(steady_jp_c)

        if len(jump_consts) > 0:
            return subst.substitute(Or(jump_consts))
        else:
            # if no jumps
            return BoolVal("True")

    def _make_visualize_const(self, module_index: int):
        # vis${ module index }@{ bound }
        return Bool("&vis${}@{}".format(module_index, self._cur_bound))

    def get_abstraction(self):
        return self._track_dict.copy()
