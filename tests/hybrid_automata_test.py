import unittest

from stlmcPy.constraints.constraints import Real, Geq, RealVal, Or, And, Leq, Ode, Lt, Add
from stlmcPy.hybrid_automaton.hybrid_automaton import Mode, HybridAutomaton, AggregatedMode
from stlmcPy.hybrid_automaton.utils import subsumption, merge_mode, indexing, merge, merge_mode_syntatically, new_merge


class HybridAutomataUtilTestCase(unittest.TestCase):

    def test_subsumption_simple(self):
        """Simple subsumption test: x >= 2 (p) subsumes x >= 3 (q)"""
        x = Real("x")
        p = Geq(x, RealVal("2"))
        q = Geq(x, RealVal("3"))
        self.assertEqual(subsumption(p, q), True,
                         'incorrect subsumption')

    def test_subsumption_simple1(self):
        """Simple subsumption test: x >= 2 (p) does not subsume x < 2 (q) and vise versa"""
        x = Real("x")
        p = Geq(x, RealVal("2"))
        q = Lt(x, RealVal("2"))
        self.assertEqual(subsumption(p, q), False,
                         'incorrect subsumption')
        self.assertEqual(subsumption(q, p), False,
                         'incorrect subsumption')

    def test_subsumption_simple2(self):
        """Simple subsumption test: And (x >= 2) (p) does not subsume And (x < 2) (q) and vise versa"""
        x = Real("x")
        p = Geq(x, RealVal("2"))
        q = Lt(x, RealVal("2"))
        self.assertEqual(subsumption(And([p]), And([q])), False,
                         'incorrect subsumption')
        self.assertEqual(subsumption(And([q]), And([p])), False,
                         'incorrect subsumption')

    def test_subsumption_and(self):
        """Simple subsumption test: x >= 2 or y >= 3 (p) subsumes x >= 2 and y >= 3 (q)"""
        x = Real("x")
        y = Real("y")
        c = [Geq(x, RealVal("2")), Geq(y, RealVal("3"))]
        p = Or(c)
        q = And(c)

        self.assertEqual(subsumption(p, q), True,
                         'incorrect subsumption')

    def test_not_subsumption_simple(self):
        """Simple subsumption test: x >= 2 (p) does not subsume y <= 3 (q) and vise versa"""
        x = Real("x")
        y = Real("y")
        p = Geq(x, RealVal("2"))
        q = Leq(y, RealVal("3"))

        self.assertEqual(subsumption(p, q), False,
                         'incorrect subsumption')
        self.assertEqual(subsumption(q, p), False,
                         'incorrect subsumption')

    def test_subsumption_none(self):
        """Simple subsumption test: None (p) subsumes x >= 2 (q)"""
        x = Real("x")
        p = Geq(x, RealVal("2"))

        self.assertEqual(subsumption(None, p), True,
                         'incorrect subsumption')
        self.assertEqual(subsumption(p, None), False,
                         'incorrect subsumption')

    def test_merge_mode(self):
        """Simple mode merging test: mode1 (x' = 1, x >= 2) and mode2 (x' = 1, x >= 3)"""
        dummy_ha = HybridAutomaton("dummy")
        x = Real("x")
        dyn = Ode([x], [RealVal("1")])
        const1 = Geq(x, RealVal("2"))
        const2 = Geq(x, RealVal("3"))

        mode1 = Mode("mode1", None)
        mode1.set_dynamics(dyn)
        mode1.set_invariant(const1)

        mode2 = Mode("mode2", None)
        mode2.set_dynamics(dyn)
        mode2.set_invariant(const2)

        merged_mode, is_merged = merge_mode(mode1, mode2, dummy_ha)
        self.assertEqual(is_merged, True, 'merging fail')
        self.assertEqual(repr(merged_mode),
                         "( aggregated mode dummy_mode1_mode2 = dyn: ode([x] = [1]), inv: (>= x 2) )",
                         'merging fail because of strange mode generation')

    def test_merge_mode_syntatically(self):
        """Simple mode merging test: mode1 (x' = 1, x >= 2) and mode2 (x' = 1, x >= 3)"""
        dummy_ha = HybridAutomaton("dummy")
        x = Real("x")
        dyn = Ode([x], [RealVal("1")])
        const1 = Geq(x, RealVal("2"))
        const2 = Geq(x, RealVal("3"))

        mode1 = Mode("mode1", None)
        mode1.set_dynamics(dyn)
        mode1.set_invariant(const1)

        mode2 = Mode("mode2", None)
        mode2.set_dynamics(dyn)
        mode2.set_invariant(const1)

        mode3 = Mode("mode3", None)
        mode3.set_dynamics(dyn)
        mode3.set_invariant(const2)

        merged_mode, is_merged = merge_mode_syntatically(mode1, mode2, dummy_ha)
        self.assertEqual(is_merged, True, 'merging fail')
        self.assertEqual(repr(merged_mode),
                         "( aggregated mode dummy_mode1_mode2 = dyn: ode([x] = [1]), inv: (>= x 2) )",
                         'merging fail because of strange mode generation')

        merged_mode2, is_merged = merge_mode_syntatically(mode1, mode3, dummy_ha)
        self.assertEqual(is_merged, False, 'merging fail')
        self.assertIsNone(merged_mode2, "should be None")

    def test_merge_mode1(self):
        """Simple mode merging test1:
        mode 1 [
        dyn:
            tx' = -5.0
            bx' = vb
            vb' = 0.3
            tau_1' = 0
            tau_2' = 1.0
            tau_3' = 1.0
        inv:
            tx + 10.0 >= 0
        ]

        mode 2 [
        dyn:
            tx' = -5.0
            bx' = vb
            vb' = 0.3
            tau_1' = 0
            tau_2' = 1.0
            tau_3' = 1.0
        inv:
            tx + 10.0 >= 0
        ]
        """

        dummy_ha = HybridAutomaton("dummy")
        tx = Real("tx")
        bx = Real("bx")
        vb = Real("vb")
        tau1 = Real("tau1")
        tau2 = Real("tau2")
        tau3 = Real("tau3")

        dyn = Ode([tx, bx, vb, tau1, tau2, tau3],
                  [RealVal("-5.0"), vb, RealVal("0.3"), RealVal("0"), RealVal("1.0"), RealVal("1.0")])
        const = Geq(Add(tx, RealVal("10.0")), RealVal("0"))

        mode1 = Mode("mode1", None)
        mode1.set_dynamics(dyn)
        mode1.set_invariant(const)

        mode2 = Mode("mode2", None)
        mode2.set_dynamics(dyn)
        mode2.set_invariant(const)

        merged_mode, is_merged = merge_mode(mode1, mode2, dummy_ha)
        self.assertEqual(is_merged, True, 'merging fail')
        self.assertEqual(repr(merged_mode),
                         "( aggregated mode dummy_mode1_mode2 = dyn: ode([tx, bx, vb, tau1, tau2, tau3] = [-5.0, vb, 0.3, 0, 1.0, 1.0]), inv: (>= (+ tx 10.0) 0) )",
                         'merging fail because of strange mode generation')

    def test_merge_agg_mode(self):
        """Simple mode merging test: agg mode1 (x' = 1, x >= 2) and mode2 (x' = 1, x >= 3)"""
        dummy_ha = HybridAutomaton("dummy")
        x = Real("x")
        dyn = Ode([x], [RealVal("1")])
        const1 = Geq(x, RealVal("2"))
        const2 = Geq(x, RealVal("3"))

        mode1 = Mode("mode1", None)
        mode1.set_dynamics(dyn)
        mode1.set_invariant(const1)

        mode2 = Mode("mode2", None)
        mode2.set_dynamics(dyn)
        mode2.set_invariant(const2)

        merged_mode, is_merged = merge_mode(mode1, mode2, dummy_ha)

        self.assertEqual(is_merged, True, 'merging fail')
        self.assertEqual(repr(merged_mode),
                         "( aggregated mode dummy_mode1_mode2 = dyn: ode([x] = [1]), inv: (>= x 2) )",
                         'merging fail because of strange mode generation')

        mode3 = Mode("mode3", None)
        mode3.set_dynamics(dyn)
        mode3.set_invariant(const2)

        merged_mode2, is_merged2 = merge_mode(merged_mode, mode3, dummy_ha)
        self.assertEqual(is_merged2, True, 'merging fail')
        self.assertEqual(repr(merged_mode2),
                         "( aggregated mode dummy_mode1_mode2_mode3 = dyn: ode([x] = [1]), inv: (>= x 2) )",
                         'merging fail because of strange mode generation')

    def test_merge_none_mode(self):
        """Simple mode merging test: mode1 (None, None), mode2 (None, None), mode3 (None, None), mode4 (None, None),
            and mode5 (None, None)
        """
        dummy_ha = HybridAutomaton("dummy")
        mode1 = Mode("mode1", None)
        mode2 = Mode("mode2", None)
        mode3 = Mode("mode3", None)
        mode4 = Mode("mode4", None)
        mode5 = Mode("mode5", None)

        merged_mode_1_2, is_merged_1_2 = merge_mode(mode1, mode2, dummy_ha)

        self.assertEqual(is_merged_1_2, True, 'merging fail')
        self.assertEqual(repr(merged_mode_1_2), "( aggregated mode dummy_mode1_mode2 = dyn: None, inv: None )",
                         'merging fail because of strange mode generation')

        merged_mode_1_2_3, is_merged_1_2_3 = merge_mode(merged_mode_1_2, mode3, dummy_ha)

        self.assertEqual(is_merged_1_2_3, True, 'merging fail')
        self.assertEqual(repr(merged_mode_1_2_3), "( aggregated mode dummy_mode1_mode2_mode3 = dyn: None, inv: None )",
                         'merging fail because of strange mode generation')

        merged_mode_1_2_3_4, is_merged_1_2_3_4 = merge_mode(merged_mode_1_2_3, mode4, dummy_ha)

        self.assertEqual(is_merged_1_2_3_4, True, 'merging fail')
        self.assertEqual(repr(merged_mode_1_2_3_4),
                         "( aggregated mode dummy_mode1_mode2_mode3_mo ... = dyn: None, inv: None )",
                         'merging fail because of strange mode generation')

        merged_mode_1_2_3_4_5, is_merged_1_2_3_4_5 = merge_mode(merged_mode_1_2_3_4, mode5, dummy_ha)

        self.assertEqual(is_merged_1_2_3_4_5, True, 'merging fail')
        self.assertEqual(repr(merged_mode_1_2_3_4_5),
                         "( aggregated mode dummy_mode1_mode2_mode3_mo ... = dyn: None, inv: None )",
                         'merging fail because of strange mode generation')

    def test_not_merge_mode(self):
        """Simple mode merging test: merged_mode = { mode1 (x' = 1, x >= 2), mode2 (x' = 1, x >= 3) } and mode (x' =
        1, x <= -1) """
        dummy_ha = HybridAutomaton("dummy")
        x = Real("x")
        dyn = Ode([x], [RealVal("1")])
        const1 = Geq(x, RealVal("2"))
        const2 = Geq(x, RealVal("3"))

        mode1 = Mode("mode1", None)
        mode1.set_dynamics(dyn)
        mode1.set_invariant(const1)

        mode2 = Mode("mode2", None)
        mode2.set_dynamics(dyn)
        mode2.set_invariant(const2)

        merged_mode, is_merged = merge_mode(mode1, mode2, dummy_ha)

        mode3 = Mode("mode3", None)
        const3 = Leq(x, RealVal("-1"))
        mode3.set_dynamics(dyn)
        mode3.set_invariant(const3)

        not_merged_mode, not_merged = merge_mode(merged_mode, mode3, dummy_ha)

        self.assertEqual(not_merged, False, 'merging fail')
        self.assertEqual(not_merged_mode, None,
                         'merging fail because of strange mode generation')

    def test_hybrid_automaton_indexing_simple(self):
        """Simple automaton indexing test:
            Modes:
                modeA (dyn : x' = 1, inv : None)
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : None)
                mode4 (dyn : x' = 1, inv : None)
            Transitions:
                modeA -> mode4 (no constraints)
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
                mode3 -> mode4 (no constraints)
        """
        x = Real("x")
        dyn = Ode([x], [RealVal("1")])

        ha = HybridAutomaton("ha")
        mode1 = ha.new_mode("mode1")
        mode1.set_dynamics(dyn)

        modeA = ha.new_mode("modeA")
        modeA.set_dynamics(dyn)

        mode2 = ha.new_mode("mode2")
        mode2.set_dynamics(dyn)

        mode3 = ha.new_mode("mode3")
        mode3.set_dynamics(dyn)

        mode4 = ha.new_mode("mode4")
        mode4.set_dynamics(dyn)

        ha.new_transition("trans1", mode1, mode2)
        ha.new_transition("trans2", mode2, mode3)
        ha.new_transition("trans3", mode3, mode4)
        ha.new_transition("trans4", modeA, mode4)

        indexing_dict = indexing(ha)
        sorted_key = sorted(indexing_dict.keys(), reverse=True)
        sorted_elem = list()
        for k in sorted_key:
            assert (isinstance(indexing_dict[k], set))
            sorted_elem.append([e.name for e in sorted(list(indexing_dict[k]), key=lambda e: e.name)])

        self.assertEqual(str(sorted_key), "[4, 3, 2, 1]",
                         "indexing failed")
        self.assertEqual(str(sorted_elem), "[['mode1'], ['mode2'], ['mode3', 'modeA'], ['mode4']]",
                         "indexing failed")

    def test_hybrid_automaton_indexing(self):
        """Simple automaton indexing test:
            Modes:
                modeA (dyn : x' = 1, inv : None)
                modeB (dyn : x' = 1, inv : None)
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : None)
                mode4 (dyn : x' = 1, inv : None)
            Transitions:
                modeA -> mode4 (no constraints)
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
                mode3 -> mode4 (no constraints)
                modeB -> mode2 (no constraints)
        """
        x = Real("x")
        dyn = Ode([x], [RealVal("1")])

        ha = HybridAutomaton("ha")
        modeA = ha.new_mode("modeA")
        modeA.set_dynamics(dyn)

        modeB = ha.new_mode("modeB")
        modeB.set_dynamics(dyn)

        mode1 = ha.new_mode("mode1")
        mode1.set_dynamics(dyn)

        mode2 = ha.new_mode("mode2")
        mode2.set_dynamics(dyn)

        mode3 = ha.new_mode("mode3")
        mode3.set_dynamics(dyn)

        mode4 = ha.new_mode("mode4")
        mode4.set_dynamics(dyn)

        ha.new_transition("trans1", mode1, mode2)
        ha.new_transition("trans2", mode2, mode3)
        ha.new_transition("trans3", mode3, mode4)
        ha.new_transition("trans4", modeA, mode4)
        ha.new_transition("trans5", modeB, mode2)

        indexing_dict = indexing(ha)
        sorted_key = sorted(indexing_dict.keys(), reverse=True)
        sorted_elem = list()
        for k in sorted_key:
            assert (isinstance(indexing_dict[k], set))
            sorted_elem.append([e.name for e in sorted(list(indexing_dict[k]), key=lambda e: e.name)])

        self.assertEqual(str(sorted_key), "[4, 3, 2, 1]",
                         "indexing failed")
        self.assertEqual(str(sorted_elem), "[['mode1', 'modeB'], ['mode2'], ['mode3', 'modeA'], ['mode4']]",
                         "indexing failed")

    def test_hybrid_automaton_merge(self):
        """Simple automaton merging test (all have same length) :
            HybridAutomaton1 [
            Modes:
                mode A (dyn : x' = 1, inv : None)
                modeB (dyn : x' = 1, inv : None)
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : None)
                mode4 (dyn : x' = 1, inv : None)
            Transitions:
                modeA -> mode4 (no constraints)
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
                mode3 -> mode4 (no constraints)
                modeB -> mode2 (no constraints)
            ]

            HybridAutomaton2 [
            Modes:
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : None)
                mode4 (dyn : x' = 1, inv : None)
            Transitions:
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
                mode3 -> mode4 (no constraints)
            ]

            HybridAutomaton3 [
            Modes:
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : None)
                mode4 (dyn : x' = 1, inv : None)
            Transitions:
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
                mode3 -> mode4 (no constraints)
            ]

        """
        x = Real("x")
        dyn = Ode([x], [RealVal("1")])

        ha1 = HybridAutomaton("ha1")
        mode1_A = ha1.new_mode("modeA")
        mode1_A.set_dynamics(dyn)

        mode1_B = ha1.new_mode("modeB")
        mode1_B.set_dynamics(dyn)

        mode1_1 = ha1.new_mode("mode1")
        mode1_1.set_dynamics(dyn)

        mode1_2 = ha1.new_mode("mode2")
        mode1_2.set_dynamics(dyn)

        mode1_3 = ha1.new_mode("mode3")
        mode1_3.set_dynamics(dyn)

        mode1_4 = ha1.new_mode("mode4")
        mode1_4.set_dynamics(dyn)

        ha1.new_transition("trans1", mode1_1, mode1_2)
        ha1.new_transition("trans2", mode1_2, mode1_3)
        ha1.new_transition("trans3", mode1_3, mode1_4)
        ha1.new_transition("trans4", mode1_A, mode1_4)
        ha1.new_transition("trans5", mode1_B, mode1_2)

        ha2 = HybridAutomaton("ha2")
        mode2_1 = ha2.new_mode("mode1")
        mode2_1.set_dynamics(dyn)

        mode2_2 = ha2.new_mode("mode2")
        mode2_2.set_dynamics(dyn)

        mode2_3 = ha2.new_mode("mode3")
        mode2_3.set_dynamics(dyn)

        mode2_4 = ha2.new_mode("mode4")
        mode2_4.set_dynamics(dyn)

        ha2.new_transition("trans1", mode2_1, mode2_2)
        ha2.new_transition("trans2", mode2_2, mode2_3)
        ha2.new_transition("trans3", mode2_3, mode2_4)

        ha3 = HybridAutomaton("ha3")
        mode3_1 = ha3.new_mode("mode1")
        mode3_1.set_dynamics(dyn)

        mode3_2 = ha3.new_mode("mode2")
        mode3_2.set_dynamics(dyn)

        mode3_3 = ha3.new_mode("mode3")
        mode3_3.set_dynamics(dyn)

        mode3_4 = ha3.new_mode("mode4")
        mode3_4.set_dynamics(dyn)

        ha3.new_transition("trans1", mode3_1, mode3_2)
        ha3.new_transition("trans2", mode3_2, mode3_3)
        ha3.new_transition("trans3", mode3_3, mode3_4)

        # ha = merge(ha1, ha2, ha3, chi_optimization=False)
        # self.assertEqual(len(ha.modes), 4, "mode size is differ")
        # self.assertEqual(len(ha.transitions), 3, "transition size is differ")

        ha2 = new_merge(ha1, ha2, ha3, chi_optimization=False, syntatic_merging=True)
        self.assertEqual(len(ha2.modes), 4, "mode size is differ")
        self.assertEqual(len(ha2.transitions), 3, "transition size is differ")

    def test_not_hybrid_automaton_merge(self):
        """Simple automaton merging test (all have same length) :

            HybridAutomaton1 [
            Modes:
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : None)
            Transitions:
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
            ]

            HybridAutomaton2 [
            Modes:
                mode1 (dyn : y' = 1, inv : None)
                mode2 (dyn : y' = 1, inv : None)
                mode3 (dyn : y' = 1, inv : None)
            Transitions:
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
            ]

            HybridAutomaton3 [
            Modes:
                mode1 (dyn : z' = 1, inv : None)
                mode2 (dyn : z' = 1, inv : None)
                mode3 (dyn : z' = 1, inv : None)
            Transitions:
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
            ]

        """
        x = Real("x")
        y = Real("y")
        z = Real("z")
        dyn1 = Ode([x], [RealVal("1")])
        dyn2 = Ode([y], [RealVal("1")])
        dyn3 = Ode([z], [RealVal("1")])

        ha1 = HybridAutomaton("ha1")
        mode1_1 = ha1.new_mode("mode1")
        mode1_1.set_dynamics(dyn1)

        mode1_2 = ha1.new_mode("mode2")
        mode1_2.set_dynamics(dyn1)

        mode1_3 = ha1.new_mode("mode3")
        mode1_3.set_dynamics(dyn1)

        ha1.new_transition("trans1", mode1_1, mode1_2)
        ha1.new_transition("trans2", mode1_2, mode1_3)

        ha2 = HybridAutomaton("ha2")
        mode2_1 = ha2.new_mode("mode1")
        mode2_1.set_dynamics(dyn2)

        mode2_2 = ha2.new_mode("mode2")
        mode2_2.set_dynamics(dyn2)

        mode2_3 = ha2.new_mode("mode3")
        mode2_3.set_dynamics(dyn2)

        ha2.new_transition("trans1", mode2_1, mode2_2)
        ha2.new_transition("trans2", mode2_2, mode2_3)

        ha3 = HybridAutomaton("ha3")
        mode3_1 = ha3.new_mode("mode1")
        mode3_1.set_dynamics(dyn3)

        mode3_2 = ha3.new_mode("mode2")
        mode3_2.set_dynamics(dyn3)

        mode3_3 = ha3.new_mode("mode3")
        mode3_3.set_dynamics(dyn3)

        ha3.new_transition("trans1", mode3_1, mode3_2)
        ha3.new_transition("trans2", mode3_2, mode3_3)

        ha = new_merge(ha1, ha2, ha3, chi_optimization=False)
        self.assertEqual(len(ha.modes), 9, "mode size is differ")
        self.assertEqual(len(ha.transitions), 6, "transition size is differ")

    def test_hybrid_automaton_merge_different_depth(self):
        """Simple automaton merging test (all have same length) :

            HybridAutomaton1 [
            Modes:
                mode1 (dyn : y' = 1, inv : None)
                mode2 (dyn : z' = 1, inv : None)
            Transitions:
                mode1 -> mode2 (no constraints)
            ]

            HybridAutomaton2 [
            Modes:
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : y' = 1, inv : None)
                mode3 (dyn : z' = 1, inv : None)
            Transitions:
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
            ]

        """
        x = Real("x")
        y = Real("y")
        z = Real("z")
        dyn1 = Ode([x], [RealVal("1")])
        dyn2 = Ode([y], [RealVal("1")])
        dyn3 = Ode([z], [RealVal("1")])

        ha1 = HybridAutomaton("ha1")
        mode1_1 = ha1.new_mode("mode1")
        mode1_1.set_dynamics(dyn2)

        mode1_2 = ha1.new_mode("mode2")
        mode1_2.set_dynamics(dyn3)

        ha1.new_transition("trans1", mode1_1, mode1_2)

        ha2 = HybridAutomaton("ha2")
        mode2_1 = ha2.new_mode("mode1")
        mode2_1.set_dynamics(dyn1)

        mode2_2 = ha2.new_mode("mode2")
        mode2_2.set_dynamics(dyn2)

        mode2_3 = ha2.new_mode("mode3")
        mode2_3.set_dynamics(dyn3)

        ha2.new_transition("trans1", mode2_1, mode2_2)
        ha2.new_transition("trans2", mode2_2, mode2_3)

        ha = new_merge(ha1, ha2, chi_optimization=False)
        self.assertEqual(len(ha.modes), 3, "mode size is differ")
        self.assertEqual(len(ha.transitions), 2, "transition size is differ")

    def test_hybrid_automaton_merge_optimization_true(self):
        """Simple automaton merging test (all have same length) :
            HybridAutomaton1 [
            Modes:
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : None)
            Transitions:
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
            ]

            HybridAutomaton2 [
            Modes:
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : None)
            Transitions:
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
            ]
        """
        x = Real("x")
        dyn = Ode([x], [RealVal("1")])

        ha1 = HybridAutomaton("ha1")
        ha1mode1 = ha1.new_mode("mode1")
        ha1mode1.set_dynamics(dyn)
        ha1mode1.chi_valuation["chi_1_1"] = True
        ha1mode1.chi_valuation["chi_1_2"] = True

        ha1mode2 = ha1.new_mode("mode2")
        ha1mode2.set_dynamics(dyn)
        ha1mode2.chi_valuation["chi_2_1"] = True
        ha1mode2.chi_valuation["chi_2_2"] = False

        ha1mode3 = ha1.new_mode("mode3")
        ha1mode3.set_dynamics(dyn)
        ha1mode3.chi_valuation["chi_3_1"] = False
        ha1mode3.chi_valuation["chi_3_2"] = False

        ha1.new_transition("trans1", ha1mode1, ha1mode2)
        ha1.new_transition("trans2", ha1mode2, ha1mode3)

        ha2 = HybridAutomaton("ha2")
        ha2mode1 = ha2.new_mode("mode1")
        ha2mode1.set_dynamics(dyn)
        ha2mode1.chi_valuation["chi_1_1"] = True
        ha2mode1.chi_valuation["chi_1_2"] = True

        ha2mode2 = ha2.new_mode("mode2")
        ha2mode2.set_dynamics(dyn)
        ha2mode2.chi_valuation["chi_2_1"] = False
        ha2mode2.chi_valuation["chi_2_2"] = False

        ha2mode3 = ha2.new_mode("mode3")
        ha2mode3.set_dynamics(dyn)
        ha2mode3.chi_valuation["chi_3_1"] = False
        ha2mode3.chi_valuation["chi_3_2"] = False

        ha2.new_transition("trans1", ha2mode1, ha2mode2)
        ha2.new_transition("trans2", ha2mode2, ha2mode3)

        ha = merge(ha1, ha2, chi_optimization=True)
        self.assertEqual(len(ha.modes), 4, "mode size is differ")
        self.assertEqual(len(ha.transitions), 4, "transition size is differ")

    def test_hybrid_automaton_merge_optimization_false(self):
        """Simple automaton merging test (all have same length) :
            HybridAutomaton1 [
            Modes:
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : None)
            Transitions:
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
            ]

            HybridAutomaton2 [
            Modes:
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : None)
            Transitions:
                mode1 -> mode2 (no constraints)
                mode2 -> mode3 (no constraints)
            ]
        """
        x = Real("x")
        dyn = Ode([x], [RealVal("1")])

        ha1 = HybridAutomaton("ha1")
        ha1mode1 = ha1.new_mode("mode1")
        ha1mode1.set_dynamics(dyn)
        ha1mode1.chi_valuation["chi_1_1"] = True
        ha1mode1.chi_valuation["chi_1_2"] = True

        ha1mode2 = ha1.new_mode("mode2")
        ha1mode2.set_dynamics(dyn)
        ha1mode2.chi_valuation["chi_2_1"] = True
        ha1mode2.chi_valuation["chi_2_2"] = False

        ha1mode3 = ha1.new_mode("mode3")
        ha1mode3.set_dynamics(dyn)
        ha1mode3.chi_valuation["chi_3_1"] = False
        ha1mode3.chi_valuation["chi_3_2"] = False

        ha1.new_transition("trans1", ha1mode1, ha1mode2)
        ha1.new_transition("trans2", ha1mode2, ha1mode3)

        ha2 = HybridAutomaton("ha2")
        ha2mode1 = ha2.new_mode("mode1")
        ha2mode1.set_dynamics(dyn)
        ha2mode1.chi_valuation["chi_1_1"] = True
        ha2mode1.chi_valuation["chi_1_2"] = True

        ha2mode2 = ha2.new_mode("mode2")
        ha2mode2.set_dynamics(dyn)
        ha2mode2.chi_valuation["chi_2_1"] = False
        ha2mode2.chi_valuation["chi_2_2"] = False

        ha2mode3 = ha2.new_mode("mode3")
        ha2mode3.set_dynamics(dyn)
        ha2mode3.chi_valuation["chi_3_1"] = False
        ha2mode3.chi_valuation["chi_3_2"] = False

        ha2.new_transition("trans1", ha2mode1, ha2mode2)
        ha2.new_transition("trans2", ha2mode2, ha2mode3)

        ha = merge(ha1, ha2, chi_optimization=False)
        self.assertEqual(len(ha.modes), 3, "mode size is differ")
        self.assertEqual(len(ha.transitions), 2, "transition size is differ")

        ha = new_merge(ha1, ha2, chi_optimization=False)
        self.assertEqual(len(ha.modes), 3, "mode size is differ")
        self.assertEqual(len(ha.transitions), 2, "transition size is differ")

    def test_hybrid_automaton_syntatic_merging(self):
        """Simple automaton merging test (all have same length) :
            HybridAutomaton1 [
            Modes:
                mode1 (dyn : x' = 1, inv : And((x >= 1.5) (x < 2.0))
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : And (x <= 11))
            Transitions:
                mode1 -> mode2 (And (x >= 1) (x <= 2))
                mode2 -> mode3 (And (x >= -1) (x <= 10))
            ]

            HybridAutomaton2 [
            Modes:
                mode1 (dyn : x' = 1, inv : And((x < 2.0)(x >= 1.5))
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : And (x <= 11))
            Transitions:
                mode1 -> mode2 (And (x <= 2) (x >= 1))
                mode2 -> mode3 (And (x >= -1) (x <= 10))
            ]

            HybridAutomaton3 [
            Modes:
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : And (x <= 11))
            Transitions:
                mode1 -> mode2 (And (x <= 2) (x >= 1))
                mode2 -> mode3 (And (x >= -1) (x <= 10))
            ]
        """
        x = Real("x")
        dyn = Ode([x], [RealVal("1")])

        const1_1 = And([x >= RealVal("1.5"), x < RealVal("2.0")])
        const1_3 = And([x <= RealVal("11")])

        const2_1 = And([x < RealVal("2.0"), x >= RealVal("1.5")])
        const2_3 = And([x <= RealVal("11")])

        trans_const1_1 = And([x >= RealVal("1"), x <= RealVal("2")])
        trans_const1_2 = And([x >= RealVal("-1"), x >= RealVal("10")])

        trans_const2_1 = And([x <= RealVal("2"), x >= RealVal("1")])
        trans_const2_2 = And([x >= RealVal("-1"), x >= RealVal("10")])

        ha1 = HybridAutomaton("ha1")
        ha1mode1 = ha1.new_mode("mode1")
        ha1mode1.set_dynamics(dyn)
        ha1mode1.set_invariant(const1_1)

        ha1mode2 = ha1.new_mode("mode2")
        ha1mode2.set_dynamics(dyn)

        ha1mode3 = ha1.new_mode("mode3")
        ha1mode3.set_dynamics(dyn)
        ha1mode3.set_invariant(const1_3)

        ha1.new_transition("trans1", ha1mode1, ha1mode2).set_guard(trans_const1_1)
        ha1.new_transition("trans2", ha1mode2, ha1mode3).set_guard(trans_const1_2)

        ha2 = HybridAutomaton("ha2")
        ha2mode1 = ha2.new_mode("mode1")
        ha2mode1.set_dynamics(dyn)
        ha2mode1.set_invariant(const2_1)

        ha2mode2 = ha2.new_mode("mode2")
        ha2mode2.set_dynamics(dyn)

        ha2mode3 = ha2.new_mode("mode3")
        ha2mode3.set_dynamics(dyn)
        ha2mode3.set_invariant(const2_3)

        ha2.new_transition("trans1", ha2mode1, ha2mode2).set_guard(trans_const2_1)
        ha2.new_transition("trans2", ha2mode2, ha2mode3).set_guard(trans_const2_2)

        ha3 = HybridAutomaton("ha3")
        ha3mode1 = ha3.new_mode("mode1")
        ha3mode1.set_dynamics(dyn)

        ha3mode2 = ha3.new_mode("mode2")
        ha3mode2.set_dynamics(dyn)

        ha3mode3 = ha3.new_mode("mode3")
        ha3mode3.set_dynamics(dyn)
        ha3mode3.set_invariant(const1_3)

        ha3.new_transition("trans1", ha3mode1, ha3mode2).set_guard(trans_const2_1)
        ha3.new_transition("trans2", ha3mode2, ha3mode3).set_guard(trans_const2_2)

        ha = new_merge(ha1, ha2, syntatic_merging=True)
        self.assertEqual(len(ha.modes), 3, "mode size is differ")
        self.assertEqual(len(ha.transitions), 2, "transition size is differ")

        ha2 = new_merge(ha1, ha3, syntatic_merging=True)
        self.assertEqual(len(ha2.modes), 4, "mode size is differ")
        self.assertEqual(len(ha2.transitions), 3, "transition size is differ")

    def test_hybrid_automaton_big_merging(self):
        """Simple automaton merging test (all have same length) :
            HybridAutomaton1 [
            Modes:
                mode1 (dyn : x' = 1, inv : And((x >= 1.5) (x < 2.0))
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : And (x <= 11))
            Transitions:
                mode1 -> mode2 (And (x >= 1) (x <= 2))
                mode2 -> mode3 (And (x >= -1) (x <= 10))
            ]

            HybridAutomaton2 [
            Modes:
                mode1 (dyn : x' = 1, inv : And((x < 2.0)(x >= 1.5))
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : And (x <= 11))
            Transitions:
                mode1 -> mode2 (And (x <= 2) (x >= 1))
                mode2 -> mode3 (And (x >= -1) (x <= 10))
            ]

            HybridAutomaton3 [
            Modes:
                mode1 (dyn : x' = 1, inv : None)
                mode2 (dyn : x' = 1, inv : None)
                mode3 (dyn : x' = 1, inv : And (x <= 11))
            Transitions:
                mode1 -> mode2 (And (x <= 2) (x >= 1))
                mode2 -> mode3 (And (x >= -1) (x <= 10))
            ]
        """
        x = Real("x")
        dyn = Ode([x], [RealVal("1")])

        # for type 1 hybrid automaton
        type1_invs = [And([x >= RealVal("1.5"), x < RealVal("2.0")]), None, And([x <= RealVal("11")])]
        type1_guard = [And([x >= RealVal("1"), x <= RealVal("2")]), And([x >= RealVal("-1"), x >= RealVal("10")])]

        # for type 2 hybrid automaton
        type2_invs = [And([x < RealVal("2.0"), x >= RealVal("1.5")]), None, And([x <= RealVal("11")])]
        type2_guard = [And([x <= RealVal("2"), x >= RealVal("1")]), And([x >= RealVal("-1"), x >= RealVal("10")])]

        hybrid_automata_queue = list()
        for i in range(0, 4500):
            ha = HybridAutomaton("ha{}".format(i))
            modes = list()
            for j in range(len(type2_invs)):
                mode = ha.new_mode("mode{}".format(j))
                mode.set_dynamics(dyn)
                if type1_invs[j] is not None:
                    mode.set_invariant(type1_invs[j])
                modes.append(mode)

            for j in range(len(type2_invs) - 1):
                ha.new_transition("trans{}".format(j), modes[j], modes[j + 1]).set_guard(type1_guard[j])

            hybrid_automata_queue.append(ha)

        ha = new_merge(*hybrid_automata_queue, syntatic_merging=True)
        # ha2 = HybridAutomaton("ha2")
        # ha2mode1 = ha2.new_mode("mode1")
        # ha2mode1.set_dynamics(dyn)
        # ha2mode1.set_invariant(const2_1)
        #
        # ha2mode2 = ha2.new_mode("mode2")
        # ha2mode2.set_dynamics(dyn)
        #
        # ha2mode3 = ha2.new_mode("mode3")
        # ha2mode3.set_dynamics(dyn)
        # ha2mode3.set_invariant(const2_3)
        #
        # ha2.new_transition("trans1", ha2mode1, ha2mode2).set_guard(trans_const2_1)
        # ha2.new_transition("trans2", ha2mode2, ha2mode3).set_guard(trans_const2_2)
        #
        # ha3 = HybridAutomaton("ha3")
        # ha3mode1 = ha3.new_mode("mode1")
        # ha3mode1.set_dynamics(dyn)
        #
        # ha3mode2 = ha3.new_mode("mode2")
        # ha3mode2.set_dynamics(dyn)
        #
        # ha3mode3 = ha3.new_mode("mode3")
        # ha3mode3.set_dynamics(dyn)
        # ha3mode3.set_invariant(const1_3)
        #
        # ha3.new_transition("trans1", ha3mode1, ha3mode2).set_guard(trans_const2_1)
        # ha3.new_transition("trans2", ha3mode2, ha3mode3).set_guard(trans_const2_2)
        #
        # ha = merge(ha1, ha2, syntatic_merging=True)
        # self.assertEqual(len(ha.modes), 3, "mode size is differ")
        # self.assertEqual(len(ha.transitions), 2, "transition size is differ")
        #
        # ha2 = merge(ha1, ha3, syntatic_merging=True)
        # self.assertEqual(len(ha2.modes), 4, "mode size is differ")
        # self.assertEqual(len(ha2.transitions), 3, "transition size is differ")
        self.assertTrue("ss")
