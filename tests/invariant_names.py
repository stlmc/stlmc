"""Invariant definitions must not alias across modules, atoms or bounds."""
import unittest

from stlmc.constraints.constraints import And, BoolVal, Eq, Forall, Leq, Ode, Real, RealVal
from stlmc.constraints.boolean_abstraction import make_boolean_abstract_consts
from stlmc.constraints.substitution import substitution
from stlmc.objects.model import StlMC


def model_with_invariants(module_count=1, atom_count=1):
    x, mode = Real('x'), Real('mode')
    modules = [dict(mode=And([Eq(mode, RealVal(str(index)))]),
                    inv=And([Leq(x, RealVal(str(5 + atom)))
                             for atom in range(atom_count)]),
                    flow=Ode([x], [RealVal('2')]), jump={}, jp_d={})
               for index in range(module_count)]
    return StlMC({'mode': mode}, {x: (True, -100, 100, True)}, {}, {},
                 modules, BoolVal('True'))


class InvariantNamespaceTest(unittest.TestCase):
    def test_all_namespace_components_are_preserved(self):
        model = model_with_invariants(12, 12)
        for bound in (0, 1, 10, 11, 20):
            model.make_invariant_consts(bound, model.make_flow_consts(bound)[1])
        definitions = {key: value for key, value in model.boolean_abstract.items()
                       if isinstance(value, Forall)}
        self.assertEqual(len(definitions), 12 * 12 * 5)
        for bound in (0, 1, 10, 11, 20):
            for module in range(12):
                for atom in range(12):
                    name = 'invAtomicID_m{}_i{}_{}'.format(module, atom, bound)
                    value = next(v for k, v in definitions.items() if k.id == name)
                    self.assertEqual(value.current_mode_number, module)
                    self.assertEqual(value.start_tau.id, 'tau_{}'.format(bound))
                    self.assertEqual(value.end_tau.id, 'tau_{}'.format(bound + 1))

    def violating_trace_formula(self, emulate_old_alias=False):
        model = model_with_invariants()
        invariants = []
        for bound in (0, 10):
            invariants.extend(model.make_invariant_consts(
                bound, model.make_flow_consts(bound)[1])[0])
        definitions = {key: value for key, value in model.boolean_abstract.items()
                       if isinstance(value, Forall)}
        if emulate_old_alias:
            old = next(k for k, value in definitions.items() if value.start_tau.id == 'tau_0')
            later = next(k for k, value in definitions.items() if value.start_tau.id == 'tau_10')
            invariants = [substitution(c, {old: later}) for c in invariants]
            definitions = {later: definitions[later]}
        # The old bound-10 definition overwrote bound 0, accepting x=3->18
        # over 7.5 seconds although the first invariant requires x<=5.
        fixed = {'tau_0': '0', 'tau_1': '7.5', 'tau_10': '8', 'tau_11': '9',
                 'currentMode_0': '0', 'currentMode_10': '0',
                 'x_0_0': '3', 'x_0_t': '18', 'x_10_0': '0', 'x_10_t': '2'}
        return And(invariants + [make_boolean_abstract_consts(definitions)] +
                   [Eq(Real(name), RealVal(value)) for name, value in fixed.items()])

    def test_later_bound_cannot_disable_first_invariant_z3(self):
        import z3
        from stlmc.solver.z3 import z3Obj
        solver = z3.Solver()
        solver.add(z3Obj(self.violating_trace_formula()))
        self.assertEqual(solver.check(), z3.unsat)

    def test_old_alias_reproduces_unsound_sat_control(self):
        import z3
        from stlmc.solver.z3 import z3Obj
        solver = z3.Solver()
        solver.add(z3Obj(self.violating_trace_formula(emulate_old_alias=True)))
        self.assertEqual(solver.check(), z3.sat)

    def test_later_bound_cannot_disable_first_invariant_yices(self):
        try:
            from stlmc.solver.yices import yicesObj
            from yices import Config, Context, Status, Terms
        except Exception as error:
            self.skipTest('optional Yices unavailable: {}'.format(error))
        config = Config()
        config.default_config_for_logic('QF_LRA')
        solver = Context(config)
        try:
            solver.assert_formula(Terms.parse_term(yicesObj(self.violating_trace_formula())))
            self.assertEqual(solver.check_context(), Status.UNSAT)
        finally:
            solver.dispose()
            config.dispose()


if __name__ == '__main__':
    unittest.main()
