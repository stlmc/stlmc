"""Display simplification never rewrites the model-checking formula tree."""
import contextlib
import io
import itertools
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'src'))
from stlmc.constraints import constraints as c
from stlmc.constraints.boolean_simplification import flatten_boolean
from stlmc.constraints.formatting import format_constraint, infix
from stlmc.artifacts.formula_index import index_subformulas
from stlmc.encoding.symbolic_discrete import formula_id
from stlmc.visualize.latex import formula2latex
from stlmc.visualize.text_output import model_text
from stlmc.utils.print import BasePrinter


class FormulaFormattingTest(unittest.TestCase):
    def setUp(self):
        self.a,self.b,self.d=map(c.Bool,('a','b','d'))

    def test_flatten_same_operator_preserves_order_and_duplicates(self):
        for kind,operator in [(c.And,'and'),(c.Or,'or')]:
            formula=kind([self.a,kind([self.b,kind([self.d,self.a])])])
            result=flatten_boolean(formula)
            self.assertEqual([id(child) for child in result.children],
                             [id(child) for child in (self.a,self.b,self.d,self.a)])
            self.assertEqual(format_constraint(formula),'('+operator+' a b d a)')

    def test_empty_singleton_neutral_and_absorbing_constants(self):
        for kind,neutral,absorbing in [(c.And,'True','False'),(c.Or,'False','True')]:
            self.assertEqual(flatten_boolean(kind([])).value,neutral)
            self.assertIs(flatten_boolean(kind([self.a])),self.a)
            self.assertIs(flatten_boolean(kind([c.BoolVal(neutral),kind([self.a])])),self.a)
            self.assertEqual(flatten_boolean(kind([self.a,c.BoolVal(absorbing)])).value,absorbing)

    def test_different_operators_and_assignments_are_not_rewritten(self):
        formula=c.And([self.a,c.Or([self.b,self.d]),c.Eq(self.a,c.BoolVal('True'))])
        self.assertEqual(format_constraint(formula),'(and a (or b d) (a = True))')
        self.assertIs(flatten_boolean(c.Not(formula)).child,formula)

    def test_nested_temporal_negation_implication_and_forall_render(self):
        local=c.Interval(True,c.RealVal('0'),False,c.RealVal('2'))
        global_time=c.Interval(True,c.RealVal('0'),False,c.RealVal('inf'))
        formula=c.GloballyFormula(local,global_time,
            c.Implies(c.Not(c.And([self.a,c.And([self.b,self.d])])),
                      c.FinallyFormula(local,global_time,c.Or([self.a,c.Or([self.b,self.d])]))))
        self.assertEqual(format_constraint(formula),
                         '([][0,2) ((not (and a b d)) -> (<>[0,2) (or a b d))))')
        integral=c.Integral(0,[c.Real('x_t')],[c.Real('x_0')],c.Ode([c.Real('x')],[c.RealVal('0')]))
        forall=c.Forall(0,c.Real('t'),c.RealVal('0'),c.And([self.a,c.And([self.b,self.d])]),integral)
        self.assertEqual(format_constraint(forall),'(forall 0 . (and a b d))')

    def test_source_children_repr_hash_and_formula_ids_are_unchanged(self):
        nested=c.And([self.b,self.d])
        formula=c.Or([self.a,c.And([nested,c.BoolVal('True')])])
        before=(repr(formula),hash(formula),tuple(map(id,formula.children)),
                tuple(map(id,nested.children)),[(id(k),v) for k,v in index_subformulas(formula)[1].items()],
                formula_id(formula),formula_id(nested))
        format_constraint(formula)
        infix(formula)
        formula2latex(formula)
        after=(repr(formula),hash(formula),tuple(map(id,formula.children)),
               tuple(map(id,nested.children)),[(id(k),v) for k,v in index_subformulas(formula)[1].items()],
               formula_id(formula),formula_id(nested))
        self.assertEqual(before,after)

    def test_binary_temporal_operands_flatten_independently(self):
        interval=c.Interval(True,c.RealVal('0'),True,c.RealVal('2'))
        for kind,operator in [(c.UntilFormula,'U'),(c.ReleaseFormula,'R')]:
            formula=kind(interval,interval,c.Or([self.a,c.Or([self.b,self.d])]),
                         c.And([self.a,c.And([self.b,self.d])]))
            self.assertEqual(format_constraint(formula),
                             '((or a b d) '+operator+'[0,2] (and a b d))')
            self.assertIn('(or a b d)',infix(formula))

    def test_interval_cache_is_not_mutated_by_plain_formatting(self):
        local=c.Interval(True,c.RealVal('0'),False,c.RealVal('2'))
        formula=c.GloballyFormula(local,local,self.a)
        # The constructor eagerly formats the local interval. Clear this
        # presentation cache to exercise a previously unformatted interval.
        local._str=None
        format_constraint(formula)
        self.assertIsNone(local._str)

    def test_boolean_truth_table_equivalence(self):
        def evaluate(node,values):
            if isinstance(node,c.Bool):return values[node.id]
            if isinstance(node,c.BoolVal):return node.value=='True'
            if isinstance(node,c.And):return all(evaluate(x,values) for x in node.children)
            if isinstance(node,c.Or):return any(evaluate(x,values) for x in node.children)
            raise AssertionError(type(node))
        for outer,inner in itertools.product((c.And,c.Or),repeat=2):
            formula=outer([self.a,outer([self.b,c.BoolVal('True')]),inner([self.d,c.BoolVal('False')])])
            for bits in itertools.product((False,True),repeat=3):
                values=dict(zip(('a','b','d'),bits))
                self.assertEqual(evaluate(formula,values),evaluate(flatten_boolean(formula),values))

    def test_infix_and_latex_support_nary_empty_and_singletons(self):
        formula=c.And([self.a,c.And([self.b,self.d])])
        self.assertEqual(infix(formula),'(a & b & d)')
        self.assertEqual(infix(c.Or([self.a,c.Or([self.b,self.d])])),'(a | b | d)')
        self.assertEqual(formula2latex(formula),'(a and b and d)')
        self.assertEqual(formula2latex(c.Or([])),'false')
        self.assertEqual(formula2latex(c.And([])),'true')
        self.assertEqual(formula2latex(c.And([self.a])),'a')

    def test_cli_and_text_use_the_same_common_format(self):
        formula=c.And([self.a,c.And([self.b,self.d])])
        output=io.StringIO()
        with contextlib.redirect_stdout(output):
            BasePrinter().run_finished('satisfied',2,0.1,formula,'up to bound 2')
        self.assertIn('  formula     : '+model_text(formula),output.getvalue())
        self.assertEqual(model_text(formula),format_constraint(formula))

    def test_text_keeps_human_readable_jump_primes(self):
        prime=c.Real("x##$%^&$%^&##'")
        formula=c.And([c.Eq(prime,c.Real('x')),c.And([self.a,self.b])])
        self.assertEqual(model_text(formula),"(and (x' = x) a b)")
        self.assertEqual(prime.id,"x##$%^&$%^&##'")


if __name__=='__main__':unittest.main()
