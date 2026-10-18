"""Numeric visualization never treats artifact strings as executable code."""
from fractions import Fraction
import math
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest

from stlmc.constraints.constraints import (
    Add, Arccos, Arcsin, Arctan, Cos, Div, IntVal, Mul, Pow, Real,
    RealVal, Sin, Function, Sqrt, Sub, Geq, Gt, Leq, Lt, Eq, Int, GloballyFormula,
)
from stlmc.constraints.interval import Interval, universeInterval
from stlmc.visualize.numbers import number_float, parse_number
from stlmc.visualize.numeric import infix_float
from stlmc.visualize.projection import continuous_values
from stlmc.visualize.sampling import DiscreteSampler, SolutionPointSampler, TimeSampler
from stlmc.visualize.robustness import robustness


class SafeVisualizationNumericTest(unittest.TestCase):
    def test_numeric_mode_arithmetic_uses_discrete_samples(self):
        mode = Real('mode')
        times = [[0., .25, .5], [.5, .75, 1.]]
        discrete = {mode: [[1., 1., 1.], [3., 3., 3.]]}
        for operator, sign in ((Geq, 1), (Gt, 1), (Leq, -1), (Lt, -1)):
            formula = operator(mode, RealVal('2'))
            with self.subTest(operator=operator.__name__):
                self.assertEqual(robustness(formula, {}, discrete, .25, times, 1., {}), -sign)
                self.assertEqual(robustness(formula, {}, discrete, .75, times, 1., {}), sign)

    def test_numeric_mode_equality_and_mixed_continuous_expression(self):
        mode, x = Real('mode'), Real('x')
        times = [[0., .5, 1.]]
        points = {x: [[2., 3., 4.]]}
        discrete = {mode: [[1., 1., 1.]]}
        self.assertEqual(robustness(Eq(mode, RealVal('2')), points, discrete,
                                    .5, times, 1., {}), -1.)
        self.assertEqual(robustness(Geq(Add(x, mode), RealVal('2')), points,
                                    discrete, .5, times, 1., {}), 2.)

    def test_integer_mode_arithmetic_uses_discrete_samples(self):
        mode = Int('mode')
        self.assertEqual(robustness(Geq(mode, IntVal('2')), {},
                                    {mode: [[3., 3.]]}, .5,
                                    [[0., .5]], 1., {}), 1.)

    def test_exact_numeric_spellings(self):
        for text, expected in [('1/2',Fraction(1,2)),('(1/2)',Fraction(1,2)),
                               ('(/ 1 2)',Fraction(1,2)),('(- (/ 1 2))',Fraction(-1,2)),
                               ('-.125e+2',Fraction(-25,2)),('1e-20',Fraction(1,10**20)),
                               (' +3. ',Fraction(3)),('((.25))',Fraction(1,4))]:
            with self.subTest(text=text):
                self.assertEqual(parse_number(text), expected)
        for text in ('inf','+Infinity','oo'):
            self.assertEqual(number_float(text), math.inf)
        self.assertEqual(number_float('-inf'), -math.inf)

    def test_invalid_numeric_syntax_and_limits(self):
        for text in ('nan','1+2','2**4','sqrt(4)','True','[1]', '1/0',
                     '(/ 1 0)','1e10001','1'*4097,'('*17+'1'+')'*17):
            with self.subTest(text=text[:40]):
                self.assertRaises(ValueError,parse_number,text)

    def test_malicious_numeric_strings_never_execute(self):
        with tempfile.TemporaryDirectory() as directory:
            marker=Path(directory)/'executed'
            payload="__import__('pathlib').Path({!r}).touch()".format(str(marker))
            for evaluate in (parse_number,number_float,
                             lambda text:infix_float(RealVal(text),[],[])):
                self.assertRaises(ValueError,evaluate,payload)
            self.assertFalse(marker.exists())

    def test_ground_arithmetic_and_transcendentals(self):
        expression=Add(Div(RealVal('(1/2)'),RealVal('2')),Pow(RealVal('2'),IntVal('3')))
        self.assertAlmostEqual(infix_float(expression,[],[]),8.25)
        for expr, expected in [(Sqrt(RealVal('4')),2),(Sin(RealVal('0')),0),
                               (Cos(RealVal('0')),1),(Arcsin(RealVal('0')),0),
                               (Arccos(RealVal('1')),0),(Arctan(RealVal('0')),0)]:
            self.assertAlmostEqual(infix_float(expr,[],[]),expected)
        self.assertRaises(ValueError,infix_float,IntVal('1/2'),[],[])
        self.assertIsInstance(infix_float(IntVal('2'),[],[]),float)
        self.assertIsInstance(infix_float(Pow(IntVal('2'),IntVal('10')),[],[]),float)

    def test_solution_uses_typed_variable_identity_and_local_time(self):
        x=Real("__import__('os').system('never-execute')")
        time=Real('time')
        dynamics=Function([x],[Add(x,Add(Mul(time,time),Sin(time)))])
        points=SolutionPointSampler().generate_samples([3.,3.5,4.],dynamics,[2.])
        self.assertAlmostEqual(points[x][0],2.)
        self.assertAlmostEqual(points[x][1],2.+.25+math.sin(.5))
        self.assertAlmostEqual(points[x][2],3.+math.sin(1.))

    def test_projection_and_time_sampling_accept_exact_fractions(self):
        x=Real('x');a=Real('tau_0');z=Real('tau_1')
        assignment={Real('x_0_0'):RealVal('(/ 1 2)'),Real('x_0_t'):RealVal('(3/2)'),
                    a:RealVal('(1/2)'),z:RealVal('1e0')}
        self.assertEqual(continuous_values(assignment,{x:None},0),{'x':[(.5,1.5)]})
        projector=SimpleNamespace(assignment=assignment,get_variable_points=lambda:[a,z])
        samples=TimeSampler(projector).generate_samples()
        self.assertEqual((samples[0][0],samples[0][-1]),(.5,1.))

    def test_discrete_sampler_numeric_data_is_not_evaluated(self):
        x=Real('mode')
        projector=SimpleNamespace(assignment={Real('mode_0'):RealVal('(/ 3 2)')},
                                  get_mode_vars=lambda:{x})
        self.assertEqual(DiscreteSampler(projector).generate_samples_at([0.,1.],0),{x:[1.5,1.5]})
        projector.assignment[Real('mode_0')]=RealVal('__import__("os")')
        self.assertRaises(ValueError,DiscreteSampler(projector).generate_samples_at,[0.],0)

    def test_robustness_evaluates_ground_arithmetic_tree(self):
        x=Real('x')
        formula=Geq(Pow(x,RealVal('2')),RealVal('(1/2)'))
        self.assertEqual(robustness(formula,{x:[[2.]]},{},0.,[[0.]],1.,{}),3.5)

    def test_temporal_bounds_are_numeric_data_not_expressions(self):
        x=Real('x')
        def formula(left):
            return GloballyFormula(Interval(True,RealVal(left),True,RealVal('inf')),
                                   universeInterval,Geq(x,RealVal('0')))
        args=({x:[[3.,2.,1.]]},{},0.,[[0.,.5,1.]],1.,{})
        self.assertEqual(robustness(formula('(1/2)'),*args),2.)
        self.assertRaises(ValueError,robustness,formula('__import__("os")'),*args)


if __name__=='__main__':
    unittest.main()
