import unittest

from stlmcPy.constraints.constraints import Real, RealVal, Sqrt, Cos, Ode
from stlmcPy.constraints.operations import expr_syntatic_equality, dynamic_syntatic_eqaulity


class ConstraintTest(unittest.TestCase):
    def test_variable_equal(self):
        x = Real("x")
        y = Real("y")

        self.assertEqual(expr_syntatic_equality(x, y), False, "cannot be the same")
        self.assertEqual(expr_syntatic_equality(y, x), False, "cannot be the same")
        self.assertEqual(expr_syntatic_equality(x, x), True, "must be the same")
        self.assertEqual(expr_syntatic_equality(y, y), True, "must be the same")

    def test_add_equal(self):
        x = Real("x")
        y = Real("y")
        c1 = RealVal("1")
        c2 = RealVal("2")
        c3 = RealVal("3")

        p1 = x + y
        p2 = x + c1
        p3 = y + c2
        p4 = y + c3

        q1 = x + y
        q2 = y + x

        self.assertEqual(expr_syntatic_equality(p1, p1), True, "add not equal")
        self.assertEqual(expr_syntatic_equality(p1, q1), True, "add not equal")
        self.assertEqual(expr_syntatic_equality(p1, p2), False, "add equal")
        self.assertEqual(expr_syntatic_equality(p1, p3), False, "add equal")
        self.assertEqual(expr_syntatic_equality(p1, p4), False, "add equal")
        self.assertEqual(expr_syntatic_equality(q1, q2), True, "add equal")

    def test_sub_equal(self):
        def test_add_equal(self):
            x = Real("x")
            y = Real("y")
            c1 = RealVal("1")
            c2 = RealVal("2")
            c3 = RealVal("3")

            p1 = x - y
            p2 = x - c1
            p3 = y - c2
            p4 = y - c3

            q1 = x - y
            q2 = y - x

            self.assertEqual(expr_syntatic_equality(p1, p1), True, "add not equal")
            self.assertEqual(expr_syntatic_equality(p1, q1), True, "add not equal")
            self.assertEqual(expr_syntatic_equality(p1, p2), False, "add equal")
            self.assertEqual(expr_syntatic_equality(p1, p3), False, "add equal")
            self.assertEqual(expr_syntatic_equality(p1, p4), False, "add equal")
            self.assertEqual(expr_syntatic_equality(q1, q2), True, "add equal")

    def test_neg_equal(self):
        x = Real("x")
        y = Real("y")

        p1 = -x
        p2 = -y

        self.assertEqual(expr_syntatic_equality(p1, p1), True, "add not equal")
        self.assertEqual(expr_syntatic_equality(p2, p1), False, "add equal")

    def test_arithmetic_equal(self):
        x = Real("x")
        y = Real("y")
        c = RealVal("2")

        p1 = x + y
        p2 = x ** y
        p3 = y - c
        p4 = y + x
        p5 = x + y
        p6 = -x
        p7 = Sqrt(x)
        p8 = Cos(y)
        p9 = Sqrt(x)
        p10 = Sqrt(y)

        self.assertEqual(expr_syntatic_equality(p1, p1), True, "add not equal")
        self.assertEqual(expr_syntatic_equality(p2, p3), False, "add equal")
        self.assertEqual(expr_syntatic_equality(p1, p3), False, "add equal")
        self.assertEqual(expr_syntatic_equality(p1, p4), True, "add not equal")
        self.assertEqual(expr_syntatic_equality(p1, p5), True, "add not equal")
        self.assertEqual(expr_syntatic_equality(p6, p8), False, "add equal")
        self.assertEqual(expr_syntatic_equality(p1, p7), False, "add equal")
        self.assertEqual(expr_syntatic_equality(p7, p9), True, "add not equal")
        self.assertEqual(expr_syntatic_equality(p9, p10), False, "add equal")

    def test_dynamics_equal(self):
        x = Real("x")
        y = Real("y")
        c = RealVal("2")
        c1 = RealVal("-2")

        p1 = x + y
        p2 = x ** y
        p3 = y - c
        p4 = y + x
        p5 = x + y
        p6 = -x
        p7 = Sqrt(x)
        p8 = Cos(y)
        p9 = Sqrt(x)
        p10 = Sqrt(y)

        d1 = Ode([x, y], [c, c1])
        d2 = Ode([y, x], [p3, p4])
        d3 = Ode([y, x], [c1, c])
        d4 = None

        self.assertEqual(dynamic_syntatic_eqaulity(d1, d3), True, "add not equal")
        self.assertEqual(dynamic_syntatic_eqaulity(d1, d2), False, "add equal")
        self.assertEqual(dynamic_syntatic_eqaulity(d2, d3), False, "add equal")
        self.assertEqual(dynamic_syntatic_eqaulity(d4, d1), False, "add equal")
        self.assertEqual(dynamic_syntatic_eqaulity(d4, d4), True, "add equal")