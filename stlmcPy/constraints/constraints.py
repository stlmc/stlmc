# start of base_objects
from stlmcPy.exception.exception import NotFoundElementError
from stlmcPy.tree.tree import Leaf, NonLeaf


class Interval:
    def __init__(self, left_end, left, right_end, right):
        self.left_end = left_end
        self.left = left
        self.right_end = right_end
        self.right = right
        self._str = None

    def __hash__(self):
        return hash(id(self))

    def __repr__(self):
        if self._str is None:
            self._str = ('[' if self.left_end else '(') + repr(self.left) + ',' + repr(self.right) + (
                ']' if self.right_end else ')')
        return self._str

    def __eq__(self, other):
        return isinstance(other,
                          Interval) and other.left_end == self.left_end and other.right_end == self.right_end and other.left == self.left and other.right == self.right


class Unary:
    def __init__(self, child):
        self.child = child
        self._str = None

    def get_child(self):
        return self.child

    def __repr__(self):
        if self._str is None:
            self._str = str(self.child)
        return self._str


class Binary:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self._str = None

    def get_left(self):
        return self.left

    def get_right(self):
        return self.right

    def __repr__(self):
        if self._str is None:
            return str(self.left) + " " + str(self.right)
        return self._str


class Multinary:
    def __init__(self, children):
        self.children = children
        self._str = None

    def at(self, i):
        if i < len(self.children):
            return self.children[i]
        else:
            raise NotFoundElementError(self, "not in the list")

    def __repr__(self):
        if self._str is None:
            repr_str = ""
            comma = " "
            for i, c in enumerate(self.children):
                if i == len(self.children) - 1:
                    repr_str += str(c)
                else:
                    repr_str += (str(c) + comma)
            self._str = repr_str
        return self._str


class Constraint:
    pass


class Expr(Constraint):
    def __sub__(self, num):
        return Sub(self, num)

    def __add__(self, num):
        return Add(self, num)

    def __mul__(self, num):
        return Mul(self, num)

    def __pow__(self, num):
        return Pow(self, num)

    def __truediv__(self, num):
        return Div(self, num)

    def __eq__(self, num):
        return Eq(self, num)

    def __ne__(self, other):
        return Neq(self, other)

    def __lt__(self, num):
        return Lt(self, num)

    def __le__(self, num):
        return Leq(self, num)

    def __gt__(self, num):
        return Gt(self, num)

    def __ge__(self, num):
        return Geq(self, num)

    def __neg__(self):
        return Neg(self)


class UnaryExpr(Expr, Unary):
    def __init__(self, child):
        Expr.__init__(self)
        Unary.__init__(self, child)
        self._str = Unary.__repr__(self)

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class BinaryExpr(Expr, Binary):
    def __init__(self, left, right):
        Expr.__init__(self)
        Binary.__init__(self, left, right)
        self._str = Binary.__repr__(self)

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class MultinaryExpr(Expr, Multinary):
    def __init__(self, children):
        Expr.__init__(self)
        Multinary.__init__(self, children)
        self._str = Multinary.__repr__(self)

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class Formula(Constraint):
    def __eq__(self, num):
        return Eq(self, num)

    def __ne__(self, other):
        return Neq(self, other)

    def __lt__(self, num):
        return Lt(self, num)

    def __le__(self, num):
        return Leq(self, num)

    def __gt__(self, num):
        return Gt(self, num)

    def __ge__(self, num):
        return Geq(self, num)


class UnaryFormula(Formula, Unary):
    def __init__(self, child):
        Formula.__init__(self)
        Unary.__init__(self, child)
        self._str = Unary.__repr__(self)

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class BinaryFormula(Formula, Binary):
    def __init__(self, left, right):
        Formula.__init__(self)
        Binary.__init__(self, left, right)
        self._range = False
        self._str = Binary.__repr__(self)

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class MultinaryFormula(Formula, Multinary):
    def __init__(self, children):
        Formula.__init__(self)
        Multinary.__init__(self, children)
        self._str = Multinary.__repr__(self)

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class Constant(Leaf, Expr):
    def __init__(self, var_type, value):
        Leaf.__init__(self)
        Expr.__init__(self)
        self.__value = value
        self.__type = var_type
        self._str = str(self.value)

    def __hash__(self):
        return hash(self._str)

    @property
    def value(self):
        return self.__value

    @property
    def type(self):
        return self.__type

    def __repr__(self):
        return self._str


class Variable(Leaf, Expr):
    def __init__(self, var_type: str, var_id: str):
        Leaf.__init__(self)
        Expr.__init__(self)
        self.__id = var_id
        self.__type = var_type
        self._str = str(self.__id)

    def __hash__(self):
        return hash(self._str)

    @property
    def type(self):
        return str(self.__type)

    @property
    def id(self):
        return self._str

    @id.setter
    def id(self, _id):
        self._str = _id

    def __repr__(self):
        return self._str


class Real(Variable):
    def __init__(self, var_id):
        Variable.__init__(self, "real", var_id)


class RealVal(Constant):
    def __init__(self, value):
        Constant.__init__(self, "real", value)


class Int(Variable):
    def __init__(self, var_id):
        Variable.__init__(self, "int", var_id)


class IntVal(Constant):
    def __init__(self, value):
        Constant.__init__(self, "int", value)


class Bool(Variable, Formula):
    def __init__(self, var_id):
        Variable.__init__(self, "bool", var_id)
        self._range = False


class BoolVal(Constant, Formula):
    def __init__(self, value):
        Constant.__init__(self, "bool", value)
        Formula.__init__(self)
        self._range = False


universeInterval = Interval(True, RealVal("0.0"), False, RealVal('inf'))


class Add(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right)
        self._str = "(+ " + BinaryExpr.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class Sub(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right)
        self._str = "(- " + BinaryExpr.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class Mul(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right)
        self._str = "(* " + BinaryExpr.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class Div(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right)
        self._str = "(/ " + BinaryExpr.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class Neg(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child)
        self._str = "(- " + Unary.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class Sqrt(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child)
        self._str = "(sqrt (" + Unary.__repr__(self) + "))"

    def __repr__(self):
        return self._str


class Sin(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child)
        self._str = "(sin (" + Unary.__repr__(self) + "))"

    def __repr__(self):
        return self._str


class Cos(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child)
        self._str = "(cos (" + Unary.__repr__(self) + "))"

    def __repr__(self):
        return self._str


class Tan(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child)
        self._str = "(tan (" + Unary.__repr__(self) + "))"

    def __repr__(self):
        return self._str


class Arcsin(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child)
        self._str = "(arcsin (" + Unary.__repr__(self) + "))"

    def __repr__(self):
        return self._str


class Arccos(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child)
        self._str = "(arccos (" + Unary.__repr__(self) + "))"

    def __repr__(self):
        return self._str


class Arctan(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child)
        self._str = "(arctan (" + Unary.__repr__(self) + "))"

    def __repr__(self):
        return self._str


class Pow(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right)
        self._str = "(^ " + BinaryExpr.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class Dynamics:
    def __init__(self, vars: list, exps: list):
        self.vars = vars
        self.exps = exps
        self._str = None

    def __repr__(self):
        if self._str is None:
            repr_str = "["
            comma = ", "
            total_len = len(self.vars)
            index = 0
            for c in self.vars:
                if index == total_len - 1:
                    repr_str += str(c)
                else:
                    repr_str += (str(c) + comma)
                index += 1
            repr_str += "] = ["
            index = 0
            for c in self.exps:
                if index == total_len - 1:
                    repr_str += str(c)
                else:
                    repr_str += (str(c) + comma)
                index += 1
            repr_str += "]"
            self._str = repr_str
        return self._str


class Function(Dynamics):
    def __init__(self, vars, exps):
        Dynamics.__init__(self, vars, exps)
        self._str = "sol(" + Dynamics.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class Ode(Dynamics):
    def __init__(self, vars, exps):
        Dynamics.__init__(self, vars, exps)
        self._str = "ode(" + Dynamics.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class And(MultinaryFormula, NonLeaf):
    def __init__(self, children):
        NonLeaf.__init__(self, children)
        MultinaryFormula.__init__(self, children)
        self._str = "(and " + MultinaryFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class Or(MultinaryFormula, NonLeaf):
    def __init__(self, children):
        NonLeaf.__init__(self, children)
        MultinaryFormula.__init__(self, children)
        self._str = "(or " + MultinaryFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class Not(UnaryFormula, NonLeaf):
    def __init__(self, child):
        NonLeaf.__init__(self, [child])
        Formula.__init__(self)
        UnaryFormula.__init__(self, child)
        self._str = "(not " + UnaryFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class Gt(BinaryFormula, Leaf):
    def __init__(self, left, right):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right)
        self._str = "(> " + BinaryFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class Geq(BinaryFormula, Leaf):
    def __init__(self, left, right):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right)
        self._str = "(>= " + BinaryFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class Lt(BinaryFormula, Leaf):
    def __init__(self, left, right):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right)
        self._str = "(< " + BinaryFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class Leq(BinaryFormula, Leaf):
    def __init__(self, left, right):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right)
        self._str = "(<= " + BinaryFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class Eq(BinaryFormula, Leaf):
    def __init__(self, left, right):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right)
        self._str = "(= " + BinaryFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class Neq(BinaryFormula, Leaf):
    def __init__(self, left, right):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right)
        self._str = "(!= " + BinaryFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class Implies(BinaryFormula, NonLeaf):
    def __init__(self, left, right):
        NonLeaf.__init__(self, [left, right])
        BinaryFormula.__init__(self, left, right)
        self._str = "(implies " + BinaryFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str

    def __hash__(self):
        return hash(self._str)


class Integral(Formula, Leaf):
    def __init__(self, current_mode_number, end_vector: list, start_vector: list, dynamics: Dynamics):
        Leaf.__init__(self)
        Formula.__init__(self)
        self.current_mode_number = current_mode_number
        # list of variables
        self.end_vector = end_vector
        # list of variables
        self.start_vector = start_vector
        # list of dynamics
        self.dynamics = dynamics
        self._range = False
        self._str = "(integral " + str(self.current_mode_number) \
                    + " " + str(self.end_vector) + " " + str(self.start_vector) + " " + str(self.dynamics) + ")"

    def __hash__(self):
        return hash(self._str)

    def __repr__(self):
        return self._str


class Forall(Formula, Leaf):
    def __init__(self, current_mode_number, end_tau, start_tau, const, integral):
        Leaf.__init__(self)
        Formula.__init__(self)
        self.current_mode_number = current_mode_number
        self.end_tau = end_tau
        self.start_tau = start_tau
        self.const = const
        self.integral = integral
        self._range = False
        self._str = "(forall " + str(self.current_mode_number) + " . " + str(self.const) + ")"

    def __hash__(self):
        return hash(self._str)

    def __repr__(self):
        return self._str


# end of boolean_objects


class UnaryTemporalFormula(UnaryFormula, NonLeaf):
    def __init__(self, local_time, global_time, child):
        NonLeaf.__init__(self, [child])
        UnaryFormula.__init__(self, child)
        self.local_time = local_time
        self.global_time = global_time
        self._str = '_' + str(self.local_time) + '^' + str(self.global_time) + ' ' + str(self.child)

    def __repr__(self):
        return self._str


class GloballyFormula(UnaryTemporalFormula):
    def __init__(self, local_time, global_time, child):
        UnaryTemporalFormula.__init__(self, local_time, global_time, child)
        self._str = "([]" + UnaryTemporalFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class FinallyFormula(UnaryTemporalFormula):
    def __init__(self, local_time, global_time, child):
        UnaryTemporalFormula.__init__(self, local_time, global_time, child)
        self._str = "(<>" + UnaryTemporalFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class BinaryTemporalFormula(BinaryFormula, NonLeaf):
    def __init__(self, local_time, global_time, left, right):
        NonLeaf.__init__(self, [left, right])
        BinaryFormula.__init__(self, left, right)
        self.local_time = local_time
        self.global_time = global_time
        self._str = '_' + str(self.local_time) + '^' + str(self.global_time) + ' ' + str(self.right)

    def __repr__(self):
        return self._str


class UntilFormula(BinaryTemporalFormula):
    def __init__(self, local_time, global_time, left, right):
        BinaryTemporalFormula.__init__(self, local_time, global_time, left, right)
        self._str = "(" + repr(self.left) + " U" + BinaryTemporalFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str


class ReleaseFormula(BinaryTemporalFormula):
    def __init__(self, local_time, global_time, left, right):
        BinaryTemporalFormula.__init__(self, local_time, global_time, left, right)
        self._str = "(" + repr(self.left) + " R" + BinaryTemporalFormula.__repr__(self) + ")"

    def __repr__(self):
        return self._str


# wrapper class for goal reach
class Reach(Formula):
    def __init__(self, formula):
        self.formula = formula
