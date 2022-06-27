# start of base_objects

from ..tree.tree import Leaf, NonLeaf
from ..exception.exception import ElementNotFoundError


class Interval:
    def __init__(self, left_end, left, right_end, right):
        self.left_end = left_end
        self.left = left
        self.right_end = right_end
        self.right = right
        self._str = None

    def __hash__(self):
        return hash((hash(self.left_end), hash(self.left), hash(self.right_end), hash(self.right)))

    def __repr__(self):
        if self._str is None:
            self._str = ('[' if self.left_end else '(') + repr(self.left) + ',' + repr(self.right) + (
                ']' if self.right_end else ')')
        return self._str

    def __eq__(self, other):
        return isinstance(other,
                          Interval) and other.left_end == self.left_end and other.right_end == self.right_end and hash(
            other.left) == hash(self.left) and hash(other.right) == hash(self.right)


# immutable
class Unary:
    def __init__(self, child, hash_root: str, op_str: str):
        self.child = child
        self._op_str = op_str
        # self._str = "({} {})".format(op_str, self.child)
        self._hash = hash((hash_root, hash(self.child)))

    def __repr__(self):
        # return self._str
        return "({} {})".format(self._op_str, self.child)

    def __hash__(self):
        return self._hash


class Binary:
    def __init__(self, left, right, hash_root: str, op_str: str):
        self.left = left
        self.right = right
        self._op_str = op_str
        # self._str = "({} {} {})".format(op_str, self.left, self.right)
        self._hash = hash((hash_root, hash(self.left), hash(self.right)))

    def __repr__(self):
        # return self._str
        return "({} {} {})".format(self.left, self._op_str, self.right)

    def __hash__(self):
        return self._hash


class Multinary:
    def __init__(self, children, hash_root: str, op_str: str):
        self.children = children
        self._op_str = op_str
        tmp = set()
        for child in self.children:
            tmp.add(hash(child))
        self._hash = hash((hash_root, frozenset(tmp)))

    def at(self, i):
        if i < len(self.children):
            return self.children[i]
        else:
            raise ElementNotFoundError(self, "not in the list")

    def __repr__(self):
        # return self._str
        _str = ""
        comma = " "
        for i, c in enumerate(self.children):
            if i == len(self.children) - 1:
                _str += str(c)
            else:
                _str += (str(c) + comma)
        _str = "({} {})".format(self._op_str, _str)
        return _str

    def __hash__(self):
        return self._hash


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
    def __init__(self, child, hash_root: str, op_str: str):
        Expr.__init__(self)
        Unary.__init__(self, child, hash_root, op_str)

    def __hash__(self):
        return Unary.__hash__(self)


class BinaryExpr(Expr, Binary):
    def __init__(self, left, right, hash_root: str, op_str: str):
        Expr.__init__(self)
        Binary.__init__(self, left, right, hash_root, op_str)

    def __hash__(self):
        return Binary.__hash__(self)


class MultinaryExpr(Expr, Multinary):
    def __init__(self, children, hash_root: str, op_str: str):
        Expr.__init__(self)
        Multinary.__init__(self, children, hash_root, op_str)

    def __hash__(self):
        return Multinary.__hash__(self)


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
    def __init__(self, child, hash_root: str, op_str: str):
        Formula.__init__(self)
        Unary.__init__(self, child, hash_root, op_str)

    def __hash__(self):
        return Unary.__hash__(self)


class BinaryFormula(Formula, Binary):
    def __init__(self, left, right, hash_root: str, op_str: str):
        Formula.__init__(self)
        Binary.__init__(self, left, right, hash_root, op_str)

    def __hash__(self):
        return Binary.__hash__(self)


class MultinaryFormula(Formula, Multinary):
    def __init__(self, children, hash_root: str, op_str: str):
        Formula.__init__(self)
        Multinary.__init__(self, children, hash_root, op_str)

    def __hash__(self):
        return Multinary.__hash__(self)


class Constant(Leaf, Expr):
    def __init__(self, var_type, value):
        Leaf.__init__(self)
        Expr.__init__(self)
        self.__value = value
        self.__type = var_type
        self._str = str(self.value)

    def __hash__(self):
        return hash(self._str)

    def __eq__(self, other):
        return self.__hash__() == other.__hash__()

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

    def __eq__(self, other):
        return self.__hash__() == other.__hash__()

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


class BoolVal(Constant, Formula):
    def __init__(self, value):
        Constant.__init__(self, "bool", value)
        Formula.__init__(self)


universeInterval = Interval(True, RealVal("0.0"), False, RealVal('inf'))


class Add(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right, "add", "+")


class Sub(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right, "sub", "-")


class Mul(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right, "mul", "*")


class Div(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right, "div", "/")


class Neg(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child, "neg", "-")


class Sqrt(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child, "sqrt", "sqrt")


class Sin(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child, "sin", "sin")


class Cos(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child, "cos", "cos")


class Tan(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child, "tan", "tan")


class Arcsin(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child, "arcsin", "arcsin")


class Arccos(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child, "arccos", "arccos")


class Arctan(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child, "arctan", "arctan")


class Pow(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right, "pow", "^")


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
        MultinaryFormula.__init__(self, children, "and", "and")

    def __hash__(self):
        return MultinaryFormula.__hash__(self)


class Or(MultinaryFormula, NonLeaf):
    def __init__(self, children):
        NonLeaf.__init__(self, children)
        MultinaryFormula.__init__(self, children, "or", "or")

    def __hash__(self):
        return MultinaryFormula.__hash__(self)


class Not(UnaryFormula, NonLeaf):
    def __init__(self, child):
        NonLeaf.__init__(self, [child])
        Formula.__init__(self)
        UnaryFormula.__init__(self, child, "not", "not")

    def __hash__(self):
        return UnaryFormula.__hash__(self)


class Gt(BinaryFormula, Leaf):
    def __init__(self, left, right, is_range=False):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right, "gt", ">")
        self.is_range = is_range

    def __hash__(self):
        return BinaryFormula.__hash__(self)


class Geq(BinaryFormula, Leaf):
    def __init__(self, left, right, is_range=False):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right, "geq", ">=")
        self.is_range = is_range

    def __hash__(self):
        return BinaryFormula.__hash__(self)


class Lt(BinaryFormula, Leaf):
    def __init__(self, left, right, is_range=False):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right, "lt", "<")
        self.is_range = is_range

    def __hash__(self):
        return BinaryFormula.__hash__(self)


class Leq(BinaryFormula, Leaf):
    def __init__(self, left, right, is_range=False):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right, "leq", "<=")
        self.is_range = is_range

    def __hash__(self):
        return BinaryFormula.__hash__(self)


class TimeBoundConst(BinaryFormula, Leaf):
    def __init__(self, left, right):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right, "gt", ">=")

    def __hash__(self):
        return BinaryFormula.__hash__(self)


class Eq(BinaryFormula, Leaf):
    def __init__(self, left, right, is_range=False):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right, "eq", "=")
        self.is_range = is_range

    def __hash__(self):
        return BinaryFormula.__hash__(self)


class Neq(BinaryFormula, Leaf):
    def __init__(self, left, right):
        Leaf.__init__(self)
        BinaryFormula.__init__(self, left, right, "neq", "!=")

    def __hash__(self):
        return BinaryFormula.__hash__(self)


class Implies(BinaryFormula, NonLeaf):
    def __init__(self, left, right):
        NonLeaf.__init__(self, [left, right])
        BinaryFormula.__init__(self, left, right, "implies", "->")

    def __hash__(self):
        return BinaryFormula.__hash__(self)


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
        self._str = "(forall " + str(self.current_mode_number) + " . " + str(self.const) + ")"

    def __hash__(self):
        return hash(self._str)

    def __repr__(self):
        return self._str


# end of boolean_objects
## hashing

class UnaryTemporalFormula(UnaryFormula, NonLeaf):
    def __init__(self, local_time, global_time, child, hash_root: str, op_str: str):
        NonLeaf.__init__(self, [child])
        UnaryFormula.__init__(self, child, hash_root, op_str)
        self.local_time = local_time
        self.global_time = global_time
        # self._str = "({}_{}^{} {})".format(op_str, self.local_time, self.global_time, self.child)
        self._str = "({}{} {})".format(op_str, self.local_time, self.child)
        self._hash = hash((hash(self.local_time), hash(self.global_time), self._hash))

    def __hash__(self):
        return self._hash

    def __repr__(self):
        return self._str


class GloballyFormula(UnaryTemporalFormula):
    def __init__(self, local_time, global_time, child):
        UnaryTemporalFormula.__init__(self, local_time, global_time, child, "globally", "[]")


class GloballyT1Formula(UnaryTemporalFormula):
    def __init__(self, local_time, global_time, child):
        UnaryTemporalFormula.__init__(self, local_time, global_time, child, "globallyT1", "[1]")


class GloballyT2Formula(UnaryTemporalFormula):
    def __init__(self, local_time, global_time, child):
        UnaryTemporalFormula.__init__(self, local_time, global_time, child, "globallyT2", "[2]")


class FinallyFormula(UnaryTemporalFormula):
    def __init__(self, local_time, global_time, child):
        UnaryTemporalFormula.__init__(self, local_time, global_time, child, "finally", "<>")


class BinaryTemporalFormula(BinaryFormula, NonLeaf):
    def __init__(self, local_time, global_time, left, right, hash_root: str, op_str: str):
        NonLeaf.__init__(self, [left, right])
        BinaryFormula.__init__(self, left, right, hash_root, op_str)
        self.local_time = local_time
        self.global_time = global_time
        self._str = "({} {}{} {})".format(self.left, op_str, self.local_time, self.right)
        self._hash = hash((hash(self.local_time), hash(self.global_time), self._hash))

    def __repr__(self):
        return self._str

    def __hash__(self):
        return self._hash


class UntilFormula(BinaryTemporalFormula):
    def __init__(self, local_time, global_time, left, right):
        BinaryTemporalFormula.__init__(self, local_time, global_time, left, right, "until", "U")


class ReleaseFormula(BinaryTemporalFormula):
    def __init__(self, local_time, global_time, left, right):
        BinaryTemporalFormula.__init__(self, local_time, global_time, left, right, "release", "R")


# wrapper class for goal reach
class Reach(Formula):
    def __init__(self, formula):
        self.formula = formula
