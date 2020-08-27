# start of base_objects
from stlmcPy.exception.exception import NotFoundElementError
from stlmcPy.tree.tree import Leaf, NonLeaf


class Interval:
    def __init__(self, left_end, left, right_end, right):
        self.left_end = left_end
        self.left = left
        self.right_end = right_end
        self.right = right

    def __hash__(self):
        return hash(id(self))

    def __repr__(self):
        return ('[' if self.left_end else '(') + repr(self.left) + ',' + repr(self.right) + (
            ']' if self.right_end else ')')

    def __eq__(self, other):
        return isinstance(other, Interval) and other.left_end == self.left_end and other.right_end == self.right_end and other.left == self.left and other.right == self.right

universeInterval = Interval(True, 0.0, False, float('inf'))


class Unary(NonLeaf):
    def __init__(self, child):
        NonLeaf.__init__(self, [child])
        self.child = child

    def get_child(self):
        return self.child

    def __repr__(self):
        return str(self.child)


class Binary(NonLeaf):
    def __init__(self, left, right):
        NonLeaf.__init__(self, [left, right])
        self.left = left
        self.right = right

    def get_left(self):
        return self.left

    def get_right(self):
        return self.right

    def __repr__(self):
        return str(self.left) + " " + str(self.right)


class Multinary(NonLeaf):
    def __init__(self, children):
        NonLeaf.__init__(self, children)
        self.children = children

    def at(self, i):
        if i < len(self.children):
            return self.children[i]
        else:
            raise NotFoundElementError(self, "not in the list")

    def __repr__(self):
        repr_str = ""
        comma = " "
        last_key = None
        if len(self.children) > 0:
            last_key = self.children[-1]
        for c in self.children:
            if str(c) == str(last_key):
                repr_str += str(c)
            else:
                repr_str += (str(c) + comma)
        return repr_str


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

    def __repr__(self):
        return Unary.__repr__(self)

    def __hash__(self):
        return hash(str(self))


class BinaryExpr(Expr, Binary):
    def __init__(self, left, right):
        Expr.__init__(self)
        Binary.__init__(self, left, right)

    def __repr__(self):
        return Binary.__repr__(self)

    def __hash__(self):
        return hash(str(self))


class MultinaryExpr(Expr, Multinary):
    def __init__(self, children):
        Expr.__init__(self)
        Multinary.__init__(self, children)

    def __repr__(self):
        return Multinary.__repr__(self)

    def __hash__(self):
        return hash(str(self))


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

    def __repr__(self):
        return Unary.__repr__(self)

    def __hash__(self):
        return hash(str(self))


class BinaryFormula(Formula, Binary):
    def __init__(self, left, right):
        Formula.__init__(self)
        Binary.__init__(self, left, right)

    def __repr__(self):
        return Binary.__repr__(self)

    def __hash__(self):
        return hash(str(self))


class MultinaryFormula(Formula, Multinary):
    def __init__(self, children):
        Formula.__init__(self)
        Multinary.__init__(self, children)

    def __repr__(self):
        return Multinary.__repr__(self)

    def __hash__(self):
        return hash(str(self))


class Constant(Leaf, Expr):
    def __init__(self, var_type, value):
        Leaf.__init__(self)
        Expr.__init__(self)
        self.__value = value
        self.__type = var_type

    def __hash__(self):
        return hash(str(self.__value))

    @property
    def value(self):
        return self.__value

    @property
    def type(self):
        return self.__type

    def __repr__(self):
        return str(self.value)


class Variable(Leaf, Expr):
    def __init__(self, var_type: str, var_id: str):
        Leaf.__init__(self)
        Expr.__init__(self)
        self.__id = var_id
        self.__type = var_type

    def __hash__(self):
        return hash(str(self.__id))

    @property
    def type(self):
        return str(self.__type)

    @property
    def id(self):
        return str(self.__id)

    def __repr__(self):
        return str(self.__id)


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


class Add(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right)

    def __repr__(self):
        return "(+ " + BinaryExpr.__repr__(self) + ")"


class Sub(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right)

    def __repr__(self):
        return "(- " + BinaryExpr.__repr__(self) + ")"


class Mul(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right)

    def __repr__(self):
        return "(* " + BinaryExpr.__repr__(self) + ")"


class Div(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right)

    def __repr__(self):
        return "(/ " + BinaryExpr.__repr__(self) + ")"


class Neg(UnaryExpr):
    def __init__(self, child):
        UnaryExpr.__init__(self, child)

    def __repr__(self):
        return "(- " + Unary.__repr__(self) + ")"


class Pow(BinaryExpr):
    def __init__(self, left, right):
        BinaryExpr.__init__(self, left, right)

    def __repr__(self):
        return "(^ " + BinaryExpr.__repr__(self) + ")"


class Dynamics:
    def __init__(self, vars: list, exps: list):
        self.vars = vars
        self.exps = exps

    def __repr__(self):
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
        return repr_str


class Function(Dynamics):
    def __init__(self, vars, exps):
        Dynamics.__init__(self, vars, exps)

    def __repr__(self):
        return "sol(" + Dynamics.__repr__(self) + ")"


class Ode(Dynamics):
    def __init__(self, vars, exps):
        Dynamics.__init__(self, vars, exps)

    def __repr__(self):
        return "ode(" + Dynamics.__repr__(self) + ")"


class And(MultinaryFormula):
    def __init__(self, children):
        MultinaryFormula.__init__(self, children)

    def __repr__(self):
        return "(and " + MultinaryFormula.__repr__(self) + ")"


class Or(MultinaryFormula):
    def __init__(self, children):
        MultinaryFormula.__init__(self, children)

    def __repr__(self):
        return "(or " + MultinaryFormula.__repr__(self) + ")"


class Not(UnaryFormula):
    def __init__(self, child):
        Formula.__init__(self)
        UnaryFormula.__init__(self, child)

    def __repr__(self):
        return "(not " + UnaryFormula.__repr__(self) + ")"

    def __hash__(self):
        return hash(str(self))


class Gt(BinaryFormula):
    def __init__(self, left, right):
        BinaryFormula.__init__(self, left, right)

    def __repr__(self):
        return "(> " + BinaryFormula.__repr__(self) + ")"

    def __hash__(self):
        return hash(str(self))



class Geq(BinaryFormula):
    def __init__(self, left, right):
        BinaryFormula.__init__(self, left, right)

    def __repr__(self):
        return "(>= " + BinaryFormula.__repr__(self) + ")"

    def __hash__(self):
        return hash(str(self))


class Lt(BinaryFormula):
    def __init__(self, left, right):
        BinaryFormula.__init__(self, left, right)

    def __repr__(self):
        return "(< " + BinaryFormula.__repr__(self) + ")"

    def __hash__(self):
        return hash(str(self))


class Leq(BinaryFormula):
    def __init__(self, left, right):
        BinaryFormula.__init__(self, left, right)

    def __repr__(self):
        return "(<= " + BinaryFormula.__repr__(self) + ")"

    def __hash__(self):
        return hash(str(self))


class Eq(BinaryFormula):
    def __init__(self, left, right):
        BinaryFormula.__init__(self, left, right)

    def __repr__(self):
        return "(= " + BinaryFormula.__repr__(self) + ")"

    def __hash__(self):
        return hash(str(self))


class Neq(BinaryFormula):
    def __init__(self, left, right):
        BinaryFormula.__init__(self, left, right)

    def __repr__(self):
        return "(!= " + BinaryFormula.__repr__(self) + ")"

    def __hash__(self):
        return hash(str(self))


class Implies(BinaryFormula):
    def __init__(self, left, right):
        BinaryFormula.__init__(self, left, right)

    def __repr__(self):
        return "(implies " + BinaryFormula.__repr__(self) + ")"

    def __hash__(self):
        return hash(str(self))


class Integral(Formula):
    def __init__(self, current_mode_number, end_vector: list, start_vector: list, dynamics: Dynamics):
        Formula.__init__(self)
        self.current_mode_number = current_mode_number
        # list of variables
        self.end_vector = end_vector
        # list of variables
        self.start_vector = start_vector
        # list of dynamics
        self.dynamics = dynamics

    def __hash__(self):
        return hash(str(self))

    def __repr__(self):
        return "(integral " + str(self.current_mode_number) \
               + " " + str(self.end_vector) + " " + str(self.start_vector) + " " + str(self.dynamics) + ")"


class Forall(Formula):
    def __init__(self, current_mode_number, end_tau, start_tau, const, integral):
        Formula.__init__(self)
        self.current_mode_number = current_mode_number
        self.end_tau = end_tau
        self.start_tau = start_tau
        self.const = const
        self.integral = integral

    def __hash__(self):
        return hash(str(self))

    def __repr__(self):
        return "(forall " + str(self.current_mode_number) + " . " + str(self.const) + ")"


# end of boolean_objects


class UnaryTemporalFormula(UnaryFormula):
    def __init__(self, local_time, global_time, child):
        UnaryFormula.__init__(self, child)
        self.local_time = local_time
        self.global_time = global_time

    def __repr__(self):
        return '_' + str(self.local_time) + '^' + str(self.global_time) + ' ' + str(self.child)


class GloballyFormula(UnaryTemporalFormula):
    def __init__(self, local_time, global_time, child):
        UnaryTemporalFormula.__init__(self, local_time, global_time, child)

    def __repr__(self):
        return "([]" + UnaryTemporalFormula.__repr__(self) + ")"


class FinallyFormula(UnaryTemporalFormula):
    def __init__(self, local_time, global_time, child):
        UnaryTemporalFormula.__init__(self, local_time, global_time, child)

    def __repr__(self):
        return "(<>" + UnaryTemporalFormula.__repr__(self) + ")"


class BinaryTemporalFormula(BinaryFormula):
    def __init__(self, local_time, global_time, left, right):
        BinaryFormula.__init__(self, left, right)
        self.local_time = local_time
        self.global_time = global_time

    def __repr__(self):
        return '_' + str(self.local_time) + '^' + str(self.global_time) + ' ' + str(self.right)


class UntilFormula(BinaryTemporalFormula):
    def __init__(self, local_time, global_time, left, right):
        BinaryTemporalFormula.__init__(self, local_time, global_time, left, right)

    def __repr__(self):
        return "(" + repr(self.left) + " U" + BinaryTemporalFormula.__repr__(self) + ")"


class ReleaseFormula(BinaryTemporalFormula):
    def __init__(self, local_time, global_time, left, right):
        BinaryTemporalFormula.__init__(self, local_time, global_time, left, right)

    def __repr__(self):
        return "(" + repr(self.left) + " R" + BinaryTemporalFormula.__repr__(self) + ")"


# wrapper class for goal reach
class Reach(Formula):
    def __init__(self, formula):
        self.formula = formula
