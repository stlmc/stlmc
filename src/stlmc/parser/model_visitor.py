from pathlib import Path

from lark import Lark, Transformer
from lark.exceptions import VisitError

from ..constraints.constraints import *
from ..constraints.operations import get_vars, substitution
from ..exceptions import NotSupportedError
from ..objects.model import StlMC
from .syntax_error import parse_file


_PARSER = Lark.open(
    str(Path(__file__).with_name("grammars") / "model.lark"),
    parser="lalr", start="start", propagate_positions=True,
)

_SECTION_KEYWORDS = (
    "const", "bool", "int", "real", "mode", "inv", "flow", "jump",
    "init", "proposition", "goal",
)
_INITIAL_PREFIX = "__stlmc_initial__"


class _NameReference:
    def __init__(self, token):
        self.token = token
        self.name = str(token)


class _ModelTransformer(Transformer):
    def __init__(self, file_name):
        super().__init__()
        self.file_name = file_name
        self.next_str = "##$%^&$%^&##'"
        self.range_dict = {}
        self.constant_dict = {}
        self.variable_declare_dict = {}
        self.proposition_dict = {}
        self.raw_proposition_dict = {}
        self.goal_labels = {}
        self.temp_jump = None
        self.init_mode = None
        self.decl_ids = set()

    @staticmethod
    def _text(value):
        return str(value)

    def _declared_variable(self, token):
        name = self._text(token)
        if name in self.variable_declare_dict:
            return self.variable_declare_dict[name]
        for variable in self.range_dict:
            if variable.id == name:
                return variable
        for variable in self.constant_dict:
            if variable.id == name:
                return variable
        raise NotSupportedError(
            "{}:{}:{}: name {!r} is not declared".format(
                self.file_name, token.line, token.column, name
            )
        )

    def _resolve(self, value):
        if isinstance(value, _NameReference):
            return self._declared_variable(value.token)
        return value

    def typed_decl(self, children):
        type_name, token = self._text(children[0]).lower(), children[1]
        variable = {"bool": Bool, "int": Int, "real": Real}[type_name](
            self._text(token)
        )
        self.variable_declare_dict.setdefault(variable.id, variable)
        self.decl_ids.add(variable.id)

    def ranged_decl(self, children):
        var_range, token = children
        variable = Real(self._text(token))
        self.range_dict.setdefault(variable, var_range)
        self.decl_ids.add(variable.id)

    def const_decl(self, children):
        name, raw_value = self._text(children[0]), self._text(children[1])
        if raw_value.lower() in {"true", "false"}:
            variable = Bool(name)
            value = BoolVal(raw_value.title())
        else:
            try:
                float(raw_value)
            except ValueError as error:
                raise NotSupportedError("wrong value: {}".format(raw_value)) from error
            variable = Real(name)
            value = RealVal(raw_value)
        if variable in self.constant_dict:
            raise NotSupportedError("{} is already declared".format(variable))
        self.constant_dict[variable] = value
        self.decl_ids.add(name)

    def number_expression(self, children):
        return RealVal(self._text(children[0]))

    def time_expression(self, children):
        return Real("time")

    def initial_expression(self, children):
        token = children[0]
        name = self._text(token)
        if not any(variable.id == name for variable in self.range_dict):
            raise NotSupportedError(
                "{}:{}:{}: initial value {!r}(0) must refer to a declared "
                "continuous variable".format(
                    self.file_name, token.line, token.column, name
                )
            )
        return Real(_INITIAL_PREFIX + name)

    def variable_expression(self, children):
        token = children[0]
        try:
            return self._declared_variable(token)
        except NotSupportedError:
            return _NameReference(token)

    def binary_expression(self, children):
        left, operator, right = children
        left, right = self._resolve(left), self._resolve(right)
        operation = {"+": Add, "-": Sub, "*": Mul, "/": Div, "**": Pow}
        return operation[self._text(operator)](left, right)

    def unary_expression(self, children):
        operator, expression = self._text(children[0]), self._resolve(children[1])
        if operator == "+":
            return expression
        operation = {
            "sin": Sin, "cos": Cos, "tan": Tan, "sqrt": Sqrt,
            "arcsin": Arcsin, "arccos": Arccos, "arctan": Arctan,
            "-": Neg,
        }
        return operation[operator](expression)

    def true_condition(self, children):
        return BoolVal("True")

    def false_condition(self, children):
        return BoolVal("False")

    def bool_operator(self, children):
        return children[0]

    def expression_condition(self, children):
        value = children[0]
        if isinstance(value, _NameReference):
            name = value.name
            bool_variable = Bool(name)
            if bool_variable in self.proposition_dict:
                return bool_variable
        return self._resolve(value)

    def not_condition(self, children):
        return Not(children[-1])

    def multi_condition(self, children):
        operator = self._text(children[0]).lower()
        return {"and": And, "or": Or}[operator](children[1:])

    def compare_condition(self, children):
        left, operator, right = children
        left, right = self._resolve(left), self._resolve(right)
        if isinstance(left, Int) and left.id == "to":
            if not isinstance(right, RealVal):
                raise NotSupportedError("initial mode must be numeric")
            self.init_mode = int(right.value)
            return BoolVal("True")
        operation = {"<=": Leq, ">=": Geq, "<": Lt, ">": Gt,
                     "=": Eq, "!=": Neq}
        return operation[self._text(operator)](left, right)

    def variable_jump(self, children):
        return Bool(self._text(children[0])[:-1] + self.next_str)

    def true_value(self, children):
        return BoolVal("True")

    def false_value(self, children):
        return BoolVal("False")

    def not_jump(self, children):
        return Not(children[-1])

    def multi_jump(self, children):
        operator = self._text(children[0]).lower()
        return {"and": And, "or": Or}[operator](children[1:])

    def assign_jump(self, children):
        next_token, operator, expression = children
        name = self._text(next_token)[:-1]
        if name == "to":
            if not isinstance(expression, RealVal):
                raise NotSupportedError("jump mode must be numeric")
            self.temp_jump = int(expression.value)
            return BoolVal("True")
        variable = self._declared_variable(next_token.update(value=name))
        next_variable = {"bool": Bool, "int": Int, "real": Real}[
            variable.type
        ](name + self.next_str)
        operation = {"<=": Leq, ">=": Geq, "<": Lt, ">": Gt,
                     "=": Eq, "!=": Neq}
        return operation[self._text(operator)](next_variable, expression)

    def exact_range_tail(self, children):
        return "exact",

    def bounded_range_tail(self, children):
        return "bounded", self._text(children[0]), self._text(children[1])

    def bracket_range(self, children):
        lower, tail = float(children[0]), children[1]
        if tail[0] == "exact":
            return True, lower, lower, True
        return True, lower, float(tail[1]), tail[2] == "]"

    def open_range(self, children):
        lower, upper, right = map(self._text, children)
        return False, float(lower), float(upper), right == "]"

    def diff_eq(self, children):
        return "ode", Real(self._text(children[-2])), children[-1]

    def sol_eq(self, children):
        token, expression = children
        name = self._text(token)
        if not any(variable.id == name for variable in self.range_dict):
            raise NotSupportedError(
                "{}:{}:{}: solution function {!r}(t) must define a declared "
                "continuous variable".format(
                    self.file_name, token.line, token.column, name
                )
            )

        expression = self._resolve(expression)
        initial_substitution = {}
        for variable in get_vars(expression):
            if variable.id == "time" or variable in self.constant_dict:
                continue
            if variable.id.startswith(_INITIAL_PREFIX):
                initial_substitution[variable] = Real(
                    variable.id[len(_INITIAL_PREFIX):]
                )
                continue
            raise NotSupportedError(
                "{}:{}:{}: bare state variable {!r} is not allowed in a "
                "solution function; use {}(0) for its initial value".format(
                    self.file_name, token.line, token.column,
                    variable.id, variable.id,
                )
            )
        expression = substitution(expression, initial_substitution)
        return "function", Real(name), expression, token

    def mode_decl(self, children):
        return And(children)

    def inv_decl(self, children):
        return And(children)

    def flow_decl(self, children):
        kind = children[0][0]
        variables = [substitution(item[1], self.constant_dict) for item in children]
        expressions = [substitution(item[2], self.constant_dict) for item in children]
        if kind == "function":
            names = [variable.id for variable in variables]
            duplicates = sorted({name for name in names if names.count(name) > 1})
            token = children[0][3]
            if duplicates:
                raise NotSupportedError(
                    "{}:{}:{}: duplicate solution function for {}".format(
                        self.file_name, token.line, token.column,
                        ", ".join(repr(name) for name in duplicates),
                    )
                )
            expected = {variable.id for variable in self.range_dict}
            missing = sorted(expected.difference(names))
            if missing:
                raise NotSupportedError(
                    "{}:{}:{}: missing solution function for continuous "
                    "variable(s): {}".format(
                        self.file_name, token.line, token.column,
                        ", ".join(missing),
                    )
                )
        return kind, variables, expressions

    def jump_rule(self, children):
        condition, jump = children[0], children[-1]
        jump_id = self.temp_jump
        self.temp_jump = None
        return condition, jump, jump_id

    def jump_decl(self, children):
        jumps, jump_ids = {}, {}
        for condition, jump, jump_id in children:
            jumps[condition] = jump
            if jump_id is not None:
                jump_ids[condition] = jump_id
        return jumps, jump_ids

    def mode_module(self, children):
        mode, invariant, flow, jumps = children
        kind, variables, expressions = flow
        dynamics = Ode(variables, expressions) if kind == "ode" else Function(
            variables, expressions
        )
        return {"mode": mode, "inv": invariant, "flow": dynamics,
                "jump": jumps[0], "jp_d": jumps[1]}

    def init_decl(self, children):
        return "init", And(children)

    def exact_interval(self, children):
        value = RealVal(self._text(children[0]))
        return Interval(True, value, True, value)

    def bounded_interval(self, children):
        left, lower, upper, right = map(self._text, children)
        return Interval(left == "[", RealVal(lower), right == "]", RealVal(upper))

    def true_formula(self, children):
        return BoolVal("True")

    def false_formula(self, children):
        return BoolVal("False")

    def expression_formula(self, children):
        expression = children[0]
        if isinstance(expression, _NameReference):
            return Bool(expression.name)
        if isinstance(expression, Variable):
            return Bool(expression.id)
        raise NotSupportedError("a standalone formula must be a proposition")

    def direct_condition(self, children):
        left, operator, right = children
        left, right = self._resolve(left), self._resolve(right)
        operation = {"<=": Leq, ">=": Geq, "<": Lt, ">": Gt,
                     "=": Eq, "!=": Neq}
        proposition = Bool("newPropDecl_{}".format(len(self.proposition_dict)))
        self.proposition_dict[proposition] = operation[self._text(operator)](left, right)
        return proposition

    def not_formula(self, children):
        return Not(children[-1])

    def binary_formula(self, children):
        left, operator, right = children
        return {"and": And, "or": Or}[self._text(operator).lower()]([left, right])

    def implies_formula(self, children):
        return Implies(children[0], children[1])

    def multi_formula(self, children):
        operator = self._text(children[0]).lower()
        return {"and": And, "or": Or}[operator](children[1:])

    def unary_temporal_formula(self, children):
        operator, interval, child = self._text(children[0]), children[1], children[2]
        return {"[]": GloballyFormula, "<>": FinallyFormula}[operator](
            interval, universeInterval, child
        )

    def temporal_formula(self, children):
        left, operator, interval, right = children
        return {"U": UntilFormula, "R": ReleaseFormula}[self._text(operator)](
            interval, universeInterval, left, right
        )

    def prop(self, children):
        return Bool(self._text(children[0])), children[1]

    def props(self, children):
        self.raw_proposition_dict = dict(children)
        self.proposition_dict = self.raw_proposition_dict.copy()

    def labeled_goal(self, children):
        return children[1], self._text(children[0]), False

    def unlabeled_goal(self, children):
        return children[0], None, False

    def reach_goal(self, children):
        return children[0], None, True

    def goal_decl(self, children):
        labeled, unlabeled, reach = [], [], []
        for goal, label, is_reach in children:
            if label is not None:
                labeled.append(goal)
                self.goal_labels[goal] = label
            elif is_reach:
                reach.append(goal)
            else:
                unlabeled.append(goal)
        return "goals", (labeled, unlabeled, reach)

    def start(self, children):
        modules = [child for child in children if isinstance(child, dict)]
        init = next(child[1] for child in children
                    if isinstance(child, tuple) and child[0] == "init")
        goals = next(child[1] for child in children
                     if isinstance(child, tuple) and child[0] == "goals")
        model = StlMC(
            self.variable_declare_dict, self.range_dict, self.constant_dict,
            self.raw_proposition_dict, modules, init, self.init_mode,
        )
        return model, self.proposition_dict, goals, self.goal_labels


class ModelVisitor:
    def get_parse_tree(self, file_name: str):
        try:
            tree = parse_file(
                _PARSER, file_name, description="model", keywords=_SECTION_KEYWORDS
            )
            return _ModelTransformer(file_name).transform(tree)
        except VisitError as error:
            raise error.orig_exc from error
