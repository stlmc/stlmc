"""Bounded gzip/JSON artifacts with an explicit, non-executable AST schema.

No Python object/module names are resolved from input. Legacy pickle files are
unsupported; regenerate artifacts with the current STLmc version.
"""

import gzip
import json
import math
import os
from pathlib import Path
import re
import tempfile
import zlib

from ..constraints import constraints as c
from ..version_info import package_version, source_commit
from ..visualize.numbers import parse_number

FORMAT = "stlmc-artifact"
SCHEMA_VERSION = 1
MAX_UNCOMPRESSED_BYTES = 64 * 1024 * 1024
MAX_DEPTH = 128
MAX_NODES = 1000000
MAX_STRING_LENGTH = 65536
_ID = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_INTERNAL_ID = re.compile(r"[A-Za-z_][A-Za-z0-9_@^]*")
_LEGACY_BOOL_ID = re.compile(r"(?:rho|chi|parU|parEndrise|parEndfall)\^\{[0-9]+,[0-9]+\}_[0-9a-fA-F]{1,128}")
_JUMP_SUFFIX = "##$%^&$%^&##'"


class ArtifactFormatError(ValueError):
    """An artifact is malformed, unsupported, or exceeds a safety limit."""


_VARIABLES = {kind.__name__: kind for kind in (c.Real, c.Int, c.Bool)}
_CONSTANTS = {kind.__name__: kind for kind in (c.RealVal, c.IntVal, c.BoolVal)}
_UNARY = {kind.__name__: kind for kind in
          (c.Neg, c.Sqrt, c.Sin, c.Cos, c.Tan, c.Arcsin, c.Arccos, c.Arctan, c.Not)}
_BINARY = {kind.__name__: kind for kind in
           (c.Add, c.Sub, c.Mul, c.Div, c.Pow, c.Gt, c.Geq, c.Lt, c.Leq,
            c.Eq, c.Neq, c.Implies, c.TimeBoundConst)}
_RANGE = {c.Gt, c.Geq, c.Lt, c.Leq, c.Eq}
_MULTI = {kind.__name__: kind for kind in (c.And, c.Or)}
_TEMPORAL_UNARY = {kind.__name__: kind for kind in
                  (c.GloballyFormula, c.GloballyT1Formula, c.GloballyT2Formula, c.FinallyFormula)}
_TEMPORAL_BINARY = {kind.__name__: kind for kind in (c.UntilFormula, c.ReleaseFormula)}
_DYNAMICS = {kind.__name__: kind for kind in (c.Dynamics, c.Ode, c.Function)}


def _fail(message):
    raise ArtifactFormatError(message)


def _identifier(value, boolean=False):
    if not isinstance(value, str) or not value or len(value) > 4096:
        _fail("invalid artifact identifier")
    base = value[:-len(_JUMP_SUFFIX)] if value.endswith(_JUMP_SUFFIX) else value
    if boolean and base.endswith("...") and _LEGACY_BOOL_ID.fullmatch(base[:-3]):
        _fail("legacy artifact contains a truncated symbol identifier; regenerate with current STLmc")
    if not (_INTERNAL_ID.fullmatch(base) or (boolean and _LEGACY_BOOL_ID.fullmatch(base))):
        _fail("invalid artifact identifier")
    return value


def _number(value, integer=False):
    if type(value) not in (str, int, float):
        _fail("invalid numeric constant")
    if isinstance(value, int) and value.bit_length() > 16384:
        _fail("numeric constant exceeds supported limit")
    try:
        number = parse_number(value)
    except (ValueError, OverflowError, TypeError) as error:
        raise ArtifactFormatError("invalid numeric constant: " + str(error)) from error
    if integer and (isinstance(number, float) or number.denominator != 1):
        _fail("IntVal must be a finite integer")
    return number


def _fields(node, names):
    if set(node) != {"tag", *names}:
        _fail("invalid fields for artifact node " + str(node.get("tag")))


def _constraint(value):
    if not isinstance(value, c.Constraint):
        _fail("AST operand must be a typed constraint")


class _Budget:
    def __init__(self):
        self.nodes = 0

    def visit(self, depth):
        self.nodes += 1
        if depth > MAX_DEPTH:
            _fail("artifact depth limit exceeded")
        if self.nodes > MAX_NODES:
            _fail("artifact node count limit exceeded")


class _Encoder(_Budget):
    def __init__(self):
        super().__init__()
        self.active = set()

    def encode(self, value, depth=0):
        self.visit(depth)
        if value is None or type(value) in (bool, str, int, float):
            if isinstance(value, str) and len(value) > MAX_STRING_LENGTH:
                _fail("artifact string limit exceeded")
            if type(value) in (int, float):
                _number(value)
                if isinstance(value, float) and not math.isfinite(value):
                    _fail("non-finite JSON primitive")
            return value
        identity = id(value)
        if identity in self.active:
            _fail("cyclic artifact data")
        self.active.add(identity)
        try:
            kind = type(value)
            child = lambda item: self.encode(item, depth + 1)
            if kind in (list, tuple, set, frozenset):
                return {"tag": kind.__name__, "items": [child(item) for item in value]}
            if kind is dict:
                return {"tag": "dict", "items": [[child(key), child(item)] for key, item in value.items()]}
            from ..solver.dreal import DrealInterval
            if kind is DrealInterval:
                _number(value.lower)
                _number(value.upper)
                _number(value.value)
                return {"tag": "DrealInterval", "lower": child(value.lower),
                        "upper": child(value.upper), "value": child(value.value)}
            tag = kind.__name__
            if kind in _VARIABLES.values():
                return {"tag": tag, "id": _identifier(value.id, kind is c.Bool)}
            if kind is c.Variable:
                return {"tag": "Variable", "type": value.type, "id": _identifier(value.id, value.type == "bool")}
            if kind in _CONSTANTS.values() or kind is c.Constant:
                if value.type == "bool":
                    if value.value not in ("True", "False"):
                        _fail("invalid Boolean constant")
                else:
                    _number(value.value, value.type == "int")
                result = {"tag": tag, "value": child(value.value)}
                if kind is c.Constant:
                    result["type"] = value.type
                return result
            if kind is c.Interval:
                return {"tag": tag, **{name: child(getattr(value, name)) for name in
                                      ("left_end", "left", "right_end", "right")}}
            if kind in _UNARY.values():
                names = ("child",)
            elif kind in _BINARY.values():
                names = ("left", "right", "is_range") if kind in _RANGE else ("left", "right")
            elif kind in _MULTI.values():
                names = ("children",)
            elif kind in _TEMPORAL_UNARY.values():
                names = ("local_time", "global_time", "child")
            elif kind in _TEMPORAL_BINARY.values():
                names = ("local_time", "global_time", "left", "right")
            elif kind in _DYNAMICS.values():
                names = ("vars", "exps")
            elif kind is c.Integral:
                names = ("current_mode_number", "end_vector", "start_vector", "dynamics")
            elif kind is c.Forall:
                names = ("current_mode_number", "end_tau", "start_tau", "const", "integral")
            elif kind is c.Reach:
                names = ("formula",)
            else:
                _fail("unsupported artifact type: " + kind.__name__)
            return {"tag": tag, **{name: child(getattr(value, name)) for name in names}}
        finally:
            self.active.remove(identity)


class _Decoder(_Budget):
    def decode(self, node, depth=0):
        self.visit(depth)
        if node is None or type(node) in (bool, str, int, float):
            if isinstance(node, str) and len(node) > MAX_STRING_LENGTH:
                _fail("artifact string limit exceeded")
            if type(node) in (int, float):
                _number(node)
                if isinstance(node, float) and not math.isfinite(node):
                    _fail("non-finite JSON primitive")
            return node
        if type(node) is not dict or not isinstance(node.get("tag"), str):
            _fail("expected a tagged artifact node")
        tag = node["tag"]
        child = lambda item: self.decode(item, depth + 1)
        def arguments(names):
            _fields(node, names)
            return [child(node[name]) for name in names]
        if tag in ("list", "tuple", "set", "frozenset", "dict"):
            _fields(node, ("items",))
            if type(node["items"]) is not list:
                _fail("artifact container items must be a list")
            if tag == "dict":
                result = {}
                for pair in node["items"]:
                    if type(pair) is not list or len(pair) != 2:
                        _fail("invalid artifact dictionary pair")
                    key, value = map(child, pair)
                    try:
                        if key in result:
                            _fail("duplicate artifact dictionary key")
                        result[key] = value
                    except TypeError as error:
                        raise ArtifactFormatError("unhashable artifact dictionary key") from error
                return result
            values = [child(item) for item in node["items"]]
            try:
                return {"list": list, "tuple": tuple, "set": set, "frozenset": frozenset}[tag](values)
            except TypeError as error:
                raise ArtifactFormatError("unhashable artifact set entry") from error
        if tag in _VARIABLES or tag == "Variable":
            _fields(node, ("id", "type") if tag == "Variable" else ("id",))
            name = _identifier(node["id"], tag == "Bool" or (tag == "Variable" and node["type"] == "bool"))
            if tag == "Variable":
                if node["type"] not in ("real", "int", "bool"):
                    _fail("invalid variable type")
                return c.Variable(node["type"], name)
            return _VARIABLES[tag](name)
        if tag in _CONSTANTS or tag == "Constant":
            args = arguments(("value", "type") if tag == "Constant" else ("value",))
            value = args[0]
            variable_type = args[1] if tag == "Constant" else {"RealVal": "real", "IntVal": "int", "BoolVal": "bool"}[tag]
            if variable_type not in ("real", "int", "bool"):
                _fail("invalid constant type")
            if variable_type == "bool":
                if type(value) is not str or value not in ("True", "False"):
                    _fail("invalid Boolean constant")
            else:
                _number(value, variable_type == "int")
            return c.Constant(variable_type, value) if tag == "Constant" else _CONSTANTS[tag](value)
        if tag == "DrealInterval":
            lower, upper, value = arguments(("lower", "upper", "value"))
            lo, hi = _number(lower), _number(upper)
            _number(value)
            # Stored value is an approximate representative, not an exact
            # interval certificate: float rounding may put it outside a tiny box.
            if lo > hi:
                _fail("invalid dReal interval bounds")
            from ..solver.dreal import DrealInterval
            interval = DrealInterval(lower, upper)
            c.Constant.__init__(interval, "real", value)
            return interval
        if tag == "Interval":
            left_end, left, right_end, right = arguments(("left_end", "left", "right_end", "right"))
            if type(left_end) is not bool or type(right_end) is not bool:
                _fail("interval endpoints must be Boolean")
            _constraint(left)
            _constraint(right)
            return c.Interval(left_end, left, right_end, right)
        if tag in _UNARY:
            args = arguments(("child",))
            _constraint(args[0])
            return _UNARY[tag](*args)
        if tag in _BINARY:
            kind = _BINARY[tag]
            args = arguments(("left", "right", "is_range") if kind in _RANGE else ("left", "right"))
            for value in args[:2]:
                _constraint(value)
            if kind in _RANGE and type(args[2]) is not bool:
                _fail("is_range must be Boolean")
            return kind(*args)
        if tag in _MULTI:
            args = arguments(("children",))
            if type(args[0]) not in (list, tuple):
                _fail("AST children must be a sequence")
            for value in args[0]:
                _constraint(value)
            return _MULTI[tag](*args)
        if tag in _TEMPORAL_UNARY or tag in _TEMPORAL_BINARY:
            unary = tag in _TEMPORAL_UNARY
            args = arguments(("local_time", "global_time", "child") if unary else ("local_time", "global_time", "left", "right"))
            if not all(type(value) is c.Interval for value in args[:2]):
                _fail("temporal bounds must be intervals")
            for value in args[2:]:
                _constraint(value)
            return (_TEMPORAL_UNARY if unary else _TEMPORAL_BINARY)[tag](*args)
        if tag in _DYNAMICS:
            variables, expressions = arguments(("vars", "exps"))
            if type(variables) not in (list, tuple) or type(expressions) not in (list, tuple) or len(variables) != len(expressions):
                _fail("invalid dynamics vectors")
            for variable in variables:
                if type(variable) not in (c.Real, c.Int) or not _ID.fullmatch(variable.id):
                    _fail("dynamics variables must be ordinary numeric identifiers")
            for expression in expressions:
                if not isinstance(expression, c.Expr) or isinstance(expression, c.Formula):
                    _fail("dynamics expressions must be numeric AST expressions")
            return _DYNAMICS[tag](variables, expressions)
        if tag == "Integral":
            mode, end, start, dynamics = arguments(("current_mode_number", "end_vector", "start_vector", "dynamics"))
            if type(mode) is not int or mode < 0 or type(end) not in (list, tuple) or type(start) not in (list, tuple) or len(end) != len(start) or not isinstance(dynamics, c.Dynamics):
                _fail("invalid integral fields")
            if not all(isinstance(value, c.Expr) for value in list(end) + list(start)):
                _fail("integral vectors must be numeric AST expressions")
            return c.Integral(mode, end, start, dynamics)
        if tag == "Forall":
            args = arguments(("current_mode_number", "end_tau", "start_tau", "const", "integral"))
            if type(args[0]) is not int or args[0] < 0 or type(args[4]) is not c.Integral:
                _fail("invalid forall fields")
            for value in args[1:4]:
                _constraint(value)
            return c.Forall(*args)
        if tag == "Reach":
            args = arguments(("formula",))
            _constraint(args[0])
            return c.Reach(*args)
        _fail("unknown artifact node tag: " + tag)


def _json_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            _fail("duplicate JSON field")
        result[key] = value
    return result


def _json_int(text):
    if len(text) > 4096:
        _fail("JSON integer length limit exceeded")
    return int(text)


def _json_float(text):
    if len(text) > 4096:
        _fail("JSON float length limit exceeded")
    _number(text)
    value = float(text)
    if not math.isfinite(value):
        _fail("non-finite JSON number")
    return value


def _check_document_budget(document):
    budget = _Budget()
    pending = [(document, 0)]
    while pending:
        node, depth = pending.pop()
        budget.visit(depth)
        if isinstance(node, str) and len(node) > MAX_STRING_LENGTH:
            _fail("artifact string limit exceeded")
        if type(node) is dict:
            pending.extend((value, depth + 1) for value in node.values())
        elif type(node) is list:
            pending.extend((value, depth + 1) for value in node)


def _validate_payload(data):
    if type(data) is not tuple or len(data) != 11:
        _fail("schema 1 requires the eleven-field artifact tuple")
    assignment, modules, mode_vars, propositions, ranges, definitions, goal, label, threshold, initial, constants = data
    if type(assignment) is not dict or not all(isinstance(key, c.Variable) and isinstance(value, c.Constant)
                                               for key, value in assignment.items()):
        _fail("artifact assignment must map variables to typed constants")
    if type(modules) is not list or not all(type(module) is dict for module in modules):
        _fail("artifact modules must be a list of dictionaries")
    for module in modules:
        if not {"mode", "inv", "flow", "jump"}.issubset(module) or not all(type(key) is str for key in module):
            _fail("invalid artifact module fields")
        _constraint(module["mode"])
        _constraint(module["inv"])
        if not isinstance(module["flow"], c.Dynamics) or type(module["jump"]) is not dict:
            _fail("invalid artifact module dynamics or jumps")
    if not all(type(value) is dict for value in (mode_vars, propositions, ranges, definitions)):
        _fail("artifact model/proposition mappings must be dictionaries")
    _constraint(goal)
    if type(label) is not str or len(label) > MAX_STRING_LENGTH:
        _fail("artifact goal label must be a string")
    try:
        finite_threshold = type(threshold) in (int, float) and math.isfinite(threshold)
    except OverflowError:
        finite_threshold = False
    if not finite_threshold:
        _fail("artifact threshold must be a finite number")
    if initial is not None:
        _constraint(initial)
    if constants is not None and type(constants) is not dict:
        _fail("artifact constants must be a dictionary or null")


def _preflight_json_depth(raw):
    # json.loads is recursive even when our AST decoder is bounded. Scan before
    # calling it, including when an embedding application raised recursionlimit.
    depth, in_string, escaped = 0, False, False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == 92:
                escaped = True
            elif byte == 34:
                in_string = False
        elif byte == 34:
            in_string = True
        elif byte in (91, 123):
            depth += 1
            if depth > MAX_DEPTH:
                _fail("artifact JSON depth limit exceeded")
        elif byte in (93, 125):
            depth -= 1
            if depth < 0:
                _fail("invalid artifact JSON nesting")


def dump_artifact(path, data, metadata=None):
    """Atomically write a schema-1 gzip JSON artifact (never pickle)."""
    _validate_payload(data)
    try:
        encoded = _Encoder().encode(data)
        # The decoder also checks constructor-specific field types on writes.
        _Decoder().decode(encoded)
        document = {"format": FORMAT, "schema_version": SCHEMA_VERSION,
                    "producer": {"version": package_version(), "commit": source_commit()},
                    "metadata": {} if metadata is None else metadata, "data": encoded}
        if type(document["metadata"]) is not dict:
            _fail("artifact metadata must be an object")
        _check_document_budget(document)
        raw = json.dumps(document, ensure_ascii=True, allow_nan=False, separators=(",", ":")).encode("utf-8")
        if len(raw) > MAX_UNCOMPRESSED_BYTES:
            _fail("artifact uncompressed size limit exceeded")
    except (TypeError, OverflowError, RecursionError) as error:
        raise ArtifactFormatError("invalid artifact data: " + str(error)) from error
    destination = Path(path)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(prefix=".stlmc-artifact-", dir=str(destination.parent), delete=False) as output:
            temporary = Path(output.name)
            with gzip.GzipFile(filename="", fileobj=output, mode="wb", mtime=0) as compressed:
                compressed.write(raw)
        os.replace(str(temporary), str(destination))
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()


def load_artifact(path):
    """Read bounded gzip JSON data; reject pickle and unknown schemas/types."""
    try:
        with open(path, "rb") as source:
            if source.read(2) != b"\x1f\x8b":
                _fail("outdated or unsupported artifact format (including legacy pickle); rerun model checking with the current STLmc version to regenerate this file")
            source.seek(0)
            with gzip.GzipFile(fileobj=source, mode="rb") as compressed:
                raw = compressed.read(MAX_UNCOMPRESSED_BYTES + 1)
        if len(raw) > MAX_UNCOMPRESSED_BYTES:
            _fail("artifact uncompressed size limit exceeded")
        _preflight_json_depth(raw)
        document = json.loads(raw, object_pairs_hook=_json_pairs,
                              parse_int=_json_int, parse_float=_json_float,
                              parse_constant=lambda value: _fail("non-finite JSON number"))
        _check_document_budget(document)
        if type(document) is not dict or set(document) != {"format", "schema_version", "producer", "metadata", "data"}:
            _fail("invalid artifact document fields")
        if document["format"] != FORMAT or type(document["schema_version"]) is not int or document["schema_version"] != SCHEMA_VERSION:
            _fail("unsupported artifact format/schema version")
        if type(document["producer"]) is not dict or set(document["producer"]) != {"version", "commit"} or not all(isinstance(value, str) for value in document["producer"].values()):
            _fail("invalid artifact producer metadata")
        if type(document["metadata"]) is not dict:
            _fail("invalid artifact metadata")
        data = _Decoder().decode(document["data"])
        _validate_payload(data)
        return data
    except ArtifactFormatError:
        raise
    except (OSError, EOFError, ValueError, TypeError, RecursionError, OverflowError, zlib.error) as error:
        raise ArtifactFormatError("invalid gzip JSON artifact: " + str(error)) from error
