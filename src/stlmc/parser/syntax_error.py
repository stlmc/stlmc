"""Consistent, user-facing syntax errors for Lark parsers."""

from difflib import get_close_matches
from pathlib import Path
import re
from typing import Iterable, Optional

from lark import UnexpectedInput
from lark.lexer import PatternStr


_TOKEN_LABELS = {
    "$END": "end of file",
    "ARROW": "'=>'",
    "COLON": "':'",
    "COMMA": "','",
    "COMPARE_OP": "comparison operator",
    "DIFF": "'d/dt'",
    "EQUAL": "'='",
    "ESCAPED_STRING": "quoted string",
    "FALSE": "'false'",
    "FUNC_OP": "function (sin, cos, tan, or sqrt)",
    "INF": "'inf'",
    "LBRACE": "'{'",
    "LBRACK": "'['",
    "LPAR": "'('",
    "ADD_OP": "'+' or '-'",
    "MUL_OP": "'*' or '/'",
    "NAME": "name",
    "NEXT_NAME": "next-state name (for example x')",
    "NUMBER": "number",
    "RANGE_LEFT": "'[' or '('",
    "RANGE_RIGHT": "']' or ')'",
    "RBRACE": "'}'",
    "RBRACK": "']'",
    "RPAR": "')'",
    "SEMICOLON": "';'",
    "SIGNED_NUMBER": "signed number",
    "TRUE": "'true'",
    "TYPE": "type ('bool', 'int', or 'real')",
}

_OPERATOR_CHARACTERS = set("+-*/<>=")


def _expected_labels(error, token_labels):
    expected = getattr(error, "expected", None) or getattr(error, "allowed", None)
    if not expected:
        return []
    labels = dict(_TOKEN_LABELS)
    labels.update(token_labels)
    return sorted({labels.get(token, token.lower().replace("_", " "))
                   for token in expected})


def _keyword_suggestion(line: str, keywords: Iterable[str]):
    match = re.match(
        r"\s*([A-Za-z][A-Za-z0-9_-]*)\s*(?::|=|\{|extends\b)", line
    )
    if match is None:
        return None
    actual = match.group(1)
    close = get_close_matches(actual, tuple(keywords), n=1, cutoff=0.7)
    if not close or close[0] == actual:
        return None
    return actual, close[0]


def _model_hint(line, column, unexpected):
    before = line[:max(column - 1, 0)].rstrip()
    if (unexpected in _OPERATOR_CHARACTERS and before
            and before[-1] in _OPERATOR_CHARACTERS):
        if before[-1] in "=<>":
            return (
                "expected an expression after {!r}; operator {!r} cannot "
                "start an expression".format(before[-1], unexpected)
            )
        return (
            "operator {!r} cannot follow {!r}; add an expression between them"
            .format(unexpected, before[-1])
        )

    constant = re.match(
        r"\s*const\s+[A-Za-z][A-Za-z0-9]*\s*=\s*"
        r"([A-Za-z][A-Za-z0-9]*)",
        line,
    )
    if constant is not None and constant.group(1) == unexpected:
        return (
            "constant values must be a number, 'true', or 'false'; "
            "a name cannot be used here"
        )
    return None


def syntax_error(file_name: str, source: str, error: UnexpectedInput,
                 *, description: Optional[str] = None,
                 keywords: Iterable[str] = (), token_labels=None) -> SyntaxError:
    """Convert a Lark parse failure into a concise diagnostic with source context."""
    location = f'{file_name}:{error.line}:{error.column}'
    lines = source.splitlines()
    raw_line = lines[error.line - 1] if 0 < error.line <= len(lines) else ""
    line = raw_line.expandtabs(4)
    pointer_column = len(raw_line[:max(error.column - 1, 0)].expandtabs(4))
    pointer = " " * pointer_column + "^"

    raw_unexpected = getattr(error, "char", None)
    if raw_unexpected is None:
        token = getattr(error, "token", None)
        raw_unexpected = None if token is None or str(token) == "" else str(token)
    unexpected = (
        "end of file" if raw_unexpected is None else repr(raw_unexpected)
    )

    heading = f"{location}: syntax error"
    if description:
        heading += f" in {description}"
    details = [heading, f"  unexpected {unexpected}"]
    model_hint = (
        _model_hint(raw_line, error.column, raw_unexpected)
        if description == "model" else None
    )
    suggestion = _keyword_suggestion(raw_line, keywords)
    if model_hint is not None:
        details.append("  " + model_hint)
    elif suggestion is not None:
        actual, expected_keyword = suggestion
        details.append(
            "  unknown keyword {!r}; did you mean {!r}?".format(
                actual, expected_keyword
            )
        )
    else:
        expected = _expected_labels(error, token_labels or {})
        if expected:
            shown = expected[:8]
            suffix = "" if len(expected) <= 8 else " (and {} more)".format(
                len(expected) - 8
            )
            details.append("  expected " + ", ".join(shown) + suffix)
    if line:
        details.extend((f"  {line}", f"  {pointer}"))
    return SyntaxError("\n".join(details))


def parse_file(parser, file_name: str, *, description: Optional[str] = None,
               keywords: Iterable[str] = ()):
    """Read and parse a UTF-8 file, enriching only Lark syntax failures."""
    source = Path(file_name).read_text(encoding="utf-8")
    try:
        return parser.parse(source)
    except UnexpectedInput as error:
        token_labels = {
            terminal.name: repr(terminal.pattern.value)
            for terminal in parser.terminals
            if isinstance(terminal.pattern, PatternStr)
        }
        raise syntax_error(
            file_name, source, error, description=description, keywords=keywords,
            token_labels=token_labels,
        ) from error
