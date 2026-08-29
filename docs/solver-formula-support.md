# Solver formula support

STLMC encodes temporal operators before invoking an SMT solver. Therefore
`[]`, `<>`, `U`, and `R` have the same front-end support for CVC5, Z3, Yices,
and dReal. Solver-specific restrictions apply to the arithmetic expressions in
flows, invariants, jump conditions, initial conditions, propositions, and STL
atomic predicates.

## Support matrix

| Formula feature | CVC5 | Z3 | Yices | dReal 3 |
| --- | --- | --- | --- | --- |
| Boolean operators and comparisons | Supported | Supported | Supported | Supported |
| `+`, `-`, `*`, `/`, unary `-` | Supported | Supported | Supported | Supported |
| `x ** n`, non-negative integer constant `n` | Supported | Supported | Supported | Supported |
| Fractional, negative, or symbolic exponent | Rejected | Rejected | Rejected | Supported |
| `sqrt` | Rejected | Rejected | Rejected | Supported |
| `sin`, `cos`, `tan` | Rejected | Rejected | Rejected | Supported |
| `arcsin`, `arccos`, `arctan` | Rejected | Rejected | Rejected | Supported |
| STL `[]`, `<>`, `U`, `R` | Encoded by STLMC | Encoded by STLMC | Encoded by STLMC | Encoded by STLMC |

“Supported” means that STLMC has an intentional solver translation for the
operator. It does not guarantee that every resulting nonlinear problem will
finish within a particular timeout. Division by an expression that can be
zero also remains subject to the target solver's arithmetic semantics.

## Validation behavior

STLMC validates the selected solver against the parsed model and selected goal
before constructing bound queries or starting parallel workers. Unsupported
arithmetic exits with status 2 and a message such as:

```text
conversion error: solver 'z3' does not support sqrt in expression (sqrt x) (use dReal for transcendental arithmetic)
```

This is distinct from `unknown`: `unknown` means that a supported formula was
sent to a solver but the solver could not establish `sat` or `unsat`.

CVC5, Z3, and Yices intentionally accept only non-negative integer constant powers.
This prevents symbolic Yices exponents from being assigned an unrelated model
value and keeps polynomial configurations within their intended arithmetic
fragment.

When `solver = "auto"`, STLMC recursively inspects model and goal expressions.
It selects dReal when a transcendental function or a non-integer, negative, or
symbolic exponent is present, including when that operation is nested inside
another arithmetic expression.

## dReal function names

The model language uses `arcsin`, `arccos`, and `arctan`. The supported dReal 3
SMT2 syntax uses `asin`, `acos`, and `atan`; STLMC translates these names. The
`tan` operator is emitted as `sin(x) / cos(x)` for compatibility with the
bundled solver.
