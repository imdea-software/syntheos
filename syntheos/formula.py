"""The LTLt formula representation shared across the whole tool.

A formula is a plain dict `{"kind": ..., "operators": [...]}`:

- kind "BOOLSYM" wraps a single operand which is either the literal name
  ("l0", "l1", ...) of a Boolean/propositional atom, or the constants "t"/"f".
- kind "Z3" wraps a single operand which is a raw Z3 expression (a theory
  atom, before it has been abstracted into a Boolean literal).
- any other kind ("!", "&", "|", "->", "<->", "X", "G", "F", "W", "R") is an
  LTL/propositional connective over 1 or 2 sub-formulas.

This module also carries the conversions between that representation and Z3
expressions (for calling the solver) and sympy Boolean expressions (for the
sympy-based tautology search in `refinement.py`).

Formula is deliberately just `dict[str, Any]`: its shape depends on "kind"
(a leaf's "operators" holds a str or a raw Z3 term, an internal node's holds
1-2 sub-formulas), which plain `dict`/`TypedDict` typing can't express
precisely without a lot of ceremony for little real benefit here - the
functions in this module are exactly the code that already enforces that
shape at runtime via isBoolSym/isZ3/kind checks.
"""

from functools import reduce
from typing import Any, TypedDict, Union

import sympy
from sympy.logic.boolalg import Boolean
from z3 import BoolRef, ExprRef

from . import z3_support as mnz3
from .errors import SyntheosError

Formula = dict[str, Any]
# A formula's "operators" holds either a literal name/raw theory term (a leaf)
# or 1-2 sub-formulas (an internal node) - see the module docstring.
Operand = Union[str, ExprRef, Formula]


class Variable(TypedDict):
    """One entry of a spec's `variables:` list."""

    name: str
    type: str
    owner: str


def fetchdepth(lit: ExprRef) -> int:
    """How many `y(...)` (previous-value) wrappers deep a Z3 term is nested,
    e.g. `y(y(x))` has fetch depth 2. Composite terms take the max over their
    children."""
    if mnz3.isz3var(lit):
        name = lit.decl().name()
        depth = 0
        while name.startswith("FETCH_"):
            depth += 1
            name = name[6:]
        return depth
    if mnz3.isz3const(lit):
        return 0
    return max(fetchdepth(child) for child in lit.children())


def replaceliterals(formula: Formula, transtab: dict[str, Formula]) -> Formula:
    """Substitute each Boolean literal in `formula` with its theory formula
    from `transtab` (as produced by the HOA parser's AP table)."""
    if isBoolSym(formula):
        if isBoolSymTrue(formula) or isBoolSymFalse(formula):
            return formula
        return transtab[symbol(formula)]
    if isZ3(formula):
        raise SyntheosError("Theory element while replacing literals")
    return createLTLExpr(formula["kind"], [replaceliterals(op, transtab) for op in formula["operators"]])


def isconstant(v: str) -> bool:
    return v.lstrip("-").isdigit()


def z3getvars(e: ExprRef) -> list[ExprRef]:
    """All uninterpreted Z3 variables appearing in `e`, deduplicated."""

    def getset(expr: ExprRef) -> set[ExprRef]:
        if mnz3.isz3var(expr):
            return {expr}
        if mnz3.isz3const(expr):
            return set()
        return reduce(lambda acc, child: acc | getset(child), expr.children(), set())

    return list(getset(e))


def ltlt2str(f: Formula) -> str:
    """Render as the flat LTL syntax Strix/SeMLL expect on the command line."""
    if isBoolSym(f):
        if isBoolSymTrue(f):
            return "t"
        if isBoolSymFalse(f):
            return "f"
        return symbol(f)
    if isZ3(f):
        return "[" + mnz3.z32str(getZ3(f)) + "]"
    if len(f["operators"]) == 1:
        return f["kind"] + "(" + ltlt2str(f["operators"][0]) + ")"
    if len(f["operators"]) == 2:
        return "(" + ltlt2str(f["operators"][0]) + " " + f["kind"] + " " + ltlt2str(f["operators"][1]) + ")"
    raise SyntheosError("Unhandled formula shape: " + str(f))  # unreachable: every kind has 1 or 2 operators


def symbol(l: Formula) -> str:
    assert isBoolSym(l)
    return l["operators"][0]


def getZ3(l: Formula) -> ExprRef:
    assert isZ3(l)
    return l["operators"][0]


def ltlt2z3(f: Formula) -> BoolRef:
    """Convert a (theory-free, i.e. already-boolized where relevant) LTLt
    formula into a Z3 expression. A "Z3"-kind node still holding a temporal
    operator (e.g. produced by z32ltlt on a quantifier) is recursively
    re-expanded rather than returned verbatim."""
    if isBoolSym(f):
        if isBoolSymTrue(f):
            return mnz3.BoolVal(True)
        if isBoolSymFalse(f):
            return mnz3.BoolVal(False)
        raise SyntheosError("Non constant bool symbol converting to z3")
    if isZ3(f):
        newexpr = z32ltlt(getZ3(f))
        if isZ3(newexpr):
            return getZ3(newexpr)
        return ltlt2z3(newexpr)
    z3funs = {
        "!": mnz3.Not,
        "&": mnz3.And,
        "|": mnz3.Or,
    }
    return z3funs[f["kind"]](*(ltlt2z3(op) for op in f["operators"]))


def getliterals(formula: Formula) -> list[ExprRef]:
    """All Z3 theory atoms appearing in a (fully expanded, propositional)
    formula."""
    if isBoolSymTrue(formula) or isBoolSymFalse(formula):
        return []
    if isBoolSym(formula):
        raise SyntheosError("Bool symbol in full expression: " + str(formula))
    if isZ3(formula):
        return [getZ3(formula)]
    return reduce(lambda acc, op: acc + getliterals(op), formula["operators"], [])


def isBoolSym(formula: Formula) -> bool:
    return formula["kind"] == "BOOLSYM"


def isBoolSymTrue(formula: Formula) -> bool:
    return isBoolSym(formula) and symbol(formula) == "t"


def isBoolSymFalse(formula: Formula) -> bool:
    return isBoolSym(formula) and symbol(formula) == "f"


def isZ3(formula: Formula) -> bool:
    return formula["kind"] == "Z3"


def ltl2sympy(formula: Formula) -> Boolean:
    """Convert a purely propositional (no temporal operators, no raw Z3
    nodes) formula into a sympy Boolean expression, for `refinement.py`'s
    tautology search."""
    if isBoolSym(formula):
        return sympy.Symbol(symbol(formula))
    sympyfuns = {
        "!": sympy.Not,
        "&": sympy.And,
        "|": sympy.Or,
    }
    return sympyfuns[formula["kind"]](*(ltl2sympy(op) for op in formula["operators"]))


def createLTLExpr(kind: str, operators: list[Operand]) -> Formula:
    return {"kind": kind, "operators": operators}


def ltlConj(a: Formula, b: Formula) -> Formula:
    return createLTLExpr("&", [a, b])


def ltlDisj(a: Formula, b: Formula) -> Formula:
    return createLTLExpr("|", [a, b])


def ltlZ3(a: ExprRef) -> Formula:
    return createLTLExpr("Z3", [a])


def ltlNeg(a: Formula) -> Formula:
    return createLTLExpr("!", [a])


def ltlImplies(a: Formula, b: Formula) -> Formula:
    return createLTLExpr("->", [a, b])


def ltlIff(a: Formula, b: Formula) -> Formula:
    return createLTLExpr("<->", [a, b])


def ltlG(a: Formula) -> Formula:
    return createLTLExpr("G", [a])


def ltlX(a: Formula) -> Formula:
    return createLTLExpr("X", [a])


def ltlBoolSym(a: str) -> Formula:
    return createLTLExpr("BOOLSYM", [a])


def z32ltlt(f: ExprRef) -> Formula:
    """Convert a Z3 expression into an LTLt formula (the inverse direction of
    ltlt2z3 for the propositional connectives, plus turning arithmetic
    comparisons into Z3-wrapped atoms)."""
    funs = {
        "negator": ltlNeg,
        "conjunctor": ltlConj,
        "disjunctor": ltlDisj,
        "thwrapper": ltlZ3,
        "constTrue": ltlBoolSym("t"),
        "constFalse": ltlBoolSym("f"),
    }
    return mnz3.z32ltltw(f, funs)


def getz3vars(identifiers: list[str], variables: list[Variable]) -> dict[str, ExprRef]:
    """Build {identifier: z3 variable} for the given identifier names, looking
    up each one's declared type in `variables` (stripping any `FETCH_`
    prefixes added for `y(...)` references first)."""
    varstable = {v["name"]: v["type"] for v in variables}

    def findtype(name: str) -> str:
        while name.startswith("FETCH_"):
            name = name[6:]
        return varstable[name]

    return {key: mnz3.makevar(key, findtype(key)) for key in identifiers}
