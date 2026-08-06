"""The LTLt formula representation used by the shield.

A formula is a plain dict `{"kind": ..., "operators": [...]}`:

- kind "BOOLSYM" wraps a single operand which is either the literal name
  ("l0", "l1", ...) of a Boolean/propositional atom, or the constants "t"/"f".
- kind "Z3" wraps a single operand which is a raw Z3 expression (a theory
  atom, before it has been abstracted into a Boolean literal).
- any other kind ("!", "&", "|") is a propositional connective over 1 or 2
  sub-formulas.

This module also carries the conversions between that representation and Z3
expressions, for evaluating a mealy machine's edge conditions against actual
play values.

Formula is deliberately just `dict[str, Any]`: its shape depends on "kind"
(a leaf's "operators" holds a str or a raw Z3 term, an internal node's holds
1-2 sub-formulas), which plain `dict`/`TypedDict` typing can't express
precisely without a lot of ceremony for little real benefit here - the
functions in this module are exactly the code that already enforces that
shape at runtime via isBoolSym/isZ3/kind checks.
"""

from typing import Any, TypeAlias, TypedDict

from z3 import BoolRef, ExprRef

from . import z3_support as mnz3
from .errors import ShieldError

Formula = dict[str, Any]
# A formula's "operators" holds either a literal name/raw theory term (a leaf)
# or 1-2 sub-formulas (an internal node) - see the module docstring.
Operand: TypeAlias = str | ExprRef | Formula


class Variable(TypedDict):
    """One entry of a mealy machine's `variables:` list."""

    name: str
    type: str
    owner: str


def fetchdepth(lit: ExprRef) -> int:
    """How many `FETCH_` (previous-value) prefixes deep a Z3 term is nested,
    e.g. `FETCH_FETCH_x` has fetch depth 2. Composite terms take the max over
    their children."""
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
    from `transtab` (as produced by the mealy machine's transtab table)."""
    if isBoolSym(formula):
        if isBoolSymTrue(formula) or isBoolSymFalse(formula):
            return formula
        return transtab[symbol(formula)]
    if isZ3(formula):
        raise ShieldError("Theory element while replacing literals")
    return createLTLExpr(formula["kind"], [replaceliterals(op, transtab) for op in formula["operators"]])


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
        raise ShieldError("Non constant bool symbol converting to z3")
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


def isBoolSym(formula: Formula) -> bool:
    return formula["kind"] == "BOOLSYM"


def isBoolSymTrue(formula: Formula) -> bool:
    return isBoolSym(formula) and symbol(formula) == "t"


def isBoolSymFalse(formula: Formula) -> bool:
    return isBoolSym(formula) and symbol(formula) == "f"


def isZ3(formula: Formula) -> bool:
    return formula["kind"] == "Z3"


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
    prefixes added for previous-value references first)."""
    varstable = {v["name"]: v["type"] for v in variables}

    def findtype(name: str) -> str:
        while name.startswith("FETCH_"):
            name = name[6:]
        return varstable[name]

    return {key: mnz3.makevar(key, findtype(key)) for key in identifiers}
