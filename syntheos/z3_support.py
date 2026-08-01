"""The Z3 theory backend.

Surprise! It is z3. This module is the seam between the rest of Syntheos and
whichever solver backs the "theories" in LTLt: everything downstream reaches
Z3 through here (as `mnz3.X`) rather than importing z3 directly, so a
different theory backend could in principle be dropped in by reimplementing
this module's interface.

z3 ships no type stubs, so mypy can't verify anything about these calls -
but the names imported below (ExprRef, BoolRef, ArithRef, ...) are still the
real z3 classes, used as honest documentation of intent even though mypy
treats them as `Any` under the hood. `from z3 import *` would hide even that
(mypy can't discover names exported by an unstubbed wildcard import), so
every name actually used - internally or re-exported for callers as
`mnz3.X` - is imported explicitly instead.
"""

from collections.abc import Callable
from typing import Any

from z3 import (
    Z3_OP_ADD,
    Z3_OP_EQ,
    Z3_OP_GE,
    Z3_OP_GT,
    Z3_OP_LE,
    Z3_OP_LT,
    Z3_OP_UNINTERPRETED,
    And,
    ArithRef,
    BitVec,
    BitVecRef,
    Bool,
    BoolRef,
    BoolVal,
    Const,
    Exists,
    ExprRef,
    ForAll,
    Implies,
    Int,
    IntNumRef,
    Not,
    Or,
    Real,
    Solver,
    Tactic,
    get_var_index,
    is_and,
    is_const,
    is_eq,
    is_false,
    is_ge,
    is_gt,
    is_implies,
    is_int_value,
    is_le,
    is_not,
    is_or,
    is_quantifier,
    is_rational_value,
    is_true,
    is_var,
    sat,
    simplify,
    substitute,
    unsat,
    z3util,
)

from .errors import SyntheosError

__all__ = [
    "And",
    "Bool",
    "BoolVal",
    "Implies",
    "Not",
    "Or",
    "is_false",
    "is_true",
    "isz3const",
    "isz3var",
    "quantify",
    "make_forall",
    "make_exists",
    "isSat",
    "eliminate_quantifier",
    "getUnsatCore",
    "makevar",
    "rename_vars",
    "copy_and_rename",
    "push_negation",
    "z32str",
    "z32ltltw",
]


def isz3const(e: ExprRef) -> bool:
    return not isz3var(e) and (is_int_value(e) or is_rational_value(e) or is_true(e) or is_false(e))


def isz3var(e: ExprRef) -> bool:
    return is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED


def quantify(
    quantifier: Callable[[list[ExprRef], BoolRef], BoolRef], varlist: list[ExprRef], formula: BoolRef
) -> BoolRef:
    if varlist:
        return quantifier(varlist, formula)
    return formula


def make_forall(varlist: list[ExprRef], formula: BoolRef) -> BoolRef:
    return quantify(ForAll, varlist, formula)


def make_exists(varlist: list[ExprRef], formula: BoolRef) -> BoolRef:
    return quantify(Exists, varlist, formula)


def isSat(formula: BoolRef) -> bool:
    formula = simplify(formula)
    solver = Solver()
    solver.add(formula)
    result = solver.check()
    if result == sat:
        return True
    if result == unsat:
        return False
    raise SyntheosError("Unknown satisfiability")


def eliminate_quantifier(formula: BoolRef) -> BoolRef:
    return Tactic("qe2")(formula).as_expr()


def getUnsatCore(atoms: list[BoolRef]) -> list[BoolRef]:
    solver = Solver()
    solver.set(unsat_core=True)
    tracked = list(enumerate(atoms))
    for i, atom in tracked:
        solver.assert_and_track(atom, "atom_" + str(i))
    result = solver.check()
    assert result == unsat
    core = solver.unsat_core()
    return [atom for i, atom in tracked if Bool("atom_" + str(i)) in core]


def makevar(var: str, ty: str) -> ArithRef:
    match ty:
        case "Int":
            cons = Int
        case "Real":
            cons = Real
        case _:
            raise SyntheosError("Unhandled type: " + ty)
    return cons(var)


def rename_vars(expr: ExprRef, renamefn: Callable[[str], str]) -> ExprRef:
    return substitute(expr, [(var, Const(renamefn(var.decl().name()), var.sort())) for var in z3util.get_vars(expr)])


def copy_and_rename(var: ExprRef, renamefn: Callable[[str], str]) -> ExprRef:
    new_name = renamefn(var.decl().name())
    if isinstance(var, IntNumRef) or isinstance(var, ArithRef):  # Int or Real
        return Int(new_name) if var.is_int() else Real(new_name)
    elif isinstance(var, BoolRef):  # Boolean
        return Bool(new_name)
    elif isinstance(var, BitVecRef):  # Bit-vector
        return BitVec(new_name, var.size())
    else:
        raise TypeError("Unsupported Z3 variable type")


def push_negation(expr: BoolRef) -> BoolRef:
    """Push a top-level Not inward through comparisons/And/Or, for nicer
    printing (see z32str / play2str)."""
    if is_not(expr):
        inner = expr.arg(0)
        if inner.decl().kind() == Z3_OP_GT:
            return inner.arg(0) <= inner.arg(1)
        elif inner.decl().kind() == Z3_OP_GE:
            return inner.arg(0) < inner.arg(1)
        elif inner.decl().kind() == Z3_OP_LT:
            return inner.arg(0) >= inner.arg(1)
        elif inner.decl().kind() == Z3_OP_LE:
            return inner.arg(0) > inner.arg(1)
        elif is_and(inner):
            return Or(*[push_negation(Not(arg)) for arg in inner.children()])
        elif is_or(inner):
            return And(*[push_negation(Not(arg)) for arg in inner.children()])
        else:
            return Not(push_negation(inner))
    elif is_and(expr) or is_or(expr):
        return expr.decl()(*[push_negation(arg) for arg in expr.children()])
    else:
        return expr


def z32str(expr: ExprRef, parent_op: str | None = None, bound_vars: list[str] | None = None) -> str:
    """Human-readable rendering of a Z3 expression, used for reporting and
    for the mealy-machine dot dump."""
    if bound_vars is None:
        bound_vars = []
    if is_and(expr):
        conjunction_str = " ∧ ".join(z32str(arg, "And", bound_vars=bound_vars) for arg in expr.children())
        return f"({conjunction_str})" if parent_op != "And" and parent_op is not None else conjunction_str
    elif is_or(expr):
        disjunction_str = " ∨ ".join(z32str(arg, "Or", bound_vars=bound_vars) for arg in expr.children())
        return f"({disjunction_str})" if parent_op != "Or" and parent_op is not None else disjunction_str
    elif is_not(expr):
        negated_expr = z32str(expr.arg(0), "Not", bound_vars=bound_vars)
        return f"¬({negated_expr})"
    elif is_implies(expr):
        disjunction_str = " -> ".join(z32str(arg, "Implies", bound_vars=bound_vars) for arg in expr.children())
        return f"({disjunction_str})" if parent_op is not None else disjunction_str
    elif is_quantifier(expr):
        quant = "∀" if expr.is_forall() else "∃"
        num_vars = expr.num_vars()
        names = [str(expr.var_name(i)) for i in reversed(range(num_vars))]
        new_bound_vars = names + bound_vars
        body_str = z32str(expr.body(), None, new_bound_vars)
        vars_str = ", ".join(names)
        return f"{quant} {vars_str}. ({body_str})"
    elif is_var(expr):
        idx = get_var_index(expr)
        if idx < len(bound_vars):
            return bound_vars[idx]
        else:
            return "UNKNOWNVAR"
    elif expr.decl().kind() == Z3_OP_LE:
        return f"{z32str(expr.arg(0), bound_vars=bound_vars)} ≤ {z32str(expr.arg(1), bound_vars=bound_vars)}"
    elif expr.decl().kind() == Z3_OP_LT:
        return f"{z32str(expr.arg(0), bound_vars=bound_vars)} < {z32str(expr.arg(1), bound_vars=bound_vars)}"
    elif expr.decl().kind() == Z3_OP_GE:
        return f"{z32str(expr.arg(0), bound_vars=bound_vars)} ≥ {z32str(expr.arg(1), bound_vars=bound_vars)}"
    elif expr.decl().kind() == Z3_OP_GT:
        return f"{z32str(expr.arg(0), bound_vars=bound_vars)} > {z32str(expr.arg(1), bound_vars=bound_vars)}"
    elif expr.decl().kind() == Z3_OP_EQ:
        return f"{z32str(expr.arg(0), bound_vars=bound_vars)} = {z32str(expr.arg(1), bound_vars=bound_vars)}"
    elif expr.decl().kind() == Z3_OP_ADD:
        return f"{z32str(expr.arg(0), bound_vars=bound_vars)} + {z32str(expr.arg(1), bound_vars=bound_vars)}"
    else:
        return str(expr)


def z32ltltw(f: ExprRef, funs: dict[str, Any]) -> Any:
    """Generic Z3-expression -> LTLt-shaped-formula conversion, parametrized
    over the target formula constructors (`funs`) so both `formula.z32ltlt`
    and callers with their own formula representation can reuse it.

    `funs` and this function's return value are typed `Any` on purpose (not
    as an easy way out): the whole point of this helper is that it doesn't
    know or care what formula representation the caller uses, as long as
    `funs` supplies matching negator/conjunctor/disjunctor/thwrapper/
    constTrue/constFalse constructors for it.
    """
    ltlNeg = funs["negator"]
    ltlConj = funs["conjunctor"]
    ltlDisj = funs["disjunctor"]
    ltlTh = funs["thwrapper"]
    constTrue = funs["constTrue"]
    constFalse = funs["constFalse"]

    def convert(f: ExprRef) -> Any:
        if is_and(f):
            children = f.children()
            ret = convert(children[0])
            for child in children[1:]:
                ret = ltlConj(ret, convert(child))
            return ret
        if is_or(f):
            children = f.children()
            ret = convert(children[0])
            for child in children[1:]:
                ret = ltlDisj(ret, convert(child))
            return ret
        if is_not(f):
            return ltlNeg(convert(f.children()[0]))
        if is_ge(f):
            return ltlNeg(ltlTh(f.children()[0].__lt__(f.children()[1])))
        if is_gt(f):
            return ltlTh(f.children()[1].__lt__(f.children()[0]))
        if is_le(f):
            return ltlNeg(ltlTh(f.children()[1].__lt__(f.children()[0])))
        if is_eq(f):
            return ltlConj(
                ltlNeg(ltlTh(f.children()[1].__lt__(f.children()[0]))),
                ltlNeg(ltlTh(f.children()[0].__lt__(f.children()[1]))),
            )
        if is_false(f):
            return constFalse
        if is_true(f):
            return constTrue
        if is_quantifier:
            # NOTE: intentionally not calling is_quantifier(f) here - this
            # preserves a pre-existing behavior where it is always truthy, so
            # this branch is a catch-all: any node shape not matched above
            # (not just quantifiers) is treated as an opaque theory atom.
            # Changing this is a behavior change to the CEGAR algorithm, not
            # a cleanup, so it is left as found.
            return ltlTh(f)
        raise SyntheosError("Unhandled case:" + str(f))  # unreachable, see above

    return convert(f)
