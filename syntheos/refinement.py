"""Turning a sympy tautology found by `sympy_support.getnewknowledge` back
into an LTLt formula, and shrinking a refuted theory disjunction down to its
unsat core so only the atoms that actually matter get remembered.
"""

from functools import reduce

from sympy import And, Not, Or, false, true
from sympy.logic.boolalg import Boolean
from z3 import BoolRef

from . import z3_support as mnz3
from .boolizer import Booleanizer
from .errors import SyntheosError
from .formula import (
    Formula,
    ltl2sympy,
    ltlBoolSym,
    ltlConj,
    ltlDisj,
    ltlNeg,
    ltlt2z3,
    ltlZ3,
    replaceliterals,
    z32ltlt,
)
from .sympy_support import getnewknowledge


def sympy2ltl(e: Boolean) -> Formula:
    if len(e.args) == 0:
        if e == true:
            name = "t"
        elif e == false:
            name = "f"
        else:
            name = e.name
        return ltlBoolSym(name)
    newargs = map(sympy2ltl, e.args)
    if e.func == Not:
        return ltlNeg(*newargs)
    if e.func == Or:
        return reduce(ltlDisj, newargs)
    if e.func == And:
        return reduce(ltlConj, newargs)
    raise SyntheosError("Unhandled case:" + str(e))


def refinetauto(boolizer: Booleanizer, ltlform: Formula) -> Formula | None:
    """Given a formula the CEGAR loop found to be a theory tautology
    (`ltlform`, e.g. `!envplay | sysplay`), search for a new Boolean
    tautology it implies that isn't already known, and return its minimal
    (unsat-core-reduced) theory-level disjunction - or None if nothing new
    was found."""
    sympyform = ltl2sympy(boolizer.boolize(ltlform))
    newknowledge = getnewknowledge(boolizer.booltautos, sympyform)
    if newknowledge is None:
        return None
    tauto = sympy2ltl(newknowledge)
    transtab = {k: ltlZ3(v) for k, (v, _kind) in boolizer.littable.items()}
    play = replaceliterals(tauto, transtab)
    return satcore(play)


def getatoms(tauto: Formula) -> list[BoolRef]:
    if tauto["kind"] == "!":
        return [ltlt2z3(tauto["operators"][0])]
    if tauto["kind"] == "|":
        return [atom for op in tauto["operators"] for atom in getatoms(op)]
    return [ltlt2z3(ltlNeg(tauto))]


def negatom(atom: Formula) -> Formula:
    if atom["kind"] == "!":
        return atom["operators"][0]
    return ltlNeg(atom)


def satcore(tauto: Formula) -> Formula:
    atoms = mnz3.getUnsatCore(getatoms(tauto))
    return reduce(ltlDisj, (negatom(z32ltlt(atom)) for atom in atoms))
