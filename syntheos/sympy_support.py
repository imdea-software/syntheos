"""Sympy-based tautology search used by `refinement.py`.

Given the current set of known Boolean tautologies (over the literal table)
and a candidate implication that the CEGAR loop wants to refute, this module
distributes the candidate into a disjunction of "prime" clauses and finds one
that is not yet implied by current knowledge - that clause becomes the new
tautology to learn.
"""

from itertools import chain

from sympy import And, Or, sympify
from sympy.logic.boolalg import eliminate_implications
from sympy.logic.inference import satisfiable

from . import logging_utils
from .formula import ltl2sympy


def ourdistribute(expr):
    """Distribute Or-over-And one step at a time, lazily, instead of sympy's
    full `to_cnf`/`to_dnf` (which can blow up); yields the resulting
    disjuncts/conjuncts depth-first."""
    if isinstance(expr, Or):
        for arg in expr.args:
            if isinstance(arg, And):
                conj = arg
                break
        else:
            return [expr]
        rest = Or(*[a for a in expr.args if a is not conj])
        return (b for c in conj.args for b in ourdistribute(Or(c, rest)))
    elif isinstance(expr, And):
        return chain(*map(ourdistribute, expr.args))
    return [expr]


def isnewknowledge(sympyknowledge, tauto) -> bool:
    return satisfiable(~tauto & sympyknowledge)


def getnewknowledge(booltautos: list, expr):
    """Find a clause of `expr` (an implication candidate, already
    boolized) that isn't already entailed by `booltautos`, or None if every
    clause is already known."""
    sympyknowledge = And(*map(ltl2sympy, booltautos))
    expr = sympify(expr)
    expr = eliminate_implications(expr)
    for count, tauto in enumerate(ourdistribute(expr), 1):
        if count > 10000:
            logging_utils.trace("Checking tauto %d", count)
            logging_utils.trace("%s", tauto)
        if isnewknowledge(sympyknowledge, tauto):
            return tauto
    return None
