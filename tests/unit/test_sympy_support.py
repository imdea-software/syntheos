import sympy
from sympy import And, Not, Or, Symbol

from syntheos.formula import ltlBoolSym, ltlDisj, ltlNeg
from syntheos.sympy_support import getnewknowledge, ourdistribute


def test_ourdistribute_distributes_and_over_or():
    a, b, c = sympy.symbols("a b c")
    result = list(ourdistribute(Or(And(a, b), c)))
    assert set(result) == {Or(a, c), Or(b, c)}


def test_ourdistribute_passthrough_when_nothing_to_distribute():
    a, b = sympy.symbols("a b")
    expr = Or(Not(a), b)
    assert list(ourdistribute(expr)) == [expr]


def test_getnewknowledge_finds_unknown_implication():
    a, b = Symbol("a"), Symbol("b")
    candidate = Or(Not(a), b)
    assert getnewknowledge([], candidate) == candidate


def test_getnewknowledge_returns_none_when_already_known():
    a_lit, b_lit = ltlBoolSym("a"), ltlBoolSym("b")
    known = [ltlDisj(ltlNeg(a_lit), b_lit)]  # a -> b, already known
    candidate = Or(Not(Symbol("a")), Symbol("b"))
    assert getnewknowledge(known, candidate) is None
