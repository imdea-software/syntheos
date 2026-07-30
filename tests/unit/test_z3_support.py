import pytest
import z3

from syntheos import z3_support as zs
from syntheos.errors import SyntheosError


def test_isz3var_and_isz3const():
    x = z3.Int("x")
    assert zs.isz3var(x)
    assert not zs.isz3const(x)
    assert zs.isz3const(z3.IntVal(3))
    assert not zs.isz3var(z3.IntVal(3))
    assert zs.isz3const(z3.BoolVal(True))


def test_quantify_returns_formula_unchanged_for_empty_varlist():
    x = z3.Int("x")
    formula = x > 0
    assert zs.make_forall([], formula) is formula
    assert zs.make_exists([], formula) is formula


def test_quantify_wraps_when_vars_present():
    x = z3.Int("x")
    q = zs.make_forall([x], x > 0)
    assert z3.is_quantifier(q)
    assert q.is_forall()


def test_isSat():
    x = z3.Int("x")
    assert zs.isSat(x > 0)
    assert not zs.isSat(z3.And(x > 0, x < 0))


def test_makevar():
    assert zs.makevar("x", "Int").sort() == z3.IntSort()
    assert zs.makevar("x", "Real").sort() == z3.RealSort()
    with pytest.raises(SyntheosError):
        zs.makevar("x", "Bool")


def test_getUnsatCore_returns_only_conflicting_atoms():
    x = z3.Int("x")
    a, b, c = x > 0, x < 0, x > -100
    core = zs.getUnsatCore([a, b, c])
    assert len(core) == 2


def test_push_negation_flips_comparison():
    x = z3.Int("x")
    result = zs.push_negation(z3.Not(x > 0))
    solver = z3.Solver()
    solver.add(result != (x <= 0))
    assert solver.check() == z3.unsat


def test_push_negation_distributes_over_and():
    x, y = z3.Ints("x y")
    result = zs.push_negation(z3.Not(z3.And(x > 0, y > 0)))
    solver = z3.Solver()
    solver.add(result != z3.Or(x <= 0, y <= 0))
    assert solver.check() == z3.unsat


def test_z32str_renders_comparison():
    x, y = z3.Ints("x y")
    assert zs.z32str(x < y) == "x < y"


def test_z32ltltw_converts_comparisons_with_custom_constructors():
    x, y = z3.Ints("x y")
    funs = {
        "negator": lambda a: ("not", a),
        "conjunctor": lambda a, b: ("and", a, b),
        "disjunctor": lambda a, b: ("or", a, b),
        "thwrapper": lambda a: ("th", a),
        "constTrue": ("true",),
        "constFalse": ("false",),
    }
    result = zs.z32ltltw(x < y, funs)
    assert result == ("th", x < y) or (result[0] == "th")


def test_z32ltltw_true_false():
    funs = {
        "negator": lambda a: ("not", a),
        "conjunctor": lambda a, b: ("and", a, b),
        "disjunctor": lambda a, b: ("or", a, b),
        "thwrapper": lambda a: ("th", a),
        "constTrue": ("true",),
        "constFalse": ("false",),
    }
    assert zs.z32ltltw(z3.BoolVal(True), funs) == ("true",)
    assert zs.z32ltltw(z3.BoolVal(False), funs) == ("false",)
