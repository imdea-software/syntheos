import pytest
import sympy
import z3

from syntheos import formula as f
from syntheos.errors import SyntheosError


def test_constructors_and_predicates():
    t = f.ltlBoolSym("t")
    lit = f.ltlBoolSym("l0")
    assert f.isBoolSym(t) and f.isBoolSymTrue(t)
    assert f.isBoolSym(lit) and not f.isBoolSymTrue(lit) and not f.isBoolSymFalse(lit)
    assert f.symbol(lit) == "l0"

    conj = f.ltlConj(lit, t)
    assert conj == {"kind": "&", "operators": [lit, t]}
    assert not f.isZ3(conj)


def test_getZ3_and_isZ3():
    x = z3.Int("x")
    theory_atom = x > 0
    z = f.ltlZ3(theory_atom)
    assert f.isZ3(z)
    assert z3.eq(f.getZ3(z), theory_atom)


def test_ltlt2str_rendering():
    lit_a = f.ltlBoolSym("l0")
    lit_b = f.ltlBoolSym("l1")
    assert f.ltlt2str(f.ltlBoolSym("t")) == "t"
    assert f.ltlt2str(f.ltlBoolSym("f")) == "f"
    assert f.ltlt2str(lit_a) == "l0"
    assert f.ltlt2str(f.ltlNeg(lit_a)) == "!(l0)"
    assert f.ltlt2str(f.ltlConj(lit_a, lit_b)) == "(l0 & l1)"
    assert f.ltlt2str(f.ltlX(lit_a)) == "X(l0)"


def test_ltlt2z3_boolsym_constants():
    assert z3.is_true(f.ltlt2z3(f.ltlBoolSym("t")))
    assert z3.is_false(f.ltlt2z3(f.ltlBoolSym("f")))


def test_ltlt2z3_raises_on_nonconstant_boolsym():
    with pytest.raises(SyntheosError):
        f.ltlt2z3(f.ltlBoolSym("l0"))


def test_ltlt2z3_connectives():
    x, y = z3.Ints("x y")
    lhs = f.ltlZ3(x < y)
    rhs = f.ltlZ3(x < 0)
    z3expr = f.ltlt2z3(f.ltlConj(lhs, f.ltlNeg(rhs)))
    solver = z3.Solver()
    solver.add(z3expr != z3.And(x < y, z3.Not(x < 0)))
    assert solver.check() == z3.unsat


def test_z32ltlt_roundtrip_on_comparison():
    x, y = z3.Ints("x y")
    ltlt = f.z32ltlt(x < y)
    assert f.isZ3(ltlt)
    back = f.ltlt2z3(ltlt)
    solver = z3.Solver()
    solver.add(back != (x < y))
    assert solver.check() == z3.unsat


def test_z32ltlt_and_or_not():
    x, y = z3.Ints("x y")
    z3expr = z3.And(x < y, z3.Not(x < 0))
    ltlt = f.z32ltlt(z3expr)
    assert ltlt["kind"] == "&"
    back = f.ltlt2z3(ltlt)
    solver = z3.Solver()
    solver.add(back != z3expr)
    assert solver.check() == z3.unsat


def test_z3getvars_dedupes_and_ignores_constants():
    x, y = z3.Ints("x y")
    expr = z3.And(x < y, x > 0, z3.IntVal(3) < y)
    names = sorted(v.decl().name() for v in f.z3getvars(expr))
    assert names == ["x", "y"]


def test_fetchdepth_counts_fetch_prefixes():
    plain = z3.Int("x")
    once = z3.Int("FETCH_x")
    twice = z3.Int("FETCH_FETCH_x")
    assert f.fetchdepth(plain) == 0
    assert f.fetchdepth(once) == 1
    assert f.fetchdepth(twice) == 2
    assert f.fetchdepth(once + plain) == 1


def test_fetchdepth_ignores_constants():
    assert f.fetchdepth(z3.IntVal(5)) == 0


def test_getliterals_collects_theory_atoms():
    x = z3.Int("x")
    formula = f.ltlConj(f.ltlZ3(x < 1), f.ltlNeg(f.ltlZ3(x > 2)))
    atoms = f.getliterals(formula)
    assert len(atoms) == 2


def test_getliterals_empty_for_constants():
    assert f.getliterals(f.ltlBoolSym("t")) == []
    assert f.getliterals(f.ltlBoolSym("f")) == []


def test_replaceliterals_substitutes_boolsym_leaves():
    transtab = {"l0": f.ltlZ3(z3.Int("x") > 0)}
    formula = f.ltlNeg(f.ltlBoolSym("l0"))
    replaced = f.replaceliterals(formula, transtab)
    assert replaced == f.ltlNeg(transtab["l0"])


def test_replaceliterals_keeps_constants():
    t = f.ltlBoolSym("t")
    assert f.replaceliterals(t, {}) == t


def test_ltl2sympy_matches_structure():
    a = f.ltlBoolSym("a")
    b = f.ltlBoolSym("b")
    expr = f.ltl2sympy(f.ltlConj(a, f.ltlNeg(b)))
    assert expr == sympy.And(sympy.Symbol("a"), sympy.Not(sympy.Symbol("b")))


def test_getz3vars_resolves_types_through_fetch_prefix():
    variables = [{"name": "x", "type": "Int", "owner": "system"}]
    z3vars = f.getz3vars(["x", "FETCH_x"], variables)
    assert z3vars["x"].sort() == z3.IntSort()
    assert z3vars["FETCH_x"].decl().name() == "FETCH_x"
    assert z3vars["FETCH_x"].sort() == z3.IntSort()
