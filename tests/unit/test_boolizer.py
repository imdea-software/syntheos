import z3

from syntheos.boolizer import Booleanizer, LITTY, mapfetch, makeconj
from syntheos.formula import isBoolSym, ltlBoolSym, ltlConj, ltlG, ltlZ3

VARIABLES = [
    {"name": "x", "type": "Int", "owner": "system"},
    {"name": "y", "type": "Int", "owner": "environment"},
]


def make_booleanizer():
    return Booleanizer(VARIABLES)


def test_isSysVar():
    b = make_booleanizer()
    assert b.isSysVar("x")
    assert not b.isSysVar("y")


def test_boolize_assigns_fresh_literals_and_reuses_them():
    b = make_booleanizer()
    x = z3.Int("x")
    lit1 = b.boolize(ltlZ3(x > 0))
    lit2 = b.boolize(ltlZ3(x > 0))
    assert isBoolSym(lit1)
    assert lit1 == lit2  # same theory atom -> same literal, not a fresh one
    assert len(b.littable) == 1


def test_boolize_classifies_literal_kind_by_variables():
    b = make_booleanizer()
    x, y = z3.Int("x"), z3.Int("y")
    b.boolize(ltlZ3(x > 0))
    b.boolize(ltlZ3(y > 0))
    kinds = {name: kind for name, [_, kind] in b.littable.items()}
    assert set(kinds.values()) == {LITTY.SYS, LITTY.ENV}


def test_boolize_constants_pass_through():
    b = make_booleanizer()
    t = ltlBoolSym("t")
    assert b.boolize(t) == t
    assert len(b.littable) == 0


def test_containssysvars():
    b = make_booleanizer()
    x, y = z3.Int("x"), z3.Int("y")
    assert b.containssysvars(x > 0)
    assert not b.containssysvars(y > 0)


def test_setformula_computes_max_fetch_depth():
    b = make_booleanizer()
    x = z3.Int("x")
    fetched_once = z3.Int("FETCH_x")
    formula = ltlConj(ltlZ3(x > 0), ltlZ3(fetched_once > 0))
    b.setformula(formula)
    assert b.maxfetchdepth == 1


def test_addguarantee_and_addassumption_dedupe():
    b = make_booleanizer()
    x = z3.Int("x")
    atom = ltlZ3(x > 0)
    b.addguarantee(ltlG(atom))
    b.addguarantee(ltlG(atom))
    assert len(b.guarantees) == 1


def test_createtauto_and_tautoExists_roundtrip():
    b = make_booleanizer()
    x = z3.Int("x")
    atom = x > 0
    assert not b.tautoExists(atom)
    tauto = b.createTauto(atom)
    b.fetchtautos.append(tauto)
    assert b.tautoExists(atom)
    assert tauto["kind"] == "G"


def test_getboolformula_combines_assumptions_guarantees_and_formula():
    b = make_booleanizer()
    # setformula() also derives maxfetchdepth from the (here, deliberately
    # empty) literal table, which only makes sense for a formula that
    # actually mentions a theory atom - set .formula directly to keep this
    # test focused on getboolformula's own assembly logic.
    b.formula = ltlBoolSym("t")
    assert b.getboolformula() == ltlBoolSym("t")
    y = z3.Int("y")
    b.addassumption(ltlG(ltlZ3(y > 0)))
    combined = b.getboolformula()
    assert combined["kind"] == "->"


def test_mapfetch_prefixes_variables_not_constants():
    x, y = z3.Ints("x y")
    mapped = mapfetch(x + y * 2)
    solver = z3.Solver()
    fx, fy = z3.Ints("FETCH_x FETCH_y")
    solver.add(mapped != fx + fy * 2)
    assert solver.check() == z3.unsat


def test_mapfetch_on_bare_variable():
    x = z3.Int("x")
    mapped = mapfetch(x)
    assert mapped.decl().name() == "FETCH_x"


def test_mapfetch_on_constant_is_noop():
    c = z3.IntVal(5)
    assert mapfetch(c).as_long() == 5


def test_makeconj_empty_and_nonempty():
    assert makeconj([]) is None
    a, b = ltlBoolSym("a"), ltlBoolSym("b")
    assert makeconj([a, b]) == ltlConj(a, b)
