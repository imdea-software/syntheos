import z3
from sympy import Symbol

from syntheos.formula import ltlBoolSym, ltlConj, ltlDisj, ltlNeg, ltlZ3
from syntheos.refinement import getatoms, negatom, satcore, sympy2ltl


def test_sympy2ltl_atom():
    assert sympy2ltl(Symbol("a")) == ltlBoolSym("a")


def test_sympy2ltl_true_false():
    from sympy import false, true

    assert sympy2ltl(true) == ltlBoolSym("t")
    assert sympy2ltl(false) == ltlBoolSym("f")


def test_sympy2ltl_and_or_not_roundtrip():
    from syntheos.formula import ltl2sympy

    a, b = ltlBoolSym("a"), ltlBoolSym("b")
    original = ltlConj(a, ltlNeg(b))
    assert sympy2ltl(ltl2sympy(original)) == original


def test_negatom_strips_or_adds_negation():
    lit = ltlBoolSym("l0")
    assert negatom(ltlNeg(lit)) == lit
    assert negatom(lit) == ltlNeg(lit)


def test_getatoms_on_negated_atom():
    x = z3.Int("x")
    atom = ltlNeg(ltlZ3(x > 0))
    atoms = getatoms(atom)
    assert len(atoms) == 1
    solver = z3.Solver()
    solver.add(atoms[0] != (0 < x))
    assert solver.check() == z3.unsat


def test_getatoms_on_disjunction_recurses():
    x = z3.Int("x")
    tauto = ltlDisj(ltlNeg(ltlZ3(x > 0)), ltlZ3(x < 10))
    atoms = getatoms(tauto)
    assert len(atoms) == 2


def test_satcore_drops_redundant_disjunct_but_stays_a_tautology():
    from syntheos.formula import getliterals, ltlt2z3

    x = z3.Int("x")
    # x>0 | x<=0 is already a tautology on its own; x<-100 is a redundant
    # third disjunct (its models are a subset of x<=0's). satcore should
    # reduce this to just the unsat core (x>0, x<=0) and drop the redundant
    # atom, while the result stays logically equivalent to True.
    tauto = ltlDisj(ltlZ3(x > 0), ltlDisj(ltlZ3(x <= 0), ltlZ3(x < -100)))
    core = satcore(tauto)
    assert len(getliterals(core)) == 2
    solver = z3.Solver()
    solver.add(z3.Not(ltlt2z3(core)))
    assert solver.check() == z3.unsat
