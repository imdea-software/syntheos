"""The Booleanizer abstracts theory atoms (Z3 expressions) into fresh
propositional literals, so the resulting purely-Boolean LTL formula can be
handed to a plain LTL synthesis backend (Strix/SeMLL). It also tracks the
guarantee/assumption tautologies discovered by the CEGAR refinement loop in
`refinement.py`, and the "fetch tautologies" (temporal consistency facts
about `y(...)`-fetched literals) added by `cegar.py`.
"""

import copy
from enum import Enum, auto
from functools import reduce

from . import z3_support as mnz3
from .errors import SyntheosError
from .formula import (
    fetchdepth,
    getZ3,
    getliterals,
    isBoolSym,
    isBoolSymFalse,
    isBoolSymTrue,
    isZ3,
    ltlBoolSym,
    ltlConj,
    ltlG,
    ltlIff,
    ltlImplies,
    ltlX,
    ltlt2z3,
    z32ltlt,
    z3getvars,
)


class LITTY(Enum):
    SYS = auto()
    ENV = auto()


def copy_and_fetch(var):
    return mnz3.copy_and_rename(var, lambda x: "FETCH_" + x)


def mapfetch(lit):
    """Replace every variable in a Z3 term with its FETCH_-prefixed (previous
    value) counterpart."""
    if mnz3.isz3const(lit):
        return lit
    if mnz3.isz3var(lit):
        return copy_and_fetch(lit)
    return lit.decl()(*(mapfetch(arg) for arg in lit.children()))


def makeconj(formulas: list):
    if len(formulas) == 0:
        return None
    return reduce(ltlConj, formulas)


class Booleanizer:
    def __init__(self, variables: list):
        self.sysvars = [v["name"] for v in variables if v["owner"] == "system"]
        self.littable: dict = {}
        self.guarantees: list = []
        self.assumptions: list = []
        self.fetchtautos: list = []
        self.booltautos: list = []
        self.formula = None
        self.realizable = None

    def isSysVar(self, v: str) -> bool:
        return v in self.sysvars

    def containssysvars(self, formula) -> bool:
        return any(self.isSysVar(v.decl().name()) for v in z3getvars(formula))

    def addTauto(self, formula):
        """Record a newly-discovered tautology as a guarantee (if it mentions
        system variables) or an assumption (otherwise), and remember its
        Boolean-literal form for the sympy tautology search."""
        if isZ3(formula):
            f = getZ3(formula)
            if mnz3.is_true(f):
                return
        self.booltautos.append(self.boolize(formula))
        z3form = ltlt2z3(formula)
        z3vars = z3getvars(z3form)
        forallformula = mnz3.make_forall(z3vars, z3form)
        if not mnz3.isSat(forallformula):
            raise SyntheosError("Not a tautology")
        if self.containssysvars(z3form):
            self.addguarantee(ltlG(formula))
        else:
            self.addassumption(ltlG(formula))

    def setformula(self, formula):
        self.formula = self.boolize(formula)
        self.maxfetchdepth = max(fetchdepth(th) for th, _kind in self.littable.values())

    def genericadd(self, target_list: list, formula):
        boolform = self.boolize(formula)
        if boolform in target_list:
            return
        target_list.append(boolform)

    def addguarantee(self, formula):
        self.genericadd(self.guarantees, formula)

    def addassumption(self, formula):
        self.genericadd(self.assumptions, formula)

    def boolize(self, formula):
        """Recursively replace every Z3 theory atom in `formula` with its
        (fresh, or previously assigned) Boolean literal."""
        if isBoolSymTrue(formula) or isBoolSymFalse(formula):
            return formula
        if isBoolSym(formula):
            raise SyntheosError("Bool symbol in full expression: " + str(formula))
        if isZ3(formula):
            return self.getliteral(getZ3(formula))
        ret = copy.deepcopy(formula)
        ret["operators"] = [self.boolize(op) for op in ret["operators"]]
        return ret

    def literalexists(self, th) -> bool:
        return self.mgetliteral(th) is not None

    def mgetliteral(self, th):
        assert not mnz3.is_true(th)
        assert not mnz3.is_false(th)
        for name, [f, _] in self.littable.items():
            if th == f:
                return ltlBoolSym(name)
        return None

    def getliteral(self, th):
        mliteral = self.mgetliteral(th)
        if mliteral is not None:
            return mliteral
        newlid = "l" + str(len(self.littable))
        kind = LITTY.SYS if self.containssysvars(th) else LITTY.ENV
        self.littable[newlid] = [th, kind]
        return ltlBoolSym(newlid)

    def tautoExists(self, formula) -> bool:
        fetchformula = mapfetch(formula)
        mliteral = self.mgetliteral(formula)
        mfliteral = self.mgetliteral(fetchformula)
        if mliteral is None or mfliteral is None:
            return False
        tauto = ltlG(ltlIff(mliteral, ltlX(mfliteral)))
        return tauto in self.fetchtautos

    def createTauto(self, formula):
        fetchformula = mapfetch(formula)
        literal = self.getliteral(formula)
        fliteral = self.getliteral(fetchformula)
        return ltlG(ltlIff(literal, ltlX(fliteral)))

    def missingTautos(self, formula) -> list:
        if mnz3.is_true(formula):
            return []
        return [l for l in getliterals(z32ltlt(formula)) if not self.tautoExists(l)]

    def createtmpassumptionfor(self, th):
        self.fetchtautos.append(self.createTauto(th))

    def getboolformula(self):
        assumption = makeconj(self.assumptions)
        guarantee = makeconj(self.guarantees)
        fetchtauto = makeconj(self.fetchtautos)
        formula = self.formula
        formula = formula if fetchtauto is None else ltlImplies(fetchtauto, formula)
        formula = formula if guarantee is None else ltlConj(guarantee, formula)
        formula = formula if assumption is None else ltlImplies(assumption, formula)
        return formula
