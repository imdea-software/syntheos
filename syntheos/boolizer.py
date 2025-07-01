from .datatypes import *
# from .maybenotz3 import *
from . import maybenotz3 as mnz3
from functools import reduce
import copy

def copy_and_fetch(var):
  return mnz3.copy_and_rename(var, lambda x : "FETCH_" + x)

def mapfetch(lit):
  if mnz3.isz3const(lit):
    return lit
  if mnz3.isz3var(lit):
    return copy_and_fetch(lit)
  new_args = [mapfetch(arg) for arg in lit.children()]
  return lit.decl()(*new_args)

def makeconj(l):
  if len(l) == 0:
    return None
  return reduce(lambda x,y: ltlConj(x, y), l)

class Booleanizer:
  def __init__(self, variables):
    self.sysvars = [v["name"] for v in variables if v["owner"] == "system"]
    self.littable = {}
    self.guarantees = []
    self.assumptions = []
    self.fetchtautos = []
    self.booltautos = []
    self.formula = None
    self.realizable = None

  def isSysVar(self, v):
    return v in self.sysvars

  def containssysvars(self,formula):
    return any([self.isSysVar(v.decl().name()) for v in z3getvars(formula)])

  def addTauto(self, formula):
    if isZ3(formula):
      f = getZ3(formula)
      if mnz3.is_true(f):
        return
    self.booltautos.append(self.boolize(formula))
    z3form = ltlt2z3(formula)
    z3vars = z3getvars(z3form)
    forallformula = mnz3.make_forall(z3vars, z3form)
    if not mnz3.isSat(forallformula):
      error("Not a tautology")
    if self.containssysvars(z3form):
      self.addguarantee(ltlG(formula))
    else:
      self.addassumption(ltlG(formula))

  def setformula(self, formula):
    self.formula = self.boolize(formula)
    self.maxfetchdepth = max(map((lambda kv: fetchdepth(kv[0])), self.littable.values()))

  def genericadd(self, ls, formula):
    boolform = self.boolize(formula)
    for g in ls:
      if g == boolform:
        return
    ls.append(boolform)

  def addguarantee(self, formula):
    self.genericadd(self.guarantees, formula)

  def addassumption(self, formula):
    self.genericadd(self.assumptions, formula)

  def boolize(self, formula):
    if isBoolSymTrue(formula) or isBoolSymFalse(formula):
      return formula
    if isBoolSym(formula):
      error("Bool symbol in full expression: " + str(formula))
    if isZ3(formula):
      return self.getliteral(getZ3(formula))
    ret = copy.deepcopy(formula)
    ret["operators"] = list(map(lambda f: self.boolize(f), ret["operators"]))
    return ret

  def literalexists(self,th):
    return self.mgetliteral(th) is not None

  def mgetliteral(self,th):
    assert not mnz3.is_true(th)
    assert not mnz3.is_false(th)
    for l,[f,_] in self.littable.items():
      if th==f:
        return ltlBoolSym(l)

  def getliteral(self,th):
    mliteral = self.mgetliteral(th)
    if mliteral is not None:
      return mliteral
    newlid = "l"+str(len(self.littable))
    kind = LITTY.SYS if self.containssysvars(th) else LITTY.ENV
    self.littable[newlid] = [th,kind]
    return ltlBoolSym(newlid)

  def tautoExists(self, formula):
    fetchformula = mapfetch(formula)
    mliteral = self.mgetliteral(formula)
    mfliteral = self.mgetliteral(fetchformula)
    if mliteral is None or mfliteral is None:
      return False
    tauto = ltlG(ltlIff(mliteral,ltlX(mfliteral)))
    return tauto in self.fetchtautos

  def createTauto(self, formula):
    fetchformula = mapfetch(formula)
    literal = self.getliteral(formula)
    fliteral = self.getliteral(fetchformula)
    return ltlG(ltlIff(literal,ltlX(fliteral)))

  def missingTautos(self, formula):
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
