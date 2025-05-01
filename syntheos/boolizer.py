from .datatypes import *
from z3 import *
from functools import reduce
import copy

def copy_and_fetch(var):
  new_name = "FETCH_" + var.decl().name()
  if isinstance(var, IntNumRef) or isinstance(var, ArithRef):  # Int or Real
      return Int(new_name) if var.is_int() else Real(new_name)
  elif isinstance(var, BoolRef):  # Boolean
      return Bool(new_name)
  elif isinstance(var, BitVecRef):  # Bit-vector
      return BitVec(new_name, var.size())
  else:
      raise TypeError("Unsupported Z3 variable type")

def mapfetch(lit):
  if isz3const(lit):
    return lit
  if isz3var(lit):
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
      if is_true(f):
        return
    self.booltautos.append(self.boolize(formula))
    z3form = ltlt2z3(formula)
    z3vars = z3getvars(z3form)
    forallformula = quantify(ForAll, z3vars, z3form)
    solver = Solver()
    solver.add(forallformula)
    if solver.check() == unsat:
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

  def getliteral(self,th):
    assert not is_true(th)
    assert not is_false(th)
    for l,[f,_] in self.littable.items():
      if th==f:
        return ltlBoolSym(l)
    newlid = "l"+str(len(self.littable))
    kind = LITTY.SYS if self.containssysvars(th) else LITTY.ENV
    self.littable[newlid] = [th,kind]
    return ltlBoolSym(newlid)


  def createtmpassumptionfor(self, formula):
    if is_true(formula):
      return False
    ret = False
    for l in getliterals(z32ltlt(formula)):
      ret = ret or self.createtmpassumptionfornormalized(l)
    return ret

  def createtmpassumptionfornormalized(self, formula):
    literal = self.getliteral(formula)
    fetchformula = mapfetch(formula)
    fetchliteral = self.getliteral(fetchformula)
    newtauto = ltlG(ltlIff(literal,ltlX(fetchliteral)))
    for ft in self.fetchtautos:
      if ft==newtauto:
        return False
    self.fetchtautos.append(newtauto)
    return True

  def getboolformula(self):
    assumption = makeconj(self.assumptions)
    guarantee = makeconj(self.guarantees)
    fetchtauto = makeconj(self.fetchtautos)
    formula = self.formula
    formula = formula if fetchtauto is None else ltlImplies(fetchtauto, formula)
    formula = formula if guarantee is None else ltlConj(guarantee, formula)
    formula = formula if assumption is None else ltlImplies(assumption, formula)
    return formula
