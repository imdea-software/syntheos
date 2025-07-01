from enum import Enum,auto
import traceback
import sys
import sympy
from functools import reduce
import re
from . import maybenotz3 as mnz3
import copy

dbglevel = 0
def setdbglevel(n):
  global dbglevel
  dbglevel = n

def dbg1(s):
  dbg(s,1)
def dbg2(s):
  dbg(s,2)
def dbg3(s):
  dbg(s,3)
def dbg(s,i):
  if dbglevel>=i:
    msg = s
    if callable(s):
      s()
      return
    print(msg)

class EDGEKIND(Enum):
  LEGAL = auto()
  ILLEGAL = auto()
  UNREACHABLE = auto()

class LITTY(Enum):
  SYS = auto()
  ENV = auto()

def error(s):
  traceback.print_stack() 
  print("ERROR:")
  print(s)
  exit(-1)

def fetchdepth(lit):
  if mnz3.isz3var(lit):
    x = lit.decl().name()
    i=0
    while x.startswith("FETCH_"):
      i = i+1
      x = x[6:]
    return i
  if mnz3.isz3const(lit):
    return 0
  return max([fetchdepth(c) for c in lit.children()])

def replaceliterals(formula, transtab):
  if isBoolSym(formula):
    if isBoolSymTrue(formula) or isBoolSymFalse(formula):
      return formula
    return transtab[symbol(formula)]
  if isZ3(formula):
    error("Theory element while replacing literals")
  ret = copy.deepcopy(formula)
  ret["operators"] = list(map(lambda f: replaceliterals(f, transtab), ret["operators"]))
  return ret

def isconstant(v):
  return v.lstrip("-").isdigit();

def z3getvars(e):
  def getset(e):
    if mnz3.isz3var(e):
      return {e}
    if mnz3.isz3const(e):
      return set()
    return reduce(lambda x,y: x.union(getset(y)), e.children(), set())
  return list(getset(e))

def ltlt2str(f):
  if isBoolSym(f):
    if isBoolSymTrue(f):
      return "t"
    if isBoolSymFalse(f):
      return "f"
    return symbol(f)
  if isZ3(f):
    return "[" + mnz3.z32str(getZ3(f)) + "]"
  if len(f["operators"]) == 1:
    return f["kind"] + "(" + ltlt2str(f["operators"][0]) + ")"
  if len(f["operators"]) == 2:
    return "(" + ltlt2str(f["operators"][0]) + " " + f["kind"] + " " + ltlt2str(f["operators"][1]) + ")"

def symbol(l):
  assert isBoolSym(l)
  return l["operators"][0]

def getZ3(l):
  assert isZ3(l)
  return l["operators"][0]

def ltlt2z3(f):
  if isBoolSym(f):
    if isBoolSymTrue(f):
      return mnz3.BoolVal(True)
    if isBoolSymFalse(f):
      return mnz3.BoolVal(False)
    error("Non constant bool symbol converting to z3")
  if isZ3(f):
    th = f["operators"][0]
    newexpr = z32ltlt(getZ3(f))
    if isZ3(newexpr):
      return getZ3(newexpr)
    return ltlt2z3(newexpr)
  z3funs = {
      "!": mnz3.Not,
      "&": mnz3.And,
      "|": mnz3.Or,
  }
  return z3funs[f["kind"]](*(list(map(ltlt2z3, f["operators"]))))

def getliterals(formula):
  if isBoolSymTrue(formula) or isBoolSymFalse(formula):
    return []
  if isBoolSym(formula):
    error("Bool symbol in full expression: " + str(e))
  if isZ3(formula):
    return [getZ3(formula)]
  return reduce(lambda x,y: x + getliterals(y), formula["operators"], [])

def isBoolSym(formula):
  return formula["kind"] == "BOOLSYM"

def isBoolSymTrue(formula):
  return isBoolSym(formula) and symbol(formula) == "t"

def isBoolSymFalse(formula):
  return isBoolSym(formula) and symbol(formula) == "f"

def isZ3(formula):
  return formula["kind"] == "Z3"

def ltl2sympy(formula):
  if isBoolSym(formula):
    sym = symbol(formula)
    return sympy.Symbol(sym)
  sympyfuns = {
      "!": sympy.Not,
      "&": sympy.And,
      "|": sympy.Or,
  }
  return sympyfuns[formula["kind"]](*(list(map(ltl2sympy, formula["operators"]))))

def createLTLExpr(k, op):
  return {"kind": k, "operators": op}

def ltlConj(a,b):
  return createLTLExpr("&", [a,b])

def ltlDisj(a,b):
  return createLTLExpr("|", [a,b])

def ltlZ3(a):
  return createLTLExpr("Z3", [a])

def ltlNeg(a):
  return createLTLExpr("!", [a])

def ltlImplies(a,b):
  return createLTLExpr("->", [a,b])

def ltlIff(a,b):
  return createLTLExpr("<->", [a,b])

def ltlG(a):
  return createLTLExpr("G", [a])

def ltlX(a):
  return createLTLExpr("X", [a])

def ltlBoolSym(a):
  return createLTLExpr("BOOLSYM", [a])

def z32ltlt(f):
  funs = {
      "negator": ltlNeg,
      "conjunctor": ltlConj,
      "disjunctor": ltlDisj,
      "thwrapper": ltlZ3,
      "constTrue": ltlBoolSym('t'),
      "constFalse": ltlBoolSym('f'),
  }
  return mnz3.z32ltltw(f, funs)

def getz3vars(identifiers, variables):
  varstable = {v["name"]:v["type"] for v in variables}
  def findtype(x):
    while x.startswith("FETCH_"):
      x = x[6:]
    return varstable[x]
  return {key: mnz3.makevar(key, findtype(key)) for key in identifiers}
