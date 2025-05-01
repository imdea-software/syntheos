from enum import Enum,auto
import traceback
from z3 import *
import sympy
from functools import reduce
import re

dbglevel = 1
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

class LITTY(Enum):
  SYS = auto()
  ENV = auto()

def error(s):
  traceback.print_stack() 
  print("ERROR:")
  print(s)
  exit(-1)

def fetchdepth(lit):
  if isz3var(lit):
    x = lit.decl().name()
    i=0
    while x.startswith("FETCH_"):
      i = i+1
      x = x[6:]
    return i
  if isz3const(lit):
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

def quantify(quantifier, varlist, formula):
  if varlist:
    return quantifier(varlist, formula)
  return formula

def isz3var(e):
  return is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED

def isz3const(e):
  return not isz3var(e) and (is_int_value(e) or is_rational_value(e) or is_true(e) or is_false(e))

def z3getvars(e):
  def getset(e):
    if isz3var(e):
      return {e}
    if isz3const(e):
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
    return "[" + str(getZ3(f)) + "]"
  if len(f["operators"]) == 1:
    return f["kind"] + "(" + ltlt2str(f["operators"][0]) + ")"
  if len(f["operators"]) == 2:
    return "(" + ltlt2str(f["operators"][0]) + " " + f["kind"] + " " + ltlt2str(f["operators"][1]) + ")"

def z32str(expr, parent_op=None):
  if is_and(expr):
    conjunction_str = " ∧ ".join(z32str(arg, 'And') for arg in expr.children())
    return f"({conjunction_str})" if parent_op == 'Or' else conjunction_str
  elif is_or(expr):
    disjunction_str = " ∨ ".join(z32str(arg, 'Or') for arg in expr.children())
    return f"({disjunction_str})" if parent_op == 'And' else disjunction_str
  elif is_not(expr):
    negated_expr = z32str(expr.arg(0), 'Not')
    return f"¬({negated_expr})"
  elif expr.decl().kind() == Z3_OP_LE:
    return f"{expr.arg(0)} ≤ {expr.arg(1)}"
  elif expr.decl().kind() == Z3_OP_LT:
    return f"{expr.arg(0)} < {expr.arg(1)}"
  elif expr.decl().kind() == Z3_OP_GE:
    return f"{expr.arg(0)} ≥ {expr.arg(1)}"
  elif expr.decl().kind() == Z3_OP_GT:
    return f"{expr.arg(0)} > {expr.arg(1)}"
  elif expr.decl().kind() == Z3_OP_EQ:
    return f"{expr.arg(0)} = {expr.arg(1)}"
  else:
    return str(expr)

def symbol(l):
  assert isBoolSym(l)
  return l["operators"][0]

def getZ3(l):
  assert isZ3(l)
  return l["operators"][0]

def ltlt2z3(f):
  if isBoolSym(f):
    if isBoolSymTrue(f):
      return BoolVal(True)
    if isBoolSymFalse(f):
      return BoolVal(False)
    error("Non constant bool symbol converting to z3")
  if isZ3(f):
    th = f["operators"][0]
    newexpr = z32ltlt(getZ3(f))
    if isZ3(newexpr):
      return getZ3(newexpr)
    return ltlt2z3(newexpr)
  z3funs = {
      "!": Not,
      "&": And,
      "|": Or,
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
  if is_and(f):
    ret = z32ltlt(f.children()[0])
    for ch in f.children()[1:]:
      ret = ltlConj(ret, z32ltlt(ch))
    return ret;
  if is_or(f):
    ret = z32ltlt(f.children()[0])
    for ch in f.children()[1:]:
      ret = ltlDisj(ret, z32ltlt(ch))
    return ret;
  if is_not(f):
    ret = ltlNeg(z32ltlt(f.children()[0]))
    return ret;
  if is_ge(f):
    return ltlNeg(ltlZ3(f.children()[0].__lt__(f.children()[1])))
  if is_gt(f):
    return ltlZ3(f.children()[1].__lt__(f.children()[0]))
  if is_le(f):
    return ltlNeg(ltlZ3(f.children()[1].__lt__(f.children()[0])))
  if is_eq(f):
    return ltlConj(ltlNeg(ltlZ3(f.children()[1].__lt__(f.children()[0]))), ltlNeg(ltlZ3(f.children()[0].__lt__(f.children()[1]))))
  if is_false(f):
    return ltlBoolSym('f')
  if is_true(f):
    return ltlBoolSym('t')
  if is_quantifier:
    return ltlZ3(f)
  error("Unhandled case:" + str(f))

def getz3vars(das, variables):
  varstable = {v["name"]:v["type"] for v in variables}
  def makevar(x):
    orix = x
    while x.startswith("FETCH_"):
      x = x[6:]
    match varstable[x]:
      case "Int":
        cons = Int
      case "Real":
        cons = Real
      case _:
        error("Unhandled type: " + varstable[x])
    return cons(orix)
  idregex = r"\b[a-zA-Z][a-zA-Z0-9_]*\b"
  identifiers = re.findall(idregex, das)
  return {key: makevar(key) for key in identifiers}
