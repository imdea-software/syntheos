from sympy import *
from sympy.logic.boolalg import *
from datatypes import ltlt2str, ltl2sympy, error, dbg2
from sympy.logic.inference import satisfiable
from itertools import chain

def ourdistribute(expr):
  if isinstance(expr, Or):
    for arg in expr.args:
      if isinstance(arg, And):
        conj = arg
        break
    else:
      return [expr]
    rest = Or(*[a for a in expr.args if a is not conj])
    return (b for c in conj.args for b in ourdistribute(Or(c,rest)))
  elif isinstance(expr, And):
    return chain(*map(ourdistribute, expr.args))
  return [expr]

def isnewknowledge(sympyknowledge, tauto):
  ret = satisfiable(~tauto & sympyknowledge)
  return ret

def getnewknowledge(booltautos, expr):
  sympyknowledge = And(*(map(ltl2sympy, booltautos)))
  expr = sympify(expr)
  expr = eliminate_implications(expr)
  tautos = ourdistribute(expr)
  dbgcnt = 0
  for tauto in tautos:
    dbgcnt += 1
    if dbgcnt > 10000:
      dbg2(f"Checking tauto {dbgcnt}")
      dbg2(tauto)
    if isnewknowledge(sympyknowledge, tauto):
      return tauto
  error("No new knowledge?")
