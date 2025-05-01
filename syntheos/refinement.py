from .datatypes import *
from sympy import Symbol, srepr, Not, And, Or, false, true
from .oursympy import getnewknowledge
from functools import reduce
from itertools import chain

def sympy2ltl(e):
  if len(e.args)==0:
    if e == true:
      name = 't'
    elif e == false:
      name = 'f'
    else:
      name = e.name
    return ltlBoolSym(name)
  newargs = map(sympy2ltl, e.args)
  if e.func == Not:
    return ltlNeg(*newargs)
  if e.func == Or:
    return reduce(ltlDisj, newargs)
  if e.func == And:
    return reduce(ltlConj, newargs)
  error("Unhandled case:" + str(e))

def refinetauto(boolizer, ltlform):
  sympyform = ltl2sympy(boolizer.boolize(ltlform))
  tauto = sympy2ltl(getnewknowledge(boolizer.booltautos, sympyform))
  transtab = {k:ltlZ3(v) for [k,[v,_]] in boolizer.littable.items()}
  play = replaceliterals(tauto, transtab)
  return satcore(play)

def getatoms(tauto):
  if tauto["kind"] == "!":
    f = tauto["operators"][0]
    return [ltlt2z3(f)]
  if tauto["kind"] == "|":
    return [x for op in tauto["operators"] for x in getatoms(op)]
  return [ltlt2z3(ltlNeg(tauto))]

def negatom(atom):
  if atom["kind"] == "!":
    return atom["operators"][0]
  return ltlNeg(atom)

def satcore(tauto):
  atoms = getatoms(tauto)
  s = Solver()
  s.set(unsat_core=True)
  enumatoms = list(enumerate(atoms))
  for i, atom in enumatoms:
    s.assert_and_track(atom, 'atom_'+str(i))
  result = s.check()
  assert result == unsat
  c = s.unsat_core()
  return reduce(ltlDisj, [negatom(z32ltlt(atom)) for i,atom in enumatoms if Bool('atom_'+str(i)) in c])
