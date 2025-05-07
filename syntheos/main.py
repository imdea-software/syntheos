import yaml
import argparse
import sys
from .datatypes import *
from .boolizer import Booleanizer
from .refinement import refinetauto
from z3 import ForAll, Exists, Solver, Implies, unsat, sat, simplify, Tactic
from .hoaparser import nodes2dot
from .reporter import Reporter
from .specreader import readfromyaml
from .strixcaller import callstrix
from .ltltparser import ltltparse

sys.setrecursionlimit(10000)

def isSat(formula):
  formula = simplify(formula)
  solver = Solver()
  solver.add(formula)
  satres = solver.check()
  if satres == sat:
    return True
  if satres == unsat:
    return False
  error("Unkown satisfiability")

def theoryTauto(edge, boolizer):
  envz3 = edge.getEnvPlay()
  z3envvars = z3getvars(envz3)
  envexists = quantify(Exists, z3envvars, envz3)
  if not isSat(envexists):
    if not boolizer.realizable:
      newtauto = ltlNeg(z32ltlt(envz3))
      return newtauto
    return None
  if not boolizer.realizable:
    return None
  sysz3 = edge.getSysResponse()
  sysplaysymbols = z3getvars(sysz3)
  z3envvars.extend([v for v in sysplaysymbols if not boolizer.isSysVar(v.decl().name())])
  z3sysvars = [v for v in sysplaysymbols if boolizer.isSysVar(v.decl().name())]
  sysexists = quantify(Exists, z3sysvars, sysz3)
  implication = Implies(envz3, sysexists)
  sysforall = quantify(ForAll, z3envvars, implication)
  if isSat(sysforall):
    return None
  partition = quantify(Exists, z3sysvars, sysz3)
  partition = Tactic('qe2')(partition).as_expr() # Comment this line to disable qe
  newtauto = ltlDisj(ltlNeg(z32ltlt(sysz3)), z32ltlt(partition))
  return newtauto

def thConsistent(edge, boolizer):
  newthm = theoryTauto(edge, boolizer)
  if newthm is not None:
    newthm = refinetauto(boolizer, newthm)
    dbg1("Found theory inconsistency")
    dbg2("Adding theorem:")
    dbg2(ltlt2str(newthm))
    boolizer.addTauto(newthm)
    return False
  return True

def tmpConsistent(edge, boolizer):
  envplay = edge.getEnvPlay()
  unfetchedvars = [var for var in z3getvars(envplay) if not var.decl().name().startswith("FETCH_")]
  fetchexpr = Tactic('qe2')(quantify(Exists, unfetchedvars, envplay)).as_expr()
  renamed_expr = substitute(fetchexpr, [(var, z3.Const(var.decl().name()[6:], var.sort())) for var in z3util.get_vars(fetchexpr)])
  literals = getliterals(z32ltlt(renamed_expr))
  newliterals = [y for y in literals if boolizer.createtmpassumptionfor(y)]
  if len(newliterals) > 0:
    dbg1("Found temporal inconsistency")
    dbg2("Adding tmp assumptions for literals:")
    dbg2(literals)
    return False
  return True

def dbgedgeprint(i,nodesn):
  sys.stdout.write('\r')
  sys.stdout.write(f"Checking edge {i}/{nodesn}. ")
  sys.stdout.flush()

def checkconsistencywith(edges, boolizer, consf):
  nodesn = len(edges)
  i = 0
  for edge in edges:
    i = i+1
    dbg1(lambda: dbgedgeprint(i,nodesn))
    if not consf(edge, boolizer):
      return False
  return True

def writemealy(mealyfname, nodes, specdata):
  specdata["transtab"] = {k: getZ3(v).sexpr() for k, v in nodes[0].edges[0].transtab.items()}
  specdata["nodes"] = [[{"envplay": ltlt2str(edge.envplay), "sysplay": ltlt2str(edge.sysplay), "outnoden": edge.outnoden} for edge in node.edges] for node in nodes]
  with open(mealyfname, "w") as f:
    yaml.dump(specdata, f, default_flow_style=False, sort_keys=False)

def parse_arguments():
  parser = argparse.ArgumentParser('LTL fetch')
  parser.add_argument('--yaml', help='YAML with specification', type=str, default=None)
  parser.add_argument('--dbglevel', help='Debug level', type=int, default=0)
  parser.add_argument('--strixmaxsecs', help='Maximum seconds', type=int, default=None)
  parser.add_argument('--reportdir', help='Reports root dir', type=str, default="")
  parser.add_argument('--save-mealy', nargs="?", const="", help='Save mealy machine to file', type=str, default=None)
  parser.add_argument("--show-mealy", action="store_true", help='Show mealy machine')
  return parser.parse_args()

def initialize_boolizer(specdata):
  variables = specdata["variables"]
  boolizer = Booleanizer(variables)
  boolizer.setformula(ltltparse(specdata["property"], variables))
  return boolizer

def cegres(boolizer, reporter, strixmaxsecs):
  consistent = False
  nodes = None
  while not consistent:
    nodes = callstrix(boolizer, reporter, strixmaxsecs)
    dbg3(lambda: print(nodes2dot(nodes)))
    edges = [edge for node in nodes for edge in node.edges]
    consistent = (
        checkconsistencywith(edges, boolizer, thConsistent) and
        (boolizer.maxfetchdepth == 0 or boolizer.realizable or
          checkconsistencywith(edges, boolizer, tmpConsistent))
    )
  return nodes

def showorsave_mealy(args, nodes, specdata):
  if args.show_mealy:
    print("Mealy machine:")
    print(nodes2dot(nodes))
  if args.save_mealy is not None:
    mealyfname = args.save_mealy if args.save_mealy != "" else (specdata["name"] + ".json")
    dbg1("Writing mealy to " + mealyfname)
    writemealy(mealyfname, nodes, specdata)

def main():
  args = parse_arguments()
  setdbglevel(args.dbglevel)
  specdata = readfromyaml(args.yaml)
  reporter = Reporter(specdata, args.reportdir)
  boolizer = initialize_boolizer(specdata)
  nodes = cegres(boolizer, reporter, args.strixmaxsecs)
  print("Done. The property is %s." % ("realizable" if boolizer.realizable else "unrealizable"))
  showorsave_mealy(args, nodes, specdata)
