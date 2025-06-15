import yaml
import argparse
import sys
from .config import CONFIG
from .datatypes import *
from .boolizer import Booleanizer, mapfetch
from .refinement import refinetauto
from z3 import ForAll, Exists, Solver, Implies, unsat, sat, simplify, Tactic
from .hoaparser import nodes2dot, play2str
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

def envPlayNewThTauto(envz3):
  z3envvars = z3getvars(envz3)
  envexists = quantify(Exists, z3envvars, envz3)
  if not isSat(envexists):
    return ltlNeg(z32ltlt(envz3))
  return None

def sysPlayNewThTauto(envz3, sysz3, boolizer):
  z3envvars = z3getvars(envz3)
  sysplaysymbols = z3getvars(sysz3)
  z3envvars.extend([v for v in sysplaysymbols if not boolizer.isSysVar(v.decl().name())])
  z3sysvars = [v for v in sysplaysymbols if boolizer.isSysVar(v.decl().name())]
  sysexists = quantify(Exists, z3sysvars, sysz3)
  implication = Implies(envz3, sysexists)
  sysforall = quantify(ForAll, z3envvars, implication)
  if isSat(sysforall):
    return None
  partition = Tactic('qe2')(sysexists).as_expr() # Comment this line to disable qe
  newtauto = ltlDisj(ltlNeg(z32ltlt(sysz3)), z32ltlt(partition))
  return newtauto

def theoryTauto(edge, boolizer):
  envz3 = edge.getEnvPlay()
  envtauto = envPlayNewThTauto(envz3)
  if envtauto is not None:
    if boolizer.realizable:
      return EDGEKIND.UNREACHABLE, envtauto
    return EDGEKIND.ILLEGAL, envtauto
  sysz3 = edge.getSysResponse()
  systauto = sysPlayNewThTauto(envz3, sysz3, boolizer)
  if systauto is not None:
    if boolizer.realizable:
      return EDGEKIND.ILLEGAL, systauto
    return EDGEKIND.UNREACHABLE, systauto
  return EDGEKIND.LEGAL, None

def thConsistent(edge, boolizer, nonewtautosallowed):
  edgekind, newthm = theoryTauto(edge, boolizer)
  if edgekind == EDGEKIND.ILLEGAL:
    dbg1("Found theory inconsistency")
    newthm = refinetauto(boolizer, newthm)
    if newthm is None:
      dbg1("But there was no new knowledge")
      assert(nonewtautosallowed)
    else:
      dbg2("Adding theorem:")
      dbg2(ltlt2str(newthm))
      boolizer.addTauto(newthm)
    return False
  return True

def isFetchedVar(var):
  return var.decl().name().startswith("FETCH_")

def realtmpConsistent(edges, boolizer, nonewtautosallowed):
  [e0, e1] = edges
  tpre = mapfetch(And(e0.getSysResponse(), e0.getEnvPlay()))
  e1envplay = e1.getEnvPlay()
  e1sysplay = e1.getSysResponse()
  prevars = list(dict.fromkeys(z3getvars(tpre) + [v for v in (z3getvars(e1sysplay) + z3getvars(e1envplay)) if isFetchedVar(v)]))
  e1envvars = [v for v in z3getvars(e1envplay) if not isFetchedVar(v)]
  envexists = quantify(Exists, e1envvars, e1envplay)
  # e1sysplayvars = z3getvars(e1sysplay)
  # e1envvars.extend([v for v in e1sysplayvars if not boolizer.isSysVar(v.decl().name()) and not v in prevars])
  # e1sysvars = [v for v in e1sysplayvars if boolizer.isSysVar(v.decl().name()) and not v in prevars]
  # sysexists = quantify(Exists, e1sysvars, e1sysplay)
  # implication = Implies(e1envplay, sysexists)
  # sysforall = quantify(ForAll, e1envvars, implication)
  # fullformula = quantify(ForAll, prevars, Implies(tpre, And(envexists, sysforall)))
  fullformula = quantify(ForAll, prevars, Implies(tpre, envexists))
  issat = isSat(fullformula)
  if issat:
    return True
  unfetchedvars = [var for var in z3getvars(e1envplay) if not isFetchedVar(var)]
  fetchexpr = Tactic('qe2')(quantify(Exists, unfetchedvars, e1envplay)).as_expr()
  renamed_expr = substitute(fetchexpr, [(var, z3.Const(var.decl().name()[6:], var.sort())) for var in z3util.get_vars(fetchexpr)])
  missingTautos = boolizer.missingTautos(renamed_expr)
  if (missingTautos):
    dbg2("Adding tmp tautos:")
    for t in missingTautos:
      dbg2(z32str(t))
      boolizer.createtmpassumptionfor(t)
  else:
    dbg2("No new temporal tautos")
    assert(nonewtautosallowed)
  return False

def dbgedgeprint(i,nodesn):
  sys.stdout.write('\r')
  sys.stdout.write(f"Checking edge {i}/{nodesn}. ")
  sys.stdout.flush()

def checkconsistencywith(edges, boolizer, consf):
  nodesn = len(edges)
  i = 0
  inconsistencies = 0
  allconsistent = True
  for edge in edges:
    i = i+1
    dbg1(lambda: dbgedgeprint(i,nodesn))
    edgeconsistent = consf(edge, boolizer, inconsistencies > 0)
    if not edgeconsistent:
      inconsistencies += 1
      allconsistent = False
    if inconsistencies > CONFIG.inconsistent_edges_tolerance:
      return False
  return allconsistent

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
  parser.add_argument('--inconsistent-edges-tolerance', help='Maximum illegal edges tolerance', type=int, default=0)
  return parser.parse_args()

def initialize_boolizer(specdata):
  variables = specdata["variables"]
  boolizer = Booleanizer(variables)
  boolizer.setformula(ltltparse(specdata["property"], variables))
  for tmptauto in specdata["tmptautos"]:
    tautoform = bparse(tmptauto, variables)
    boolizer.createtmpassumptionfor(getZ3(tautoform))
  return boolizer

def cegres(boolizer):
  consistent = False
  nodes = None
  while not consistent:
    nodes = callstrix(boolizer)
    dbg3(lambda: print(nodes2dot(nodes)))
    edges = [edge for node in nodes for edge in node.edges]
    consedges = [[edge, consedge] for node in nodes for edge in node.edges for consedge in edge.outnode.edges]
    consistent = (
        checkconsistencywith(edges, boolizer, thConsistent) and
        (boolizer.maxfetchdepth == 0 or boolizer.realizable or
          checkconsistencywith(consedges, boolizer, realtmpConsistent))
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
  CONFIG.inconsistent_edges_tolerance = args.inconsistent_edges_tolerance
  setdbglevel(args.dbglevel)
  specdata = readfromyaml(args.yaml)
  reporter = Reporter(specdata, args.reportdir)
  CONFIG.reporter = reporter
  CONFIG.strixmaxsecs = args.strixmaxsecs
  boolizer = initialize_boolizer(specdata)
  nodes = cegres(boolizer)
  print("Done. The property is %s." % ("realizable" if boolizer.realizable else "unrealizable"))
  showorsave_mealy(args, nodes, specdata)
