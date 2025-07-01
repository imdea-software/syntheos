import yaml
import argparse
import sys
from .config import CONFIG
from .datatypes import *
from .boolizer import Booleanizer, mapfetch
from .refinement import refinetauto
from . import maybenotz3 as mnz3
from .hoaparser import nodes2dot, play2str
from .reporter import Reporter
from .specreader import readfromyaml
from .strixcaller import callstrix
from .ltltparser import ltltparse

sys.setrecursionlimit(10000)

def envPlayNewThTauto(envz3):
  z3envvars = z3getvars(envz3)
  envexists = mnz3.make_exists(z3envvars, envz3)
  if not mnz3.isSat(envexists):
    return ltlNeg(z32ltlt(envz3))
  return None

def sysPlayNewThTauto(envz3, sysz3, boolizer):
  z3envvars = z3getvars(envz3)
  sysplaysymbols = z3getvars(sysz3)
  z3envvars.extend([v for v in sysplaysymbols if not boolizer.isSysVar(v.decl().name())])
  z3sysvars = [v for v in sysplaysymbols if boolizer.isSysVar(v.decl().name())]
  sysexists = mnz3.make_exists(z3sysvars, sysz3)
  implication = mnz3.thImplies(envz3, sysexists)
  sysforall = mnz3.make_forall(z3envvars, implication)
  if mnz3.isSat(sysforall):
    return None
  partition = mnz3.eliminate_quantifier(sysexists)
  newtauto = ltlDisj(ltlNeg(z32ltlt(sysz3)), z32ltlt(partition))
  return newtauto

def theoryTauto(edge, boolizer):
  envz3 = edge.getEnvPlay()
  envtauto = envPlayNewThTauto(envz3)
  if envtauto is not None:
    return (EDGEKIND.UNREACHABLE if boolizer.realizable else EDGEKIND.ILLEGAL, envtauto)
  sysz3 = edge.getSysResponse()
  systauto = sysPlayNewThTauto(envz3, sysz3, boolizer)
  if systauto is not None:
    return (EDGEKIND.ILLEGAL if boolizer.realizable else EDGEKIND.UNREACHABLE, systauto)
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

def tmpConsistent(edges, boolizer, nonewtautosallowed):
  e0, e1 = edges
  tpre = mapfetch(mnz3.And(e0.getSysResponse(), e0.getEnvPlay()))
  e1envplay = e1.getEnvPlay()
  e1sysplay = e1.getSysResponse()
  prevars = list(dict.fromkeys(z3getvars(tpre) + [v for v in (z3getvars(e1sysplay) + z3getvars(e1envplay)) if isFetchedVar(v)]))
  e1envvars = [v for v in z3getvars(e1envplay) if not isFetchedVar(v)]
  envexists = mnz3.make_exists(e1envvars, e1envplay)
  fullformula = mnz3.make_forall(prevars, mnz3.thImplies(tpre, envexists))
  if mnz3.isSat(fullformula):
    return True
  dbg1("Found temporal inconsistency")
  unfetchedvars = [var for var in z3getvars(e1envplay) if not isFetchedVar(var)]
  fetchexpr = mnz3.eliminate_quantifier(mnz3.make_exists(unfetchedvars, e1envplay))
  renamed_expr = mnz3.rename_vars(fetchexpr, lambda x: x[6:])
  missingTautos = boolizer.missingTautos(renamed_expr)
  if (missingTautos):
    dbg2("Adding tmp tautos:")
    for t in missingTautos:
      dbg2(mnz3.z32str(t))
      boolizer.createtmpassumptionfor(t)
  else:
    dbg2("No new temporal tautos")
    assert(nonewtautosallowed)
  return False

def dbgedgeprint(i,nodesn):
  sys.stdout.write('\r')
  sys.stdout.write(f"Checking edge {i}/{nodesn}. ")
  sys.stdout.flush()

def checkconsistencywith(edges, boolizer, consf, inconsistencies = 0):
  # You can provide a value for inconsistencies (and return it)
  # if you want to share the inconsistencies checker between the temporal
  # and the theories checker.
  # You will also have to handle the boolean short-circuit.
  nodesn = len(edges)
  allconsistent = True
  for idx, edge in enumerate(edges, 1):
    dbg1(lambda: dbgedgeprint(idx,nodesn))
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
  while True:
    nodes = callstrix(boolizer)
    dbg3(lambda: print(nodes2dot(nodes)))
    edges = [edge for node in nodes for edge in node.edges]
    consedges = [[edge, consedge] for node in nodes for edge in node.edges for consedge in edge.outnode.edges]
    if checkconsistencywith(edges, boolizer, thConsistent) and \
       (boolizer.maxfetchdepth == 0 or boolizer.realizable or \
        checkconsistencywith(consedges, boolizer, tmpConsistent)):
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
