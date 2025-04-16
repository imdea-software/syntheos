import argparse
from hoaparser import *
from datatypes import *
import json
from boolparser import boolparse
import z3
from collections import deque

def readmealy(mealyfname):
  mealydata = None
  with open(mealyfname, "r") as f:
    mealydata = json.loads(f.read())
  transtab = {k:z32ltlt(parse_smt2_string(f"(assert {v})", decls=getz3vars(v,mealydata["variables"]))[0]) for k,v in mealydata["transtab"].items()}
  mealynodes = mealydata["nodes"]
  nodes = [Node(str(i)) for i in range(len(mealynodes))]
  for i,mealyedges in enumerate(mealynodes):
    for mealyedge in mealyedges:
      outnoden = mealyedge["outnoden"]
      e = Edge(boolparse(mealyedge["envplay"]), boolparse(mealyedge["sysplay"]), nodes[outnoden], outnoden, transtab)
      nodes[i].addEdge(e)
  maxfetchdepth = max([fetchdepth(getZ3(v)) for v in transtab.values()])
  return Shield(nodes[0]),maxfetchdepth

def models(val, expr):
  for k,v in val.items():
    expr = substitute(expr, (Int(k), IntVal(v)))
  s = Solver()
  s.add(expr)
  ret = s.check() == sat
  return ret

def getResponse(val, expr):
  for k,v in val.items():
    expr = substitute(expr, (Int(k), IntVal(v)))
  s = Solver()
  s.add(expr)
  s.check()
  return s.model()

class Shield:
  def __init__(self, node):
    self.node = node

  def protect(self, envval, prsysval):
    if prsysval is None:
      prsysval = ltlBoolSym('f');
    fullval = envval | prsysval
    for edge in self.node.edges:
      fullplay = z3.And(edge.getEnvPlay(), edge.getSysResponse())
      if models(fullval, fullplay):
        self.node = edge.outnode
        return prsysval
    dbg1(f"The proposed response {prsysval} was not valid")
    for edge in self.node.edges:
      envplay = edge.getEnvPlay()
      if models(envval, envplay):
        self.node = edge.outnode
        return getResponse(envval, edge.getSysResponse())

def main(args):
  shield, maxfetchdepth = readmealy(args.mealy)
  plays = [
      [{'d': 105}, {'a': 10}],
      [{'d': 105}, {'a': 10}],
      [{'d': 105}, {'a': 10}],
  ]
  prevplays = deque(maxlen = maxfetchdepth)
  playvars= None
  for envplay, sysplay in plays:
    fetchedpast = {("FETCH_"*(i+1)+k) : v for i,kv in enumerate(reversed(prevplays)) for k,v in kv.items()}
    print(shield.protect(envplay|fetchedpast, sysplay))
    fullplay = envplay | sysplay
    prevplays.append(fullplay)

if __name__ == '__main__':
  parser = argparse.ArgumentParser('Mealy shield')
  parser.add_argument('--mealy', help='File with mealy', type=str, default="")
  args = parser.parse_args()
  main(args)
