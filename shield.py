import argparse
import json
import yaml
import z3
from collections import deque
from syntheos.boolparser import boolparse
from syntheos.hoaparser import *
from syntheos.datatypes import *

def readmealy(mealyfname):
  mealydata = None
  with open(mealyfname, "r") as f:
    mealydata = yaml.safe_load(f.read())
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

def z3_val_to_python(val):
    if val.sort().kind() == Z3_INT_SORT:
        return val.as_long()
    elif val.sort().kind() == Z3_BOOL_SORT:
        return is_true(val)
    elif val.sort().kind() == Z3_REAL_SORT:
        num, den = val.as_fraction()
        return float(num) / float(den)
    else:
        # fallback: try to convert to string
        return str(val)

def model_to_dict(model):
    return {str(d): z3_val_to_python(model[d]) for d in model.decls()}

def models(val, expr):
  for k,v in val.items():
    expr = substitute(expr, (Int(k), IntVal(v)))
  s = Solver()
  s.add(expr)
  if s.check() == sat:
    return model_to_dict(s.model())|val
  return None

class Shield:
  def __init__(self, node):
    self.node = node

  def protect(self, envval, prsysval):
    fullval = envval | prsysval
    for edge in self.node.edges:
      fullplay = z3.And(edge.getEnvPlay(), edge.getSysResponse())
      model = models(fullval, fullplay)
      if model != None:
        self.node = edge.outnode
        return {k:v for k,v in model.items() if k not in envval and not k.startswith("FETCH_")}
    return None

def keepvar(v, n):
  return not v.startswith("FETCH_" * n)

def main(args):
  shield, maxfetchdepth = readmealy(args.mealy)
  plays = (json.loads(line) for line in sys.stdin)
  prevplays = deque(maxlen = maxfetchdepth)
  playvars= None
  for envplay, sysplay in plays:
    fetchedpast = {("FETCH_"*(i+1)+k) : v for i,kv in enumerate(reversed(prevplays)) for k,v in kv.items() if keepvar(k, maxfetchdepth)}
    fullenv = envplay|fetchedpast
    model = shield.protect(fullenv, sysplay)
    if model is None:
      dbg1(f"The proposed response {sysplay} was not valid")
      model = shield.protect(fullenv, {})
    print(json.dumps(model))
    fullplay = envplay | model
    prevplays.append(fullplay)

if __name__ == '__main__':
  parser = argparse.ArgumentParser('Mealy shield')
  parser.add_argument('--mealy', help='File with mealy', type=str, default="")
  args = parser.parse_args()
  main(args)
