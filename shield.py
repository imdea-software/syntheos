import argparse
import json
import yaml
import z3
import sys
import re
from collections import deque
from syntheos.boolparser import boolparse
from syntheos.hoaparser import *
from syntheos.datatypes import *

class Shield:
  def __init__(self, node, variables):
    self.node = node
    self.variables = variables

  def gettypeof(self, nm):
    while nm.startswith("FETCH_"):
      nm = nm[6:]
    for v in self.variables:
      if v["name"] == nm:
        return v["type"]
    return None

  def models(self, val, expr):
    """
    Checks if a model satisfies the given Z3 expression.
    """
    for k, v in val.items():
      expr = z3.substitute(expr, (z3tycons(self.gettypeof(k))(k), z3valcons(self.gettypeof(k))(v)))
    solver = z3.Solver()
    solver.add(expr)
    if solver.check() == z3.sat:
      return model_to_dict(solver.model()) | val
    return None

  def protect(self, envval, prsysval):
    """
    Protects the system by finding a valid response based on the environment and proposed system values.
    """
    fullval = envval | prsysval
    sysvars = [v["name"] for v in self.variables if v["owner"] == "system"]
    for edge in self.node.edges:
      fullplay = z3.And(edge.getEnvPlay(), edge.getSysResponse())
      model = self.models(fullval, fullplay)
      if model is not None:
        self.node = edge.outnode
        assignedmodel = {k: v for k, v in model.items() if k in sysvars}
        arbitraryvals = {v["name"]:getvalfor(v["type"]) for v in self.variables if v["owner"] == "system"}
        return arbitraryvals | assignedmodel
    return None

def z3tycons(ty):
  match ty:
    case "Int":
      return z3.Int
    case "Real":
      return z3.Real
    case _:
      error("Unhandled type: " + ty)

def z3valcons(ty):
  match ty:
    case "Int":
      return z3.IntVal
    case "Real":
      return z3.RealVal
    case _:
      error("Unhandled type: " + ty)

def getvalfor(ty):
  match ty:
    case "Int":
      return 1234
    case "Real":
      return 2345
    case _:
      error("Unhandled type: " + ty)

def read_mealy(mealy_fname):
  """
  Reads a Mealy machine from a YAML file and constructs the Shield object.
  """
  with open(mealy_fname, "r") as f:
    mealy_data = yaml.safe_load(f.read())

  variables = mealy_data["variables"]
  idregex = r"\b[a-zA-Z][a-zA-Z0-9_]*\b"
  transtab = {
    k: z32ltlt(parse_smt2_string(f"(assert {v})", decls=getz3vars(re.findall(idregex, v), variables))[0])
    for k, v in mealy_data["transtab"].items()
  }
  mealynodes = mealy_data["nodes"]
  nodes = [Node(str(i)) for i in range(len(mealynodes))]

  for i, mealy_edges in enumerate(mealynodes):
    for mealy_edge in mealy_edges:
      outnoden = mealy_edge["outnoden"]
      edge = Edge(
        boolparse(mealy_edge["envplay"]),
        boolparse(mealy_edge["sysplay"]),
        nodes[outnoden],
        outnoden,
        transtab,
      )
      nodes[i].addEdge(edge)

  max_fetch_depth = max(fetchdepth(getZ3(v)) for v in transtab.values())
  return Shield(nodes[0], variables), max_fetch_depth, nodes


def z3_val_to_python(val):
  """
  Converts a Z3 value to a Python-native type.
  """
  if val.sort().kind() == z3.Z3_INT_SORT:
    return val.as_long()
  elif val.sort().kind() == z3.Z3_BOOL_SORT:
    return z3.is_true(val)
  elif val.sort().kind() == z3.Z3_REAL_SORT:
    num, den = val.as_fraction()
    return float(num) / float(den)
  else:
    return str(val)  # Fallback to string


def model_to_dict(model):
  """
  Converts a Z3 model to a dictionary.
  """
  return {str(d): z3_val_to_python(model[d]) for d in model.decls()}


def keep_var(v, n):
  """
  Determines whether a variable should be kept based on its prefix and depth.
  """
  return not v.startswith("FETCH_" * n)


def parse_arguments():
  """
  Parses command-line arguments.
  """
  parser = argparse.ArgumentParser(description="Mealy shield")
  parser.add_argument('--mealy', help='File with Mealy machine', type=str, required=True)
  parser.add_argument('--show-mealy', action="store_true", help='Show mealy machine')
  parser.add_argument('--dbglevel', help='Debug level', type=int, default=0)
  return parser.parse_args()


def process_plays(shield, max_fetch_depth):
  """
  Processes plays from standard input and applies the shield logic.
  """
  plays = (json.loads(line) for line in sys.stdin)
  prev_plays = deque(maxlen=max_fetch_depth)

  for env_play, sys_play in plays:
    fetched_past = {
      ("FETCH_" * (i + 1) + k): v
      for i, kv in enumerate(reversed(prev_plays))
      for k, v in kv.items()
      if keep_var(k, max_fetch_depth)
    }
    full_env = env_play | fetched_past
    model = shield.protect(full_env, sys_play)

    if model is None:
      print("The proposed response was not valid", file=sys.stderr)
      model = shield.protect(full_env, {})

    print(json.dumps(model))
    full_play = env_play | model
    prev_plays.append(full_play)


def main():
  """
  Main function to execute the shield logic.
  """
  args = parse_arguments()
  setdbglevel(args.dbglevel)
  shield, max_fetch_depth, nodes = read_mealy(args.mealy)
  if args.show_mealy:
    print("Mealy machine:")
    print(nodes2dot(nodes))
  process_plays(shield, max_fetch_depth)


if __name__ == '__main__':
  main()
