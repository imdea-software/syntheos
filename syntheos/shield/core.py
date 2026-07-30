"""The runtime shield: given a Mealy machine (the controller Syntheos
synthesized), play it safely. On each step it takes the environment's actual
move plus the system's proposed move and, if that combination isn't a legal
edge out of the current game node, substitutes a legal one instead.
"""

import re

import yaml
import z3

from ..errors import SyntheosError
from ..formula import fetchdepth, getZ3, getz3vars, z32ltlt
from ..hoa import Edge, Node
from ..prop_parser import boolparse


def z3tycons(ty: str):
    match ty:
        case "Int":
            return z3.Int
        case "Real":
            return z3.Real
        case _:
            raise SyntheosError("Unhandled type: " + ty)


def z3valcons(ty: str):
    match ty:
        case "Int":
            return z3.IntVal
        case "Real":
            return z3.RealVal
        case _:
            raise SyntheosError("Unhandled type: " + ty)


def getvalfor(ty: str):
    """An arbitrary placeholder value for a system variable the shield left
    unconstrained (any value works, since the game doesn't care)."""
    match ty:
        case "Int":
            return 1234
        case "Real":
            return 2345
        case _:
            raise SyntheosError("Unhandled type: " + ty)


def z3_val_to_python(val):
    if val.sort().kind() == z3.Z3_INT_SORT:
        return val.as_long()
    elif val.sort().kind() == z3.Z3_BOOL_SORT:
        return z3.is_true(val)
    elif val.sort().kind() == z3.Z3_REAL_SORT:
        return float(val.as_fraction())
    else:
        return str(val)


def model_to_dict(model) -> dict:
    return {str(d): z3_val_to_python(model[d]) for d in model.decls()}


class Shield:
    def __init__(self, node: Node, variables: list):
        self.node = node
        self.variables = variables

    def gettypeof(self, name: str):
        while name.startswith("FETCH_"):
            name = name[6:]
        for v in self.variables:
            if v["name"] == name:
                return v["type"]
        return None

    def models(self, val: dict, expr):
        """If `expr` (a play's condition) is satisfiable once every variable
        in `val` is substituted with its concrete value, return a full model
        (that substitution plus a satisfying assignment for the rest);
        otherwise None."""
        for k, v in val.items():
            expr = z3.substitute(expr, (z3tycons(self.gettypeof(k))(k), z3valcons(self.gettypeof(k))(v)))
        solver = z3.Solver()
        solver.add(expr)
        if solver.check() == z3.sat:
            return model_to_dict(solver.model()) | val
        return None

    def protect(self, envval: dict, prsysval: dict):
        """Find an edge out of the current node consistent with the
        environment's actual values and (as much as possible of) the
        system's proposed values, advance the shield to that edge's target
        node, and return the full system response to play."""
        fullval = envval | prsysval
        sysvars = [v["name"] for v in self.variables if v["owner"] == "system"]
        for edge in self.node.edges:
            fullplay = z3.And(edge.getEnvPlay(), edge.getSysResponse())
            model = self.models(fullval, fullplay)
            if model is not None:
                self.node = edge.outnode
                assignedmodel = {k: v for k, v in model.items() if k in sysvars}
                arbitraryvals = {v["name"]: getvalfor(v["type"]) for v in self.variables if v["owner"] == "system"}
                return arbitraryvals | assignedmodel
        return None


def read_mealy(mealy_fname: str):
    """Load a Mealy machine saved by `syntheos --save-mealy`."""
    with open(mealy_fname, "r") as f:
        mealy_data = yaml.safe_load(f.read())

    variables = mealy_data["variables"]
    idregex = r"\b[a-zA-Z][a-zA-Z0-9_]*\b"
    transtab = {
        k: z32ltlt(z3.parse_smt2_string(f"(assert {v})", decls=getz3vars(re.findall(idregex, v), variables))[0])
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
