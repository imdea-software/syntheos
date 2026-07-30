"""Parsing Strix/SeMLL's HOA (Hanoi Omega-Automata) output into a game graph
of Node/Edge objects, and rendering that graph back out as a dot graph or as
individual plays for reporting.
"""

from io import StringIO

from . import z3_support as mnz3
from .config import CONFIG
from .formula import ltlt2z3, ltlZ3, replaceliterals
from .logging_utils import logger
from .prop_parser import boolparse


def simply(cond, transtab):
    return ltlt2z3(replaceliterals(cond, transtab))


class Edge:
    def __init__(self, envplay, sysplay, outnode, outnoden, transtab):
        self.envplay = envplay
        self.sysplay = sysplay
        self.envplayz3 = None
        self.sysplayz3 = None
        self.transtab = transtab
        self.outnode = outnode
        self.outnoden = outnoden

    def getEnvPlay(self):
        if self.envplayz3 is None:
            self.envplayz3 = simply(self.envplay, self.transtab)
        return self.envplayz3

    def getSysResponse(self):
        if self.sysplayz3 is None:
            self.sysplayz3 = simply(self.sysplay, self.transtab)
        return self.sysplayz3


class Node:
    def __init__(self, name):
        self.edges = []
        self.name = name

    def addEdge(self, e):
        self.edges.append(e)


def parseprefix(txtstrm, littable):
    """Read the HOA header up to `--BODY--`, returning
    (state count, start state, realizable?, AP-index -> theory-formula table)."""
    noden = None
    startnode = None
    realizable = None
    transtab = None
    for line in txtstrm:
        if line.startswith("AP: "):
            literals = line[line.index('"') + 1 : -2].split('" "')
            transtab = {
                str(key): (ltlZ3(littable[l][0]) if l else None)
                for key, l in enumerate(literals)
            }
        if "REALIZABLE" in line:
            realizable = "UNREALIZABLE" not in line
            logger.info(line)
        line = line.rstrip()
        if line.startswith("States: "):
            noden = int(line[8:])
        if line.startswith("Start: "):
            startnode = int(line[7:])
        if line == "--BODY--":
            return noden, startnode, realizable, transtab


def processEdge(line, currentnode, nodes, transtab, realizable):
    condstr, outnodestr = line[1:].split("] ")
    outnoden = int(outnodestr)
    plays = boolparse(condstr)["operators"]
    # Strix always emits [env-play, sys-play]; SeMLL swaps the order on an
    # UNREALIZABLE result.
    playix = [0, 1] if realizable or CONFIG.backend == "strix" else [1, 0]
    e = Edge(plays[playix[0]], plays[playix[1]], nodes[outnoden], outnoden, transtab)
    nodes[currentnode].addEdge(e)


def play2str(play) -> str:
    return mnz3.z32str(mnz3.push_negation(play))


def nodes2dot(nodes) -> str:
    lines = ["digraph {"]
    for noden, node in enumerate(nodes):
        for edge in node.edges:
            lines.append(
                "    " + str(noden) + " -> " + edge.outnode.name
                + '[label="When\\n' + play2str(edge.getEnvPlay()) + "\\nthen:\\n"
                + play2str(edge.getSysResponse()) + '"];'
            )
    lines.append("}")
    return "\n".join(lines)


def parsehoa(txt: str, littable: dict) -> dict:
    txtstrm = StringIO(txt)
    nodenumber, startnode, realizable, transtab = parseprefix(txtstrm, littable)
    assert startnode == 0 or CONFIG.backend == "semml"
    nodes = [Node(str(i)) for i in range(nodenumber)]
    currentnode = None
    for line in txtstrm:
        line = line.rstrip()
        if line.startswith("State: "):
            line = line[7:]
            currentnode = int(line[: line.index(" ")])
        if line.startswith("["):
            processEdge(line, currentnode, nodes, transtab, realizable)
    return {"nodes": nodes, "realizable": realizable}
