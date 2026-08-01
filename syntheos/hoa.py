"""Parsing Strix/SeMLL's HOA (Hanoi Omega-Automata) output into a game graph
of Node/Edge objects, and rendering that graph back out as a dot graph or as
individual plays for reporting.
"""

from io import StringIO
from typing import TextIO, TypedDict

from z3 import BoolRef, ExprRef

from . import z3_support as mnz3
from .boolizer import LITTY
from .config import CONFIG
from .formula import Formula, ltlt2z3, ltlZ3, replaceliterals
from .logging_utils import logger
from .prop_parser import boolparse

# AP index (as it appears in HOA edge conditions, e.g. "0" in "[0&!1]") -> the
# theory formula it stands for. An AP whose name Strix reported as empty (see
# parseprefix) maps to None; edges never actually reference such an AP, since
# an empty name means Strix determined the proposition was irrelevant and
# optimized every mention of it away.
TransTab = dict[str, Formula | None]

LitTable = dict[str, tuple[ExprRef, LITTY]]


class HoaInfo(TypedDict):
    nodes: list["Node"]
    realizable: bool


def simply(cond: Formula, transtab: TransTab) -> BoolRef:
    return ltlt2z3(replaceliterals(cond, transtab))  # type: ignore[arg-type]


class Edge:
    # Game graphs are rebuilt from scratch on every CEGAR iteration and can
    # have many edges for larger specs; slots keep each instance small and
    # attribute access fast instead of paying for a per-instance __dict__.
    __slots__ = ("envplay", "sysplay", "envplayz3", "sysplayz3", "transtab", "outnode", "outnoden")

    def __init__(self, envplay: Formula, sysplay: Formula, outnode: "Node", outnoden: int, transtab: TransTab):
        self.envplay = envplay
        self.sysplay = sysplay
        self.envplayz3: BoolRef | None = None
        self.sysplayz3: BoolRef | None = None
        self.transtab = transtab
        self.outnode = outnode
        self.outnoden = outnoden

    def getEnvPlay(self) -> BoolRef:
        if self.envplayz3 is None:
            self.envplayz3 = simply(self.envplay, self.transtab)
        return self.envplayz3

    def getSysResponse(self) -> BoolRef:
        if self.sysplayz3 is None:
            self.sysplayz3 = simply(self.sysplay, self.transtab)
        return self.sysplayz3


class Node:
    __slots__ = ("edges", "name")

    def __init__(self, name: str):
        self.edges: list[Edge] = []
        self.name = name

    def addEdge(self, e: Edge) -> None:
        self.edges.append(e)


def parseprefix(txtstrm: TextIO, littable: LitTable) -> tuple[int, int, bool, TransTab] | None:
    """Read the HOA header up to `--BODY--`, returning
    (state count, start state, realizable?, AP-index -> theory-formula table)."""
    noden = None
    startnode = None
    realizable = None
    transtab: TransTab = {}
    for line in txtstrm:
        if line.startswith("AP: "):
            literals = line[line.index('"') + 1 : -2].split('" "')
            transtab = {str(key): (ltlZ3(littable[l][0]) if l else None) for key, l in enumerate(literals)}
        if "REALIZABLE" in line:
            realizable = "UNREALIZABLE" not in line
            logger.info(line)
        line = line.rstrip()
        if line.startswith("States: "):
            noden = int(line[8:])
        if line.startswith("Start: "):
            startnode = int(line[7:])
        if line == "--BODY--":
            assert noden is not None and startnode is not None and realizable is not None
            return noden, startnode, realizable, transtab
    return None


def processEdge(line: str, currentnode: int, nodes: list[Node], transtab: TransTab, realizable: bool) -> None:
    condstr, outnodestr = line[1:].split("] ")
    outnoden = int(outnodestr)
    plays = boolparse(condstr)["operators"]
    # Strix always emits [env-play, sys-play]; SeMLL swaps the order on an
    # UNREALIZABLE result.
    playix = [0, 1] if realizable or CONFIG.backend == "strix" else [1, 0]
    e = Edge(plays[playix[0]], plays[playix[1]], nodes[outnoden], outnoden, transtab)
    nodes[currentnode].addEdge(e)


def play2str(play: BoolRef) -> str:
    return mnz3.z32str(mnz3.push_negation(play))


def nodes2dot(nodes: list[Node]) -> str:
    lines = ["digraph {"]
    for noden, node in enumerate(nodes):
        for edge in node.edges:
            lines.append(
                "    "
                + str(noden)
                + " -> "
                + edge.outnode.name
                + '[label="When\\n'
                + play2str(edge.getEnvPlay())
                + "\\nthen:\\n"
                + play2str(edge.getSysResponse())
                + '"];'
            )
    lines.append("}")
    return "\n".join(lines)


def parsehoa(txt: str, littable: LitTable) -> HoaInfo:
    txtstrm = StringIO(txt)
    prefix = parseprefix(txtstrm, littable)
    assert prefix is not None, "HOA output ended before --BODY--"
    nodenumber, startnode, realizable, transtab = prefix
    assert startnode == 0 or CONFIG.backend == "semml"
    nodes = [Node(str(i)) for i in range(nodenumber)]
    currentnode = -1
    for line in txtstrm:
        line = line.rstrip()
        if line.startswith("State: "):
            line = line[7:]
            currentnode = int(line[: line.index(" ")])
        if line.startswith("["):
            processEdge(line, currentnode, nodes, transtab, realizable)
    return {"nodes": nodes, "realizable": realizable}
