"""The game graph the shield walks: Node/Edge objects rebuilt from a saved
mealy machine, plus rendering that graph back out as a dot graph for
`--show-mealy`.
"""

from z3 import BoolRef

from . import z3_support as mnz3
from .formula import Formula, ltlt2z3, replaceliterals

# AP index (as it appears in a saved mealy machine's transtab) -> the theory
# formula it stands for.
TransTab = dict[str, Formula | None]


def simply(cond: Formula, transtab: TransTab) -> BoolRef:
    return ltlt2z3(replaceliterals(cond, transtab))  # type: ignore[arg-type]


class Edge:
    # Game graphs can have many edges for larger mealy machines; slots keep
    # each instance small and attribute access fast instead of paying for a
    # per-instance __dict__.
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
