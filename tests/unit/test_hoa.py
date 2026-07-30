import z3

from syntheos.boolizer import LITTY
from syntheos.hoa import nodes2dot, parsehoa, play2str

# Real output captured from `./strix -f '(l0 -> l1)' --ins=l0 --outs=l1 -o hoa`.
SAMPLE_HOA = """REALIZABLE
HOA: v1
tool: "strix" "21.0.0"
States: 2
Start: 0
AP: 2 "l0" "l1"
controllable-AP: 1
acc-name: all
Acceptance: 0 t
--BODY--
State: 0 "[0]"
[(t) & (1)] 1
State: 1 "[1]"
[(t) & (1)] 1
--END--
"""


def make_littable():
    x = z3.Int("x")
    return {
        "l0": [x > 0, LITTY.ENV],
        "l1": [x < 10, LITTY.SYS],
    }


def test_parsehoa_builds_expected_graph_shape():
    info = parsehoa(SAMPLE_HOA, make_littable())
    assert info["realizable"] is True
    nodes = info["nodes"]
    assert len(nodes) == 2
    for node in nodes:
        assert len(node.edges) == 1
        assert node.edges[0].outnode is nodes[1]


def test_edge_plays_expand_through_transtab():
    info = parsehoa(SAMPLE_HOA, make_littable())
    edge = info["nodes"][0].edges[0]
    x = z3.Int("x")
    solver = z3.Solver()
    solver.add(edge.getEnvPlay() != z3.BoolVal(True))
    assert solver.check() == z3.unsat  # envplay was the constant AP "t"
    solver = z3.Solver()
    solver.add(edge.getSysResponse() != (x < 10))
    assert solver.check() == z3.unsat  # sysplay was AP index 1 -> l1 -> x<10


def test_nodes2dot_and_play2str_do_not_crash():
    info = parsehoa(SAMPLE_HOA, make_littable())
    dot = nodes2dot(info["nodes"])
    assert dot.startswith("digraph {")
    assert dot.rstrip().endswith("}")
    assert "->" in dot
    x = z3.Int("x")
    assert "x" in play2str(x > 0)


def test_parsehoa_supports_empty_literal_names():
    hoa = SAMPLE_HOA.replace('AP: 2 "l0" "l1"', 'AP: 2 "l0" ""')
    littable = make_littable()
    info = parsehoa(hoa, littable)
    assert len(info["nodes"]) == 2
