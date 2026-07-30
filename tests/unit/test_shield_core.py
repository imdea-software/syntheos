import z3

from syntheos.errors import SyntheosError
from syntheos.formula import ltlBoolSym, ltlZ3
from syntheos.hoa import Edge, Node
import pytest

from syntheos.shield.core import (
    Shield,
    getvalfor,
    model_to_dict,
    z3_val_to_python,
    z3tycons,
    z3valcons,
)

VARIABLES = [
    {"name": "e", "type": "Int", "owner": "environment"},
    {"name": "x", "type": "Int", "owner": "system"},
]


def build_two_edge_shield():
    e, x = z3.Int("e"), z3.Int("x")
    node0 = Node("0")
    node1 = Node("1")
    transtab = {
        "0": ltlZ3(e > 0),
        "1": ltlZ3(x > 5),
        "2": ltlZ3(e <= 0),
        "3": ltlZ3(x <= 5),
    }
    edge_forward = Edge(ltlBoolSym("0"), ltlBoolSym("1"), node1, 1, transtab)
    edge_selfloop = Edge(ltlBoolSym("2"), ltlBoolSym("3"), node0, 0, transtab)
    node0.addEdge(edge_forward)
    node0.addEdge(edge_selfloop)
    return Shield(node0, VARIABLES), node0, node1


def test_protect_accepts_a_valid_proposal_and_advances_node():
    shield, node0, node1 = build_two_edge_shield()
    result = shield.protect({"e": 10}, {"x": 7})
    assert result == {"x": 7}
    assert shield.node is node1


def test_protect_takes_selfloop_when_env_is_nonpositive():
    shield, node0, node1 = build_two_edge_shield()
    result = shield.protect({"e": -3}, {"x": 2})
    assert result == {"x": 2}
    assert shield.node is node0


def test_protect_rejects_invalid_proposal_but_falls_back_to_free_choice():
    shield, node0, node1 = build_two_edge_shield()
    # x=-100 satisfies neither edge (x>5 nor x<=5 both fail... actually
    # x<=5 holds, but that edge also requires e<=0, which is false here) so
    # the fully-specified proposal is rejected outright.
    assert shield.protect({"e": 10}, {"x": -100}) is None
    # Falling back to an unconstrained system choice (as process_plays does)
    # must find *some* legal x satisfying edge_forward's x>5.
    fallback = shield.protect({"e": 10}, {})
    assert fallback is not None
    assert fallback["x"] > 5
    assert shield.node is node1


def test_gettypeof_strips_fetch_prefix():
    shield, _, _ = build_two_edge_shield()
    assert shield.gettypeof("x") == "Int"
    assert shield.gettypeof("FETCH_x") == "Int"
    assert shield.gettypeof("FETCH_FETCH_x") == "Int"
    assert shield.gettypeof("unknown") is None


def test_type_helpers_reject_unsupported_types():
    with pytest.raises(SyntheosError):
        z3tycons("Bool")
    with pytest.raises(SyntheosError):
        z3valcons("Bool")
    with pytest.raises(SyntheosError):
        getvalfor("Bool")


def test_type_helpers_int_and_real():
    assert z3tycons("Int") is z3.Int
    assert z3tycons("Real") is z3.Real
    assert z3valcons("Int") is z3.IntVal
    assert z3valcons("Real") is z3.RealVal
    assert isinstance(getvalfor("Int"), int)
    assert isinstance(getvalfor("Real"), int)  # arbitrary placeholder, not type-checked


def test_z3_val_to_python_and_model_to_dict():
    solver = z3.Solver()
    x, r, b = z3.Int("x"), z3.Real("r"), z3.Bool("b")
    solver.add(x == 3, r == 1.5, b == True)
    assert solver.check() == z3.sat
    model = solver.model()
    result = model_to_dict(model)
    assert result["x"] == 3
    assert result["r"] == 1.5
    assert result["b"] is True
    assert z3_val_to_python(z3.IntVal(7)) == 7
