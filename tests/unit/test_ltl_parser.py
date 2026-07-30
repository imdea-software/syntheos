import pytest
import z3

from syntheos import ltl_parser
from syntheos.errors import SyntheosError
from syntheos.formula import getZ3, isZ3

VARS = [
    {"name": "x", "type": "Int", "owner": "system"},
    {"name": "y", "type": "Int", "owner": "environment"},
]


def test_parses_simple_theory_atom_under_G():
    result = ltl_parser.ltltparse("G([x>0])", VARS)
    assert result["kind"] == "G"
    inner = result["operators"][0]
    assert isZ3(inner)
    x = z3.Int("x")
    solver = z3.Solver()
    solver.add(getZ3(inner) != (x > 0))
    assert solver.check() == z3.unsat


def test_parses_connectives_and_precedence():
    result = ltl_parser.ltltparse("[x>0] & [y>0] -> [x>y]", VARS)
    assert result["kind"] == "->"
    assert result["operators"][0]["kind"] == "&"


def test_fetch_level_ok_inside_matching_X():
    # y(x) has fetch depth 1, needs to be inside at least one X
    result = ltl_parser.ltltparse("X([y(x)>0])", VARS)
    assert result["kind"] == "X"


def test_fetch_level_violation_raises():
    with pytest.raises(SyntheosError):
        ltl_parser.ltltparse("[y(x)>0]", VARS)


def test_nested_fetch_needs_two_X():
    with pytest.raises(SyntheosError):
        ltl_parser.ltltparse("X([y(y(x))>0])", VARS)
    ok = ltl_parser.ltltparse("X(X([y(y(x))>0]))", VARS)
    assert ok["kind"] == "X"


def test_replace_expressions_handles_nesting():
    assert ltl_parser.replace_expressions("y(y(x))>0") == "FETCH_FETCH_x>0"
    assert ltl_parser.replace_expressions("y(x)>y(z)") == "FETCH_x>FETCH_z"
