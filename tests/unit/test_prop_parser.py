from syntheos.formula import isBoolSymFalse, isBoolSymTrue, symbol
from syntheos.prop_parser import boolparse


def test_parses_literal():
    result = boolparse("3")
    assert symbol(result) == "3"


def test_parses_constants():
    assert isBoolSymTrue(boolparse("t"))
    assert isBoolSymFalse(boolparse("f"))


def test_parses_negation_and_precedence():
    # & binds tighter than |
    result = boolparse("0|1&!2")
    assert result["kind"] == "|"
    rhs = result["operators"][1]
    assert rhs["kind"] == "&"
    assert rhs["operators"][1]["kind"] == "!"


def test_parses_parens():
    result = boolparse("(0|1)&2")
    assert result["kind"] == "&"
    assert result["operators"][0]["kind"] == "|"
