"""Parser for the LTLt specification language: standard LTL connectives
(`!`, `&`, `|`, `->`, `<->`, `X`, `G`, `F`, `W`, `R`) over theory atoms written
as `[<python-ish expression over the spec's variables>]`, e.g. `[x>y(y(x))]`
where `y(...)` refers to the previous value of a variable.
"""

import re

import ply.lex as lex
import ply.yacc as yacc

from .errors import SyntheosError
from .formula import fetchdepth, getZ3, getz3vars, isZ3, z32ltlt

# Set by ltltparse() for the duration of a parse; PLY's grammar actions below
# are module-level functions and can't otherwise receive the spec's variable
# list.
variables = None

tokens = (
    "F", "G", "X", "NEG",  # Unary operators
    "W", "R", "BIDIRECTIONAL", "IMPLIES",  # Binary operators
    "OR", "AND",
    "STRING",  # Leaves
    "LPAREN", "RPAREN",  # Parentheses for grouping
)

t_NEG = r"!"
t_F = r"F"
t_G = r"G"
t_X = r"X"

t_W = r"W"
t_R = r"R"
t_BIDIRECTIONAL = r"<->"
t_IMPLIES = r"->"

t_OR = r"\|"
t_AND = r"&"

t_STRING = r"\[[^\]]*\]"  # Strings enclosed in square brackets

t_LPAREN = r"\("
t_RPAREN = r"\)"

t_ignore = " \t\n"


def t_error(t):
    raise SyntheosError(f"Illegal character '{t.value[0]}'")


lexer = lex.lex()

precedence = (
    ("left", "IMPLIES", "BIDIRECTIONAL", "W", "R"),
    ("left", "AND", "OR"),
    ("right", "F", "G", "X", "NEG"),
)


def p_expression_unary(p):
    """expression : F expression
    | G expression
    | X expression
    | NEG expression"""
    p[0] = {"kind": p[1], "operators": [p[2]]}


def p_expression_binary(p):
    """expression : expression R expression
    | expression W expression
    | expression BIDIRECTIONAL expression
    | expression IMPLIES expression
    | expression OR expression
    | expression AND expression
    """
    p[0] = {"kind": p[2], "operators": [p[1], p[3]]}


def p_expression_group(p):
    """expression : LPAREN expression RPAREN"""
    p[0] = p[2]


def z3parse(s: str):
    """Evaluate the `[...]` payload as a Python expression over the spec's
    Z3-typed variables, e.g. "x>y(y(x))" with x an Int becomes a Z3 formula.
    Builtins are stripped from eval's scope since only arithmetic/comparison
    syntax is ever needed here."""
    das = s[1:-1]
    idregex = r"\b[a-zA-Z][a-zA-Z0-9_]*\b"
    identifiers = re.findall(idregex, das)
    z3vars = getz3vars(identifiers, variables)
    return eval(das, {"__builtins__": {}}, z3vars)


def p_expression_string(p):
    """expression : STRING"""
    p[0] = z32ltlt(z3parse(p[1]))


def p_error(p):
    print("Syntax error in input!")
    raise SyntheosError(p)


parser = yacc.yacc(debug=0)


def checkFetchLevel(f) -> bool:
    """A `y(...)`-wrapped (FETCH_) variable at nesting depth d may only
    appear inside at least d `X` operators, since it refers to a value from
    d steps ago."""

    def cfl(f, level):
        if isZ3(f):
            return fetchdepth(getZ3(f)) <= level
        if f["kind"] == "X":
            level += 1
        return all(cfl(x, level) for x in f["operators"])

    return cfl(f, 0)


def replace_expressions(text: str) -> str:
    """Rewrite `y(y(x))` into `FETCH_FETCH_x` before tokenizing, so nested
    fetches survive as plain identifiers."""

    def replace_nested(expression):
        while match := re.search(r"y\((.*?)\)", expression):
            expression = re.sub(r"y\((.*?)\)", r"FETCH_\1", expression, count=1)
        return expression

    return replace_nested(text)


def ltltparse(bstr: str, variables_value: list):
    global variables
    variables = variables_value
    bstr = replace_expressions(bstr)
    structed = parser.parse(bstr, lexer=lexer)
    if not checkFetchLevel(structed):
        raise SyntheosError("Fetched variable with wrong level of X")
    return structed
