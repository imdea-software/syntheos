"""Parser for the flat propositional formulas over literal ids that appear in
HOA edge conditions (e.g. `[0&!1]`) and in saved Mealy-machine YAML (e.g.
`l0&!l1`). Built with PLY, mirroring `ltl_parser.py`'s approach.
"""

import ply.lex as lex
import ply.yacc as yacc
from ply.lex import LexToken
from ply.yacc import YaccProduction

from .errors import SyntheosError
from .formula import Formula, ltlBoolSym, ltlConj, ltlDisj, ltlNeg

tokens = ("NUMBER",)

literals = ["|", "!", "&", "(", ")"]


def t_NUMBER(t: LexToken) -> LexToken:
    r"\d+|t|f"
    t.value = ltlBoolSym(t.value)
    return t


t_ignore = " "


def t_error(t: LexToken) -> None:
    raise SyntheosError(f"Illegal character '{t.value[0]}'")


lexer = lex.lex()

precedence = (
    ("left", "|"),
    ("left", "&"),
    ("right", "UMINUS"),
)


def p_statement_expr(p: YaccProduction) -> None:
    "statement : expression"
    p[0] = p[1]


def p_expression_binop(p: YaccProduction) -> None:
    """expression : expression '|' expression
    | expression '&' expression"""
    if p[2] == "|":
        p[0] = ltlDisj(p[1], p[3])
    elif p[2] == "&":
        p[0] = ltlConj(p[1], p[3])


def p_expression_uminus(p: YaccProduction) -> None:
    "expression : '!' expression %prec UMINUS"
    p[0] = ltlNeg(p[2])


def p_expression_group(p: YaccProduction) -> None:
    "expression : '(' expression ')'"
    p[0] = p[2]


def p_expression_number(p: YaccProduction) -> None:
    "expression : NUMBER"
    p[0] = p[1]


def p_error(p: YaccProduction | None) -> None:
    if p:
        print(f"Syntax error at '{p.value}'")
    else:
        print("Syntax error at EOF")


parser = yacc.yacc(debug=0)


def boolparse(s: str) -> Formula:
    return parser.parse(s, lexer=lexer)
