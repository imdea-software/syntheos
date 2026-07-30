"""Parser for the flat propositional formulas over literal ids that appear in
HOA edge conditions (e.g. `[0&!1]`) and in saved Mealy-machine YAML (e.g.
`l0&!l1`). Built with PLY, mirroring `ltl_parser.py`'s approach.
"""

import ply.lex as lex
import ply.yacc as yacc

from .errors import SyntheosError
from .formula import ltlBoolSym, ltlConj, ltlDisj, ltlNeg

tokens = ("NUMBER",)

literals = ["|", "!", "&", "(", ")"]


def t_NUMBER(t):
    r"\d+|t|f"
    t.value = ltlBoolSym(t.value)
    return t


t_ignore = " "


def t_error(t):
    raise SyntheosError("Illegal character '%s'" % t.value[0])


lexer = lex.lex()

precedence = (
    ("left", "|"),
    ("left", "&"),
    ("right", "UMINUS"),
)


def p_statement_expr(p):
    "statement : expression"
    p[0] = p[1]


def p_expression_binop(p):
    """expression : expression '|' expression
    | expression '&' expression"""
    if p[2] == "|":
        p[0] = ltlDisj(p[1], p[3])
    elif p[2] == "&":
        p[0] = ltlConj(p[1], p[3])


def p_expression_uminus(p):
    "expression : '!' expression %prec UMINUS"
    p[0] = ltlNeg(p[2])


def p_expression_group(p):
    "expression : '(' expression ')'"
    p[0] = p[2]


def p_expression_number(p):
    "expression : NUMBER"
    p[0] = p[1]


def p_error(p):
    if p:
        print("Syntax error at '%s'" % p.value)
    else:
        print("Syntax error at EOF")


parser = yacc.yacc(debug=0)


def boolparse(s: str):
    return parser.parse(s, lexer=lexer)
