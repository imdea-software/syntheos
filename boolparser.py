import ply.lex as lex
import ply.yacc as yacc
from datatypes import *

tokens = (
    'NUMBER',
)

literals = ['|', '!', '&', '(', ')']

# Tokens

def t_NUMBER(t):
    r'\d+|t|f'
    t.value = ltlBoolSym(t.value)
    return t

t_ignore = " "

def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

lexer = lex.lex()

# Parsing rules

precedence = (
    ('left', '|'),
    ('left', '&'),
    ('right', 'UMINUS'),
)

def p_statement_expr(p):
    'statement : expression'
    p[0]=p[1]

def p_expression_binop(p):
    '''expression : expression '|' expression
                  | expression '&' expression'''
    if p[2] == '|':
        p[0] = ltlDisj(p[1], p[3])
    elif p[2] == '&':
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

parser = yacc.yacc()

def boolparse(s):
  return parser.parse(s, lexer=lexer)
