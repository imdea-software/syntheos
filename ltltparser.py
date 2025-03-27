import ply.lex as lex
import ply.yacc as yacc
from z3 import *
import re
from datatypes import *

varstable = None

# Lexical Analyzer (Tokenizer)

# List of token names
tokens = (
    'F', 'G', 'X', 'NEG',  # Unary operators
    'W', 'R', 'BIDIRECTIONAL', 'IMPLIES',  # Binary operators
    'OR', 'AND',
    'STRING',  # Leaves
    'LPAREN', 'RPAREN',  # Parentheses for grouping
)

# Regular expressions for each token
t_NEG = r'!'
t_F = r'F'
t_G = r'G'
t_X = r'X'

t_W = r'W'
t_R = r'R'
t_BIDIRECTIONAL = r'<->'
t_IMPLIES = r'->'

t_OR = r'\|'
t_AND = r'&'

t_STRING = r'\[[^\]]*\]'  # Match strings enclosed in square brackets

t_LPAREN = r'\('
t_RPAREN = r'\)'

t_ignore = ' \t\n'  # Ignore spaces, tabs, and newlines

# Error handling for illegal characters
def t_error(t):
    print(f"Illegal character '{t.value[0]}'")
    t.lexer.skip(1)

# Build the lexer
lexer = lex.lex()

# Precedence rules (higher precedence goes first)
precedence = (
    ('left', 'IMPLIES', 'BIDIRECTIONAL'),  # Binary operators like -> and <->
    ('left', 'AND', 'OR'),  # N-ary operators like | and &
    ('right', 'F', 'G', 'X', 'NEG'),  # Unary operators have highest precedence (right associative)
)

# Parsing rules for the grammar

def p_expression_unary(p):
    '''expression : F expression
                  | G expression
                  | X expression
                  | NEG expression'''
    p[0] = {"kind": p[1], "operators": [p[2]]}  # (operator, operand list)

def p_expression_binary(p):
    '''expression : expression R expression
                  | expression W expression
                  | expression BIDIRECTIONAL expression
                  | expression IMPLIES expression
                  | expression OR expression
                  | expression AND expression
                  '''
    p[0] = {"kind": p[2], "operators": [p[1], p[3]]}  # (operator, operand list)

def p_expression_group(p):
    '''expression : LPAREN expression RPAREN'''
    p[0] = p[2]  # Grouping, just pass the inner expression

def makevar(x):
  orix = x
  while x.startswith("FETCH_"):
    x = x[6:]
  match varstable[x]:
    case "Int":
      cons = Int
    case "Real":
      cons = Real
    case _:
      error("Unhandled type: " + varstable[x])
  return cons(orix)

def z3parse(s):
  safe_globals = {"__builtins__": None}  # Disable built-in functions
  das = s[1:-1]
  idregex = r"\b[a-zA-Z][a-zA-Z0-9_]*\b"
  identifiers = re.findall(idregex, das)
  z3vars = {key: makevar(key) for key in identifiers}
  return eval(das, {}, z3vars)

def p_expression_string(p):
    '''expression : STRING'''
    p[0] = z32ltlt(z3parse(p[1]))  # A string leaf

# Error rule for syntax errors
def p_error(p):
    print("Syntax error in input!")
    error(p)

# Build the parser
parser = yacc.yacc()

def checkFetchLevel(f):
  def cfl(f,l):
    if isZ3(f):
      return fetchdepth(getZ3(f)) <= l
    if f["kind"] == "X":
      l = l+1
    return all([cfl(x,l) for x in f["operators"]])
  return cfl(f,0)

def replace_expressions(text):
  def replace_nested(expression):
    while match := re.search(r'y\((.*?)\)', expression):
      expression = re.sub(r'y\((.*?)\)', r'FETCH_\1', expression, 1)
    return expression
  return replace_nested(text)

# Example usage
def ltltparse(bstr, variables):
  global varstable
  varstable = {v["name"]:v["type"] for v in variables}
  bstr = replace_expressions(bstr)
  structed = parser.parse(bstr, lexer=lexer)
  if not checkFetchLevel(structed):
    error("Fetched variable with wrong level of X")
  return structed
