# Surprise! It is z3
from z3 import *

def isz3const(e):
  return not isz3var(e) and (is_int_value(e) or is_rational_value(e) or is_true(e) or is_false(e))

def isz3var(e):
  return is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED

def quantify(quantifier, varlist, formula):
  if varlist:
    return quantifier(varlist, formula)
  return formula

def make_forall(varlist, formula):
  return quantify(ForAll, varlist, formula)

def make_exists(varlist, formula):
  return quantify(Exists, varlist, formula)

def isSat(formula):
  formula = simplify(formula)
  solver = Solver()
  solver.add(formula)
  satres = solver.check()
  if satres == sat:
    return True
  if satres == unsat:
    return False
  error("Unkown satisfiability")

def eliminate_quantifier(formula):
  return Tactic('qe2')(formula).as_expr()

def thImplies(f0, f1):
  return Implies(f0,f1)

def getUnsatCore(atoms):
  s = Solver()
  s.set(unsat_core=True)
  enumatoms = list(enumerate(atoms))
  for i, atom in enumatoms:
    s.assert_and_track(atom, 'atom_'+str(i))
  result = s.check()
  assert result == unsat
  c = s.unsat_core()
  return [atom for i,atom in enumatoms if Bool('atom_'+str(i)) in c]

def makevar(var, ty):
  match ty:
    case "Int":
      cons = z3.Int
    case "Real":
      cons = z3.Real
    case _:
      error("Unhandled type: " + varstable[x])
  return cons(var)

def rename_vars(expr, renamefn):
  return substitute(expr, [(var, z3.Const(renamefn(var.decl().name()), var.sort())) for var in z3util.get_vars(expr)])

def copy_and_rename(var, renamefn):
  new_name = renamefn(var.decl().name())
  if isinstance(var, IntNumRef) or isinstance(var, ArithRef):  # Int or Real
      return Int(new_name) if var.is_int() else Real(new_name)
  elif isinstance(var, BoolRef):  # Boolean
      return Bool(new_name)
  elif isinstance(var, BitVecRef):  # Bit-vector
      return BitVec(new_name, var.size())
  else:
      raise TypeError("Unsupported Z3 variable type")

def push_negation(expr):
  if is_not(expr):
    inner = expr.arg(0)
    if inner.decl().kind() == Z3_OP_GT:
      return inner.arg(0) <= inner.arg(1)
    elif inner.decl().kind() == Z3_OP_GE:
      return inner.arg(0) < inner.arg(1)
    elif inner.decl().kind() == Z3_OP_LT:
      return inner.arg(0) >= inner.arg(1)
    elif inner.decl().kind() == Z3_OP_LE:
      return inner.arg(0) > inner.arg(1)
    elif is_and(inner):
      return Or(*[push_negation(Not(arg)) for arg in inner.children()])
    elif is_or(inner):
      return And(*[push_negation(Not(arg)) for arg in inner.children()])
    else:
        return Not(push_negation(inner))
  elif is_and(expr) or is_or(expr):
    return expr.decl()(*[push_negation(arg) for arg in expr.children()])
  else:
    return expr


def z32str(expr, parent_op=None, bound_vars = []):
  if is_and(expr):
    conjunction_str = " ∧ ".join(z32str(arg, 'And', bound_vars=bound_vars) for arg in expr.children())
    return f"({conjunction_str})" if parent_op != 'And' and parent_op is not None else conjunction_str
  elif is_or(expr):
    disjunction_str = " ∨ ".join(z32str(arg, 'Or', bound_vars=bound_vars) for arg in expr.children())
    return f"({disjunction_str})" if parent_op != 'Or' and parent_op is not None else disjunction_str
  elif is_not(expr):
    negated_expr = z32str(expr.arg(0), 'Not', bound_vars=bound_vars)
    return f"¬({negated_expr})"
  elif is_implies(expr):
    disjunction_str = " -> ".join(z32str(arg, 'Implies', bound_vars=bound_vars) for arg in expr.children())
    return f"({disjunction_str})" if parent_op is not None else disjunction_str
  elif is_quantifier(expr):
    quant = "∀" if expr.is_forall() else "∃"
    num_vars = expr.num_vars()
    names = [str(expr.var_name(i)) for i in reversed(range(num_vars))]
    new_bound_vars = names + bound_vars
    body_str = z32str(expr.body(), None, new_bound_vars)
    vars_str = ", ".join(names)
    return f"{quant} {vars_str}. ({body_str})"
  elif is_var(expr):
    idx = get_var_index(expr)
    if idx < len(bound_vars):
      return bound_vars[idx]
    else:
      return "UNKNOWNVAR"
  elif expr.decl().kind() == Z3_OP_LE:
    return f"{z32str(expr.arg(0), bound_vars=bound_vars)} ≤ {z32str(expr.arg(1), bound_vars=bound_vars)}"
  elif expr.decl().kind() == Z3_OP_LT:
    return f"{z32str(expr.arg(0), bound_vars=bound_vars)} < {z32str(expr.arg(1), bound_vars=bound_vars)}"
  elif expr.decl().kind() == Z3_OP_GE:
    return f"{z32str(expr.arg(0), bound_vars=bound_vars)} ≥ {z32str(expr.arg(1), bound_vars=bound_vars)}"
  elif expr.decl().kind() == Z3_OP_GT:
    return f"{z32str(expr.arg(0), bound_vars=bound_vars)} > {z32str(expr.arg(1), bound_vars=bound_vars)}"
  elif expr.decl().kind() == Z3_OP_EQ:
    return f"{z32str(expr.arg(0), bound_vars=bound_vars)} = {z32str(expr.arg(1), bound_vars=bound_vars)}"
  elif expr.decl().kind() == Z3_OP_ADD:
    return f"{z32str(expr.arg(0), bound_vars=bound_vars)} + {z32str(expr.arg(1), bound_vars=bound_vars)}"
  else:
    return str(expr)

def z32ltltw(f, funs):
  ltlNeg = funs["negator"]
  ltlConj = funs["conjunctor"]
  ltlDisj = funs["disjunctor"]
  ltlTh = funs["thwrapper"]
  constTrue = funs["constTrue"] # ltlBoolSym('t')
  constFalse = funs["constFalse"]
  def z32ltlt(f):
    if is_and(f):
      ret = z32ltlt(f.children()[0])
      for ch in f.children()[1:]:
        ret = ltlConj(ret, z32ltlt(ch))
      return ret;
    if is_or(f):
      ret = z32ltlt(f.children()[0])
      for ch in f.children()[1:]:
        ret = ltlDisj(ret, z32ltlt(ch))
      return ret;
    if is_not(f):
      ret = ltlNeg(z32ltlt(f.children()[0]))
      return ret;
    if is_ge(f):
      return ltlNeg(ltlTh(f.children()[0].__lt__(f.children()[1])))
    if is_gt(f):
      return ltlTh(f.children()[1].__lt__(f.children()[0]))
    if is_le(f):
      return ltlNeg(ltlTh(f.children()[1].__lt__(f.children()[0])))
    if is_eq(f):
      return ltlConj(ltlNeg(ltlTh(f.children()[1].__lt__(f.children()[0]))), ltlNeg(ltlTh(f.children()[0].__lt__(f.children()[1]))))
    if is_false(f):
      return constFalse
    if is_true(f):
      return constTrue
    if is_quantifier:
      return ltlTh(f)
    error("Unhandled case:" + str(f))
  return z32ltlt(f)
