from boolparser import boolparse
from datatypes import *
from io import StringIO

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

def simply(cond, transtab):
  return ltlt2z3(replaceliterals(cond, transtab))

class Edge:
  def __init__(self, envplay, sysplay, outnode, outnoden, transtab):
    self.envplay = envplay
    self.sysplay = sysplay
    self.envplayz3 = None
    self.sysplayz3 = None
    self.transtab = transtab
    self.outnode = outnode
    self.outnoden = outnoden

  def getEnvPlay(self):
    if self.envplayz3 is None:
      self.envplayz3 = simply(self.envplay, self.transtab)
    return self.envplayz3

  def getSysResponse(self):
    if self.sysplayz3 is None:
      self.sysplayz3 = simply(self.sysplay, self.transtab)
    return self.sysplayz3

class Node:
  def __init__(self, name):
    self.edges = []
    self.name = name
  def addEdge(self, e):
    self.edges.append(e)

def parseprefix(txtstrm, littable):
  noden = None
  startnode = None
  realizable = None
  transtab = None
  for line in txtstrm:
    if line.startswith("AP: "):
      literals = line[line.index('"')+1:-2].split('" "')
      transtab = {str(key):value for (key, value) in enumerate([ltlZ3(littable[l][0]) for l in literals])}
    if "REALIZABLE" in line:
      realizable = not ("UNREALIZABLE" in line)
      dbg1(line)
    line = line.rstrip()
    if line.startswith("States: "):
      noden = int(line[8:])
    if line.startswith("Start: "):
      startnode = int(line[7:])
    if line == "--BODY--":
      return noden, startnode, realizable, transtab

def processEdge(line, currentnode, nodes, transtab):
  condstr,outnodestr = line[1:].split("] ")
  outnoden = int(outnodestr)
  plays = boolparse(condstr)["operators"]
  e = Edge(plays[0], plays[1], nodes[outnoden], outnoden, transtab)
  nodes[currentnode].addEdge(e)

def nodes2dot(nodes):
  ret = "digraph {\n"
  for noden, node in enumerate(nodes):
    for edge in node.edges:
      ret += "    " + str(noden) + " -> " + edge.outnode.name +\
      "[label=\"When\\n" + z32str(push_negation(edge.getEnvPlay())) + "\\nthen:\\n" +\
      z32str(push_negation(edge.getSysResponse())) + "\"];\n"
  ret += "}"
  return ret

def parsehoa(txt, littable):
  txtstrm = StringIO(txt)
  nodenumber, startnode, realizable, transtab = parseprefix(txtstrm, littable)
  assert(startnode == 0)
  nodes = [Node(str(i)) for i in range(nodenumber)]
  for line in txtstrm:
    line = line.rstrip()
    if line.startswith("State: "):
      line = line[7:]
      currentnode = int(line[:line.index(" ")])
    if line.startswith("["):
      processEdge(line, currentnode, nodes, transtab)
  return { "nodes": nodes, "realizable": realizable }
