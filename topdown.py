
import argparse, glob, re, sys
from itertools import izip,count
from language import *
from value import *
from automata import *

DO_STATS = True
SIMPLIFY = True
LIMITER = False

Notequal = u'\u2260'

# There should be another, smarter way of checking whether a value is a 
# constant
def isConstValue(val):
  return (val.getName()[0] == 'C')

#  /\
# /__\
#  ||  Same as above
def isWildcard(val):
  return (not isinstance(val, Instr) and val.getName()[0] == '%')

def local_get_root(src):
  values = src.values()
  root = values.pop()
  while not isinstance(root, Instr):
    root = values.pop()
  return root

twoOperands = [
    'add',
    'sub',
    'mul',
    'udiv',
    'sdiv',
    'urem',
    'srem',
    'shl',
    'ashr',
    'lshr',
    'and',
    'or',
    'xor',
]

# Retrieves arity of symbol using only the symbol's character string
def arity(symbol):
  assert(symbol in twoOperands)
  if symbol in twoOperands:
    return 2
  return 0

######################################################

class tree(object):
  def __init__(self, insts):
    self.inputs = set((k,v) for k,v in insts.iteritems() if isinstance(v,Input))
    self.root = local_get_root(insts)

  # TODO: support more than just binary operations
  @staticmethod
  def numOperands(f):
    assert(isinstance(f, BinOp)), "For now only BinOp are supported"
    return 2

  # TODO: constrain input using asserts or errors
  def subtree(self, path):
    st = self.root
    for i in path:
      assert(i is not 0), "Position 0 not possible"
      if i is 1:
        st = st.v1
      elif i is 2:
        st = st.v2
    return st

  def dump(self):
    if (self.root is not None):
      print(str(self.root.getName()) + "\n{")
      if (self.root.v1):
        print(self.root.v1.getName())
      if (self.root.v2):
        print(self.root.v2.getName())
      print("}\n")

######################################################

class peepholeopt(object):
  def __init__(self, name, pre, source, target):
    self.name = name
    self.pre = pre
    self.source = source
    self.target = target

    self.src_tree = tree(source)
    self.tgt_tree = tree(target)

  # p1 subsumes p2 if p2 is an instance of p1
  @staticmethod
  def subsumes(p1, p2):
    if isinstance(p1, Instr):
      if isinstance(p2, Instr):
        if p1.v1 is not None and p2.v1 is not None:
          left_child = peepholeopt.subsumes(p1.v1, p2.v1)
          if (left_child is False):
            return False

        if p1.v2 is not None and p2.v2 is not None:
          right_child = peepholeopt.subsumes(p1.v2, p2.v2)
          if (right_child is False):
            return False
        return (p1.getOpName() == p2.getOpName())
      else:
        return False
    elif isinstance(p1, Value):
      # p1 is a value but not a constant => Wildcard, or
      if (not isConstValue(p1)) or (isinstance(p2, Value) and isConstValue(p2)):
        return True
      else:
        return False
    else:
      return False

######################################################

class counter(object):
  id = 0
  def __init__(self):
    pass
  
  @classmethod
  def getNext(cls):
    current = cls.id
    cls.id = cls.id + 1
    return current

######################################################

class prefix_tree(object):
  def __init__(self, symbol, numOfChildren):
    self.symbol = symbol
    self.children = []
    for i in range(0, numOfChildren):
      self.children.append(None)
  
  def findWildcardPaths(self):
    paths = []
    self.localwildcardPaths(self, [], paths)
    return paths
  
  # walks through tree to find all wildcards in prefix tree
  def localwildcardPaths(self, node, current_path, paths):
    # TODO: Enforce once or the other, not both node and node.symbol being None
    if node is None or node.symbol is None:
      paths.append(current_path)
    else:
      nchildren = node.numOfChildren()
      for i in range(1, nchildren + 1):
        c = node.childAt(i)
        node.localwildcardPaths(c, [i] + current_path, paths)

  # Might very well regret this offset later on...
  def childAt(self, index):
    return self.children[index-1]

  def replaceAt2(self, path, using):
    assert(isinstance(using, prefix_tree)), "Using has to be of type prefix_tree"
    if (len(path) is 0):
      self.symbol = using.symbol
      self.children = using.children
    else:
      assert(path[-1] in range(1, self.numOfChildren() + 1)), "Position outside arity bound"
      if (len(path) is 1):
        # make sure the last node isn't a None
        i = path[0]
        self.addChild(using, i)
      else:
        self.replaceAt2(path[:-1], using)

  # TODO: perhaps make a recursive version instead of this...
  def replaceAt(self, path, using):
    assert(isinstance(using, prefix_tree)), "Using has to be of type prefix_tree"
    if (len(path) is 0):
      self.symbol = using.symbol
      self.children = using.children
    elif (len(path) > 0):
      pt = self
      for i in path:
        assert(i is not 0), "Position 0 not possible"
        assert(i in range(1,self.numOfChildren() + 1)), "Position outside arity bound"
        ptPrevious = pt
        pt = pt.childAt(i)
      if pt is None:
        ptPrevious.childAt(path.b)
      ptPrevious.symbol = using.symbol
      ptPrevious.children = using.children
    return self

  def addChild(self, child, at):
    assert(isinstance(child, prefix_tree)), "Make sure child is of type prefix_tree"
    assert(at in range(1,self.numOfChildren() + 1)), "Position outside arity bound"
    self.children[at-1] = child

  def numOfChildren(self):
    return len(self.children)
  
  def dump(self):
    print(str(self.symbol) + "\n{\n")
    for c in self.children:
      c.dump()
    print("\n}\n")

######################################################

# TODO: return valid priority
def priority(pat):
  return 1

# TODO: Redo
def matches(P, M):
  for p in P:
    found = False
    for m in M:
      if priority(m) >= priority(p):
        found = True
    if found is False:
      return False
  return True

# TODO: heuristic: choose node with least number of differing symbols at that path
# for all patterns
# For now, just take the first unknown path 
def choosePath(prefix, P):
  paths = prefix.findWildcardPaths()
  return paths[0]
  #for p in P:
  #  for path in paths:
  #    subt = p.subtree(path)

######################################################

class AutomataBuilder(object):
  def __init__(self):
    self.pos = {}
    self.automaton = DFA()
    self.count = counter()

  def localGetNext(self):
    return counter.getNext()
  
  def symbolsAt(self, path, patterns, isvar = False):
    F = set()
    if not isvar:
      for p in patterns:
        f = p.subtree(path)
        if isinstance(f, Instr):
          F.add(f.getOpName())
        elif isConstValue(f):
          F.add(f.getName())
    return F

  # Calculate new P for recursive call, note that the new P is ALWAYS a subset
  # of the old P
  @staticmethod
  def recursiveP(f, P, path):
    newP = []
    for p in P:
      subp = p.subtree(path)
      if (isinstance(subp, Instr) and subp.getOpName() is f):
        newP.append(p)
    return newP

  @staticmethod
  def variablesAt(P, path):
    V = []
    for p in P:
      subt = p.subtree(path)
      if isWildcard(subt):
        V.append(subt)
    return V

  # s : current state
  # e : prefix tree
  # P : list of patterns
  # TODO: label states properly
  def createAutomaton(self, s, e, P):
    M = set(p for p in P if peepholeopt.subsumes(p, e))
    #if len(M) != 0 and matches(P,M):
      # TODO: rephrase acceptance condition...
    if len(P) is 1:
      self.automaton.finalizeState(s)
    else:
      path = choosePath(e, P)
      self.pos[s] = path
      F =  self.symbolsAt(path, P)
      for f in F:
        freshState = str(self.localGetNext())
        self.automaton.addState(str(freshState))
        self.automaton.addTransition(f, s, str(freshState))
        st = prefix_tree(f, arity(f))
        recursP = AutomataBuilder.recursiveP(f, P, path)
        e.replaceAt2(path, st)
        self.createAutomaton(str(freshState), e, recursP)
      # TODO: also add anchestor variables
      V = AutomataBuilder.variablesAt(P, path)
      if len(V) != 0:
        freshState = str(self.localGetNext())
        self.automaton.addState(str(freshState))
        self.automaton.addTransition(Notequal, s, str(freshState))
        st = prefix_tree(Notequal, 0)
        e.replaceAt2(path, st)
        self.createAutomaton(str(freshState), e, V)

######################################################

def generate_automaton(opts, out):
  root_opts = defaultdict(list)
  opts = list(izip(count(1), opts))

  # gather names of testcases
  if DO_STATS:
    for rule, opt in opts:
      name = opt[0]
      # TODO: abstract this
      src_root = local_get_root(opt[4]).getOpName()

      # FIXME: sanitize name
#       out.write('STATISTIC(Rule{0}, "{1}.{0}. {2}");\n'.format(rule, src_root, name))

#   if SIMPLIFY:
#     out.write('''
#   if (Value *V = SimplifyInstruction(I, SQ)) {
#     return replaceInstUsesWith(*I, V);
#   }
# ''')

  phs = []

  # sort opts by root opcode
  for opt in opts:
    root_opts[local_get_root(opt[1][4]).getOpName()].append(opt)
    name, pre, src_bb, tgt_bb, src, tgt, src_used, tgt_used, tgt_skip = opt[1]
    phs.append(peepholeopt(name, pre, src, tgt))

  Patterns = []
  for ph in phs:
    Patterns.append(ph.src_tree)

  prefix = prefix_tree(None, 0)
  
  AB = AutomataBuilder()
  startState = AB.localGetNext()
  AB.automaton.addState(startState)
  AB.automaton.initializeState(startState)
  AB.createAutomaton(startState, prefix, Patterns)

  AB.automaton.dump()
  AB.automaton.show('automaton')
  print(AB.pos)
