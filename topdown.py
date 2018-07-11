
import argparse, glob, re, sys
from itertools import izip,count
from language import *
from value import *
from automata import *

from pdb import set_trace

DO_STATS = True
SIMPLIFY = True
LIMITER = False

Notequal = u'\u2260'
#Notequal = 'Sink'

############################# Helper functions ###########################

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
  assert(symbol in twoOperands or symbol[0] is 'C'), "Arity doesn't support {} yet".format(symbol)
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

  def subtree(self, path):
    st = self.root
    reversedPath = list(path)
    reversedPath.reverse()
    if reversedPath is not None:
      for i in reversedPath:
        assert(i in range(1, tree.numOperands(st) + 1)), "Position outside range"
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
    # TODO: Enforce one or the other, not both node and node.symbol being None
    if node is None or node.symbol is None:
      paths.append(current_path)
    else:
      nchildren = node.numOfChildren()
      for i in range(1, nchildren + 1):
        newCurrentPath = list(current_path)
        c = node.childAt(i)
        newCurrentPath.append(i)
        node.localwildcardPaths(c, newCurrentPath, paths)

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
  
  @staticmethod
  def symbolsAt(path, P, isvar = False):
    F = set()
    if not isvar:
      for ph in P:
        p = ph.src_tree
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
    for ph in P:
      p = ph.src_tree
      subp = p.subtree(path)
      if (isinstance(subp, Instr) and subp.getOpName() is f) or (isConstValue(subp)):
        newP.append(ph)
    return newP

  @staticmethod
  def patternsWithVariablesAt(P, path):
    V = []
    for ph in P:
      p = ph.src_tree
      subt = p.subtree(path)
      if isWildcard(subt):
        V.append(ph)
    return V

  # Applies renaming of states
  def applyDFARename(self):
    if len(self.pos) is not 0:
      # template for format, basically says <unique state id>@<path to be checked>
      template = "{}@{}"
      newDFA = DFA()
      # Rename initial state
      newDFA.initializeState(template.format(self.automaton.init, self.pos[self.automaton.init]))

      # Rename final states
      for s in self.automaton.final:
        newDFA.finalizeState(template.format(s, self.pos[s]))

      # Rename states
      for s in self.automaton.states:
        newDFA.addState(template.format(s, self.pos[s]))
      
      # Rename transitions
      for src,edg in self.automaton.graph.items():
        for sym,dst in edg.items():
          for d in dst:
            #print("from {} to {}, using symbol {}".format(src, d, sym))
            src_str = template.format(src, self.pos[src])
            dst_str = template.format(d, self.pos[d])
            newDFA.addTransition(sym, src_str, dst_str)

      # clear lookup table
      self.pos = {}
      self.automaton = newDFA

  # s : current state
  # e : prefix tree
  # P : list of patterns
  def createAutomaton(self, s, e, P, sinkState = None):
    assert(len(P) is not 0), "Can't generate automaton using 0 patterns"
    M = set(p for p in P if peepholeopt.subsumes(p.src_tree, e))
    #if len(M) != 0 and matches(P,M):
    # TODO: rephrase acceptance condition...
    if len(P) is 1:
      self.automaton.finalizeState(s)
      self.pos[s] = P[0].name
    else:
      path = choosePath(e, P)
      self.pos[s] = path if len(path) is not 0 else 'empty'
      V = AutomataBuilder.patternsWithVariablesAt(P, path)
      if len(V) != 0:
        sinkState = str(self.localGetNext())
        self.automaton.addState(str(sinkState))
        self.automaton.addTransition(Notequal, s, str(sinkState))
        st = prefix_tree(Notequal, 0)
        e.replaceAt2(path, st)
        self.createAutomaton(str(sinkState), e, V, None)
      elif sinkState is not None and len(V) == 0:
        self.automaton.addTransition(Notequal, s, str(sinkState))

      F =  self.symbolsAt(path, P)
      for f in F:
        freshState = str(self.localGetNext())
        self.automaton.addState(str(freshState))
        #self.automaton.addTransition("{} = {}".format(self.pos[s], f), s, str(freshState))
        self.automaton.addTransition(f, s, str(freshState))
        st = prefix_tree(f, arity(f))
        recursP = AutomataBuilder.recursiveP(f, P, path)
        e.replaceAt2(path, st)
        self.createAutomaton(str(freshState), e, recursP, sinkState)

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

  prefix = prefix_tree(None, 0)
  
  AB = AutomataBuilder()
  startState = AB.localGetNext()
  AB.automaton.addState(str(startState))
  AB.automaton.initializeState(str(startState))
  AB.createAutomaton(str(startState), prefix, phs)

  AB.automaton.dump()
  AB.automaton.show('PREautomaton')
  AB.applyDFARename()
  AB.automaton.dump()
  AB.automaton.show('POSTautomaton')
