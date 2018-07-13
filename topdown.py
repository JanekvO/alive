
import argparse, glob, re, sys
from enum import Enum
from itertools import izip,count
from language import *
from value import *
from automata import *

from pdb import set_trace

DO_STATS = True
SIMPLIFY = True
LIMITER = False

#Notequal = u'\u2260'
Notequal = '%Sink'

############################# Helper functions ###########################

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
# TODO: clean up functions like this, should properly make tree class(es)
# to hide functionality like this in
def arity(symbol):
  #assert(symbol in twoOperands or symbol[0] is 'C'), "Arity doesn't support {} yet".format(symbol)
  if symbol in twoOperands:
    return 2
  return 0

######################################################

# FIXME: Replace these enums with classes considering python 2.7 doesn't
# support enums unless installing the backported version
class NodeType(Enum):
  ConstVal = 1
  ConstWildcard = 2
  Wildcard = 3
  Operation = 4

class TreeNode(object):
  def __init__(self, symbol, numOfChildren):
    self.symbol = symbol
    self.children = []
    for i in range(numOfChildren):
      self.children.append(None)
  
  def nodeType(self):
    pass
  
  def numOfChildren(self):
    return len(self.children)
  
  # p1 subsumes p2 if p2 is an instance of p1
  @staticmethod
  def subsumption(p1, p2):
    # if p1 is a wildcard, then always true
    if p1.nodeType() is NodeType.Wildcard:
      return True
    # at this point p1 is known to not be a wildcard, p2 being none denotes a 
    # wildcard to be filled in therefore we know it's not subsumed
    elif p2 is None or p2.symbol is None:
      return False
    # if p1 is a constant wildcard (e.g. C, C1, C2, ...), then only true if
    # p2 is either a constant wildcard or constant value (e.g. -1, 1, 2, 3, ...)
    elif p1.nodeType() is NodeType.ConstWildcard and \
        (p2.nodeType() is NodeType.ConstWildcard or p2.nodeType() is NodeType.ConstVal):
      return True
    # true if p1 and p2 are (the same) constant values
    elif p1.nodeType() is NodeType.ConstVal and p2.nodeType() is NodeType.ConstVal and \
          p1.symbol is p2.symbol:
      return True
    # if both are operations and their symbols match, recurs on their children.
    # if all children of p1 subsume children of p2, return true
    elif p1.nodeType() is NodeType.Operation and p2.nodeType() is NodeType.Operation and \
          p1.symbol is p2.symbol:
          p1OperandNum = p1.numOfChildren()
          p2OperandNum = p2.numOfChildren()
          assert(p1OperandNum is p2OperandNum), "Operation with multiple possible arities is not possible"
          for i in range(1, p1OperandNum + 1):
            if TreeNode.subsumes(p1.childAt(i), p2.childAt(i)) is False:
              return False
          return True
    # catch all, return false
    else:
      return False
  
  # self subsumes p if p is an instance of self
  def subsumes(self, p):
    #self.dump()
    #p.dump()
    return TreeNode.subsumption(self, p)
  
  def subtreeExists(self, path):
    return (self.subtree(path) is not None)

  def subtree(self, path):
    curTree = self
    for i in path:
      if curTree is None or len(curTree.children) is 0:
        return None
      curTree = curTree.childAt(i)
    return curTree
  
  def replaceAt(self, path, using):
    if (len(path) is 0):
      self.symbol = using.symbol
      self.children = using.children
    elif (len(path) is 1):
      i = path[0]
      self.addChild(using, i)
    else:
      self.childAt(path[0]).replaceAt(path[1:], using)

  def addChild(self, child, at):
    self.children[at - 1] = child

  def childAt(self, index):
    return self.children[index - 1]
  
  def dump(self):
    self.localprint("", True)
  
  def localprint(self, prefix, isLastChild):
    infix = "L-- " if isLastChild is True else "|-- "
    print(str(prefix) + infix + str(self.symbol))
    for i in range(self.numOfChildren(), 1, -1):
      suffix = "    " if isLastChild is True else "|   "
      if self.childAt(i) is not None:
        self.childAt(i).localprint(str(prefix) + suffix, False)
      else:
        print(prefix + suffix + '--- ' + "None")
    if self.numOfChildren() > 0:
      finalInfix = "    " if isLastChild is True else "|   "
      if self.childAt(1) is not None:
        self.childAt(1).localprint(str(prefix) + finalInfix, True)
      else:
        print(prefix + finalInfix + '--- ' + "None")

class ExpressionTree(TreeNode):
  def __init__(self, instr):
    self.expr = instr
    self.children = []
    self.populate()
  
  def populate(self):
    nt = self.nodeType()
    if nt is NodeType.Operation:
      self.symbol = self.expr.getOpName()

      # TODO: Replace this with something a bit more generic, since only binary
      # operations are supported for now (and we know how the BinOp class
      # looks like) we can get away with this hard coded part
      self.children.append(ExpressionTree(self.expr.v1))
      self.children.append(ExpressionTree(self.expr.v2))

    elif nt is NodeType.Wildcard or nt is NodeType.ConstWildcard:
      self.symbol = self.expr.getName()
    elif nt is NodeType.ConstVal:
      # TODO: Don't like refering to class variables directly but I really need the value
      self.symbol = str(self.expr.val)
    
  def nodeType(self):
    ret = None
    if isinstance(self.expr, Instr):
      ret = NodeType.Operation
    elif isinstance(self.expr, Input):
      if self.expr.getName()[0] is 'C':
        ret = NodeType.ConstWildcard
      elif self.expr.getName()[0] is '%':
        ret = NodeType.Wildcard
    elif self.expr.isConst():
      ret = NodeType.ConstVal
    elif isinstance(self.expr, CnstBinaryOp):
      pass
    elif isinstance(self.expr, CnstUnaryOp):
      pass
    if ret is None:
      raise Exception('ExpressionTree\'s type unknown or not implemented yet')
    return ret

class PrefixTree(TreeNode):
  def __init__(self, symbol, numOfChildren):
    super(PrefixTree, self).__init__(symbol, numOfChildren)
  
  def nodeType(self):
    ret = None
    if len(self.children) > 0:
      ret = NodeType.Operation
    elif self.symbol[0] is 'C':
      ret = NodeType.ConstWildcard
    elif self.symbol[0] is '%':
      ret = NodeType.Wildcard
    else:
      ret = NodeType.ConstVal
    return ret

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

######################################################

class peepholeopt(object):
  def __init__(self, name, pre, source, target):
    self.name = name
    self.pre = pre
    self.source = source
    self.target = target

    self.src_tree = ExpressionTree(local_get_root(source))
    # Not necessary to put target in a ExpressionTree as we don't do any
    # matching on it.
    self.tgt_root = local_get_root(target)

######################################################

class counter(object):
  def __init__(self):
    self.id = 0
  
  def getNext(self):
    current = self.id
    self.id = self.id + 1
    return current

######################################################

# TODO: return valid priority
def priority(pat):
  return 1

######################################################

class Chooser(object):
  def makeChoice(self, prefix, P):
    pass

# Chooses first available path (usually boils down to left-to-right)
class naiveChoice(Chooser):
  def makeChoice(self, prefix, P):
    paths = prefix.findWildcardPaths()
    return paths[0]

# Chooses path with most amount of symbols at path, for all patterns
class discriminatingChoice(Chooser):
  def makeChoice(self, prefix, P):
    paths = prefix.findWildcardPaths()
    currentMax = (0, [])
    for path in paths:
      symbols = AutomataBuilder.symbolsAt(path, P)
      (size, curPath) = currentMax
      if size < len(symbols):
        currentMax = (len(symbols), path)
    (size, path) = currentMax
    return path

# Chooses path with least amount of symbols at path, for all patterns
class minimizedChoice(Chooser):
  def makeChoice(self, prefix, P):
    paths = prefix.findWildcardPaths()
    currentMin = (sys.maxint, [])
    for path in paths:
      symbols = AutomataBuilder.symbolsAt(path, P)
      (size, curPath) = currentMin
      if size > len(symbols):
        currentMin = (len(symbols), path)
    (size, path) = currentMin
    return path

def createChooser(choice):
  if choice is naiveChoice:
    return naiveChoice()
  elif choice is discriminatingChoice:
    return discriminatingChoice()
  elif choice is minimizedChoice:
    return minimizedChoice()
  else:
    raise TypeError('This path chooser does not exist.')

######################################################

class AutomataBuilder(object):
  def __init__(self, chooser):
    self.pos = {}
    self.automaton = DFA()
    self.count = counter()
    self.chooser = createChooser(chooser)

  def localGetNext(self):
    return self.count.getNext()
  
  @staticmethod
  def symbolsAt(path, P, isvar = False):
    F = set()
    if not isvar:
      for ph in P:
        p = ph.src_tree
        f = p.subtree(path)
        if f is not None:
          if f.nodeType() is NodeType.Operation:
            F.add(f.symbol)
          elif f.nodeType() is NodeType.ConstVal or f.nodeType() is NodeType.ConstWildcard:
            F.add(f.symbol)
    return F

  # Calculate new P for recursive call, note that the new P is ALWAYS a subset
  # of the old P
  @staticmethod
  def recursiveP(f, P, path):
    newP = []
    for ph in P:
      p = ph.src_tree
      subp = p.subtree(path)
      # don't like subp return None thing going on, but how else to denote that
      # no path exists for p?
      if subp is not None:
        nt = subp.nodeType()
        if (nt is NodeType.Operation and subp.symbol is f) or \
            (nt is NodeType.ConstWildcard) or \
            (nt is NodeType.ConstVal):
          newP.append(ph)
    return newP

  @staticmethod
  def patternsWithVariablesAt(P, path):
    V = []
    for ph in P:
      p = ph.src_tree
      subt = p.subtree(path)
      if subt is not None and subt.nodeType() is NodeType.Wildcard:
        V.append(ph)
    return V

  @staticmethod
  def exists(p, M):
    for m in M:
      if priority(m) >= priority(p):
        return True
    return False

  @staticmethod
  def acceptancCondition(P, M):
    for p in P:
      if not AutomataBuilder.exists(p, M):
        return False
    return True

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
    print("s:{}\te:{}\tP:{}".format(s, e.symbol, P))
    M = set(p for p in P if p.src_tree.subsumes(e))
    if len(M) is not 0 and AutomataBuilder.acceptancCondition(P, M) and len(P) is 1:
      self.automaton.finalizeState(s)
      self.pos[s] = M.pop().name
    else:
      path = self.chooser.makeChoice(e, P)
      self.pos[s] = path if len(path) is not 0 else 'empty'
      V = AutomataBuilder.patternsWithVariablesAt(P, path)
      if len(V) != 0:
        sinkState = str(self.localGetNext())
        self.automaton.addState(str(sinkState))
        self.automaton.addTransition(Notequal, s, str(sinkState))
        st = PrefixTree(Notequal, 0)
        e.replaceAt(path, st)
        self.createAutomaton(str(sinkState), e, V, None)
      elif sinkState is not None and len(V) == 0:
        self.automaton.addTransition(Notequal, s, str(sinkState))

      F =  self.symbolsAt(path, P)
      for f in F:
        freshState = str(self.localGetNext())
        self.automaton.addState(str(freshState))
        self.automaton.addTransition(f, s, str(freshState))
        st = PrefixTree(f, arity(f))
        recursP = AutomataBuilder.recursiveP(f, P, path)
        e.replaceAt(path, st)
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

  prefixDc = PrefixTree(None, 0)
  prefixNc = PrefixTree(None, 0)
  prefixMc = PrefixTree(None, 0)
  
  ABdc = AutomataBuilder(discriminatingChoice)
  ABnc = AutomataBuilder(naiveChoice)
  ABmc = AutomataBuilder(minimizedChoice)

  startStateDc = ABdc.localGetNext()
  startStateNc = ABnc.localGetNext()
  startStateMc = ABmc.localGetNext()

  ABdc.automaton.addState(str(startStateDc))
  ABdc.automaton.initializeState(str(startStateDc))
  ABdc.createAutomaton(str(startStateDc), prefixDc, phs)

  ABnc.automaton.addState(str(startStateNc))
  ABnc.automaton.initializeState(str(startStateNc))
  ABnc.createAutomaton(str(startStateNc), prefixNc, phs)

  ABmc.automaton.addState(str(startStateMc))
  ABmc.automaton.initializeState(str(startStateMc))
  ABmc.createAutomaton(str(startStateMc), prefixMc, phs)

  ABdc.applyDFARename()
  ABdc.automaton.dump()
  ABdc.automaton.show('automaton_discriminating')

  ABnc.applyDFARename()
  ABnc.automaton.dump()
  ABnc.automaton.show('automaton_naive')

  ABmc.applyDFARename()
  ABmc.automaton.dump()
  ABmc.automaton.show('automaton_minimizing')
