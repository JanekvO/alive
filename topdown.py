
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
Notequal = 'Sink'
ConstWC = 'C*'
WC = '%*'

############################# Helper functions ###########################

def local_get_root(src):
  values = src.values()
  root = values.pop()
  while not isinstance(root, Instr):
    root = values.pop()
  return root

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

  @staticmethod
  def retrieveOperands(expression):
    ret = []
    if isinstance(expression, ConversionOp) or \
        isinstance(expression, CopyOperand):
      ret.append(expression.v)
      return ret
    elif isinstance(expression, BinOp) or \
          isinstance(expression, Icmp):
      ret.append(expression.v1)
      ret.append(expression.v2)
      return ret
    # This is a pretty stupid way of checking, but checking for an instance of
    # the Select class causes an error
    elif isinstance(expression, Instr) and \
          expression.getOpName() is 'select':
      ret.append(expression.c)
      ret.append(expression.v1)
      ret.append(expression.v2)
      return ret
    elif isinstance(expression, Br):
      ret.append(expression.cond)
      ret.append(expression.true)
      ret.append(expression.false)
      return ret
    elif isinstance(expression, Ret):
      ret.append(expression.val)
      return ret
    # TODO: more fitting exception
    raise Exception('Operation does not exist or is not supported yet')
  
  def populate(self):
    nt = self.nodeType()
    if nt is NodeType.Operation:
      self.symbol = self.expr.getOpName()
      ch = ExpressionTree.retrieveOperands(self.expr)
      for c in ch:
        self.children.append(ExpressionTree(c))
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

ArityLookup = {
  'trunc' : 1,
  'zext' : 1,
  'sext' : 1,
  'ZExtOrTrunc' : 1,
  'ptrtoint' : 1,
  'inttoptr' : 1,
  'bitcast' : 1,
  'ret' : 1,
  'add' : 2,
  'sub' : 2,
  'mul' : 2,
  'udiv' : 2,
  'sdiv' : 2,
  'urem' : 2,
  'srem' : 2,
  'shl' : 2,
  'ashr' : 2,
  'lshr' : 2,
  'and' : 2,
  'or' : 2,
  'xor' : 2,
  'icmp' : 2,
  'select' : 3,
  'br' : 3
}

class PrefixTree(TreeNode):
  def __init__(self, symbol, numOfChildren):
    super(PrefixTree, self).__init__(symbol, numOfChildren)
  
  @staticmethod
  def arity(symbol):
    if symbol in ArityLookup:
      return ArityLookup[symbol]
    return 0

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

    if len(paths) > 0:
      currentMax = (0, paths[0])
    else:
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

    if len(paths) > 0:
      currentMin = (sys.maxint, paths[0])
    else:
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
  def __init__(self, chooser, prioritytable):
    self.pos = {}
    self.automaton = DFA()
    self.count = counter()
    self.chooser = createChooser(chooser)
    self.PriorityLookup = prioritytable

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
          elif f.nodeType() is NodeType.ConstVal:
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
            (nt is NodeType.ConstVal and subp.symbol is f):
          newP.append(ph)
    return newP

  @staticmethod
  def patternsWithWCAt(P, path):
    V = []
    for ph in P:
      p = ph.src_tree
      subt = p.subtree(path)
      if subt is not None and subt.nodeType() is NodeType.Wildcard:
        V.append(ph)
    return V

  @staticmethod
  def patternsWithConstWCAt(P, path):
    V = []
    for ph in P:
      p = ph.src_tree
      subt = p.subtree(path)
      if subt is not None and subt.nodeType() is NodeType.ConstWildcard:
        V.append(ph)
    return V

  @staticmethod
  def patternsWithVariablesAt(P, path):
    V = []
    for ph in P:
      p = ph.src_tree
      subt = p.subtree(path)
      if subt is not None and (subt.nodeType() is NodeType.Wildcard or \
          subt.nodeType() is NodeType.ConstWildcard):
        V.append(ph)
    return V

  def exists(self, p, M):
    for m in M:
      if self.priority(m) >= self.priority(p):
        return True
    return False

  def acceptancCondition(self, P, M):
    for p in P:
      if not self.exists(p, M):
        return False
    return True

  def priority(self, pat):
    return self.PriorityLookup[pat]

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
  
  # Used to make any sink states more specific to either ConstWildcard or regular
  # Wildcard. This diverges from literature as regular literature assumes a single
  # form of wildcard, whereas in our case the subsumption is as follows:
  # wildcards > ConstWildcards > Constants 
  def constrainSink(self, s, e, V, path):
    nodeTypes = set()
    for p in V:
      subtree = p.src_tree.subtree(path)
      nodeTypes.add(subtree.nodeType())

    assert(NodeType.ConstWildcard in nodeTypes or \
            NodeType.Wildcard in nodeTypes), 'No (constant) wildcard in sink state, why does this state exist?'
    self.pos[s] = path if len(path) is not 0 else 'empty'

    PWithConstWC = AutomataBuilder.patternsWithConstWCAt(V, path)
    PWithNotConstWC = AutomataBuilder.patternsWithWCAt(V, path)

    sinkState = None
    if NodeType.Wildcard in nodeTypes:
      WCState = str(self.localGetNext())
      self.automaton.addState(WCState)
      self.automaton.addTransition(WC, s, WCState)
      sinkState = WCState
      st = PrefixTree(WC, 0)
      e.replaceAt(path, st)
      self.createAutomaton(WCState, e, PWithNotConstWC, None)
    if NodeType.ConstWildcard in nodeTypes:
      ConstWCState = str(self.localGetNext())
      self.automaton.addState(ConstWCState)
      self.automaton.addTransition(ConstWC, s, ConstWCState)
      st = PrefixTree(ConstWC, 0)
      e.replaceAt(path, st)
      self.createAutomaton(ConstWCState, e, PWithConstWC, sinkState)

  # s : current state
  # e : prefix tree
  # P : list of patterns
  def createAutomaton(self, s, e, P, sinkState = None):
    assert(len(P) is not 0), "Can't generate automaton using 0 patterns"
    print("s:{}\te:{}\tP:{}".format(s, e.symbol, len(P)))
    M = set(p for p in P if p.src_tree.subsumes(e))
    if len(M) is not 0 and self.acceptancCondition(P, M):
      self.automaton.finalizeState(s)
      m = M.pop()
      while (len(M) > 0):
        n = M.pop()
        if self.priority(n) > self.priority(m):
          m = n
      self.pos[s] = m.name
    else:
      path = self.chooser.makeChoice(e, P)
      self.pos[s] = path if len(path) is not 0 else 'empty'
      V = AutomataBuilder.patternsWithVariablesAt(P, path)
      F =  self.symbolsAt(path, P)
      if len(V) != 0:
        eDeepcopy = copy.deepcopy(e)
        sinkState = str(self.localGetNext())
        self.automaton.addState(str(sinkState))
        self.automaton.addTransition(Notequal, s, str(sinkState))
        st = PrefixTree(Notequal, 0)
        eDeepcopy.replaceAt(path, st)
        self.constrainSink(sinkState, eDeepcopy, V, path)
        #self.createAutomaton(str(sinkState), e, V, None)
      elif sinkState is not None and len(V) == 0:
        self.automaton.addTransition(Notequal, s, str(sinkState))

      for f in F:
        eDeepcopy = copy.deepcopy(e)
        freshState = str(self.localGetNext())
        self.automaton.addState(str(freshState))
        self.automaton.addTransition(f, s, str(freshState))
        st = PrefixTree(f, PrefixTree.arity(f))
        recursP = AutomataBuilder.recursiveP(f, P, path)
        eDeepcopy.replaceAt(path, st)
        self.createAutomaton(str(freshState), eDeepcopy, recursP, sinkState)

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

  PriorityLookup = {p:(len(phs) - i) for i,p in enumerate(phs)}

  prefixDc = PrefixTree(None, 0)
  prefixNc = PrefixTree(None, 0)
  prefixMc = PrefixTree(None, 0)
  
  ABdc = AutomataBuilder(discriminatingChoice, PriorityLookup)
  ABnc = AutomataBuilder(naiveChoice, PriorityLookup)
  ABmc = AutomataBuilder(minimizedChoice, PriorityLookup)

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
