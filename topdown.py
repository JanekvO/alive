
import argparse, glob, re, sys
from itertools import izip,count
from value import *
from automata import *
from collections import deque
from precondition import *
from gen import MatchBuilder, CodeGenerator, minimal_type_constraints, get_root
from codegen import *
from treepatternmatching import *
from topologicalorder import *

from pdb import set_trace

DO_STATS = True
SIMPLIFY = True
LIMITER = False

Notequal = u'\u2260'
#Notequal = 'Sink'
ConstWC = 'C*'

############################# Helper functions ###########################

def local_get_root(src):
  values = src.values()
  root = values.pop()
  while not isinstance(root, Instr):
    root = values.pop()
  return root

######################################################

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
  'addnsw' : 2,
  'addnuw' : 2,
  'addnswnuw' : 2,
  'sub' : 2,
  'subnsw' : 2,
  'subnuw' : 2,
  'subnswnuw' : 2,
  'mul' : 2,
  'mulnsw' : 2,
  'mulnuw' : 2,
  'mulnswnuw' : 2,
  'udiv' : 2,
  'udivexact' : 2,
  'sdiv' : 2,
  'sdivexact' : 2,
  'urem' : 2,
  'srem' : 2,
  'shl' : 2,
  'shlnsw' : 2,
  'shlnuw' : 2,
  'shlnswnuw' : 2,
  'ashr' : 2,
  'ashrexact' : 2,
  'lshr' : 2,
  'lshrexact' : 2,
  'and' : 2,
  'or' : 2,
  'xor' : 2,
  'icmpeq' : 2,
  'icmpne' : 2,
  'icmpugt' : 2,
  'icmpuge' : 2,
  'icmpult' : 2,
  'icmpule' : 2,
  'icmpsgt' : 2,
  'icmpsge' : 2,
  'icmpslt' : 2,
  'icmpsle' : 2,
  'select' : 3,
  'br' : 3
}

class TDExprTree(ExpressionTree):
  def __init__(self, instr):
    self.expr = instr
    self.children = []
    self.populate()
  
  # FIXME: stop relying on strings for flag matching
  def getSymbol(self):
    s = self.symbol
    if isinstance(self.expr, Icmp):
      s = s + Icmp.opnames[self.expr.op]
    elif isinstance(self.expr, BinOp):
      if 'nsw' in self.expr.flags:
        s = s + 'nsw'
      if 'nuw' in self.expr.flags:
        s = s + 'nuw'
      if 'exact' in self.expr.flags:
        s = s + 'exact'
    return s
  
  def populate(self):
    nt = self.nodeType()
    if nt is NodeType.Operation:
      self.symbol = self.expr.getOpName()
      ch = ExpressionTree.retrieveOperands(self.expr)
      for c in ch:
        self.children.append(TDExprTree(c))
    elif nt is NodeType.Wildcard or nt is NodeType.ConstWildcard:
      self.symbol = self.expr.getName()
    elif nt is NodeType.ConstVal:
      # TODO: Don't like refering to class variables directly but I really need the value
      self.symbol = str(self.expr.val)
      self.val = self.expr.val
    
  def nodeType(self):
    return ExpressionTree.retrieveExprType(self.expr)

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
    if self.symbol is not None:
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

class TDpeepholeopt(peepholeoptimization):
  def __init__(self, rule, name, pre, source, target, target_skip):
    super(TDpeepholeopt, self).__init__(rule, name, pre, source, target, target_skip)
    self.cg = TopDownCodeGenerator()

    self.src_tree = TDExprTree(local_get_root(source))
    # Not necessary to put target in a TDExprTree as we don't do any
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
      symbols = PatternHelper.symbolsAt(path, P)
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
      symbols = PatternHelper.symbolsAt(path, P)
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

class StateAuxiliary(object):
  def __init__(self, prefix, patterns, path=None, accepting=False, sink=None):
    self.prefix = prefix
    self.patterns = patterns
    self.path = path
    self.accepting = accepting
    self.sink = sink

######################################################

class AutomataBuilder(object):
  def __init__(self, chooser, prioritytable):
    self.stateAuxData = {}
    self.automaton = DFA()
    self.count = counter()
    self.chooser = createChooser(chooser)
    self.PriorityLookup = prioritytable

  def localGetNext(self):
    return self.count.getNext()
  
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
        if (nt is NodeType.Operation and subp.getSymbol() == f) or \
            (nt is NodeType.ConstVal and subp.getSymbol() == f):
          newP.append(ph)
    return newP

  def show(self, filename):
    dfa = self.automaton
    addedNodes = []
    dot = Digraph(format='xdot')
    addedNodes.append(dfa.init)
    for fs in dfa.final:
      addedNodes.append(fs)
    dot.node(str(dfa.init), 'initial')
    for fs in dfa.final:
      acSt = list(self.stateAuxData[fs].patterns)[0]
      # Sanitize for graphviz
      sanitize = {' ' : '', ':': '_'}
      name = acSt.name
      for b,a in sanitize.items():
        name = name.replace(b, a)
      dot.node(fs, name, { 'color' : 'green' })
    for src,edg in dfa.graph.items():
      if src not in addedNodes:
        sState = self.stateAuxData[src]
        dot.node(str(src), str(sState.path))
      addedNodes.append(src)
      for sym,dst in edg.items():
        for d in dst:
          if d not in addedNodes:
            addedNodes.append(d)
            dState = self.stateAuxData[d]
            dot.node(str(d), str(dState.path))
          dot.edge(str(src), str(d), sym)
    dot.render(filename, cleanup=True)
  
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

  #FIXME: priority should be given to the least subsuming (i.e. most specific
  # pattern)
  def priority(self, pat):
    return self.PriorityLookup[pat]

  # Used to make any sink states more specific to either ConstWildcard or regular
  # Wildcard. This diverges from literature as regular literature assumes a single
  # form of wildcard, whereas in our case the subsumption is as follows:
  # wildcards > ConstWildcards > Constants 
  def createSink(self, s, e, V, path):
    nodeTypes = set()
    for p in V:
      subtree = p.src_tree.subtree(path)
      nodeTypes.add(subtree.nodeType())

    assert(NodeType.ConstWildcard in nodeTypes or \
            NodeType.Wildcard in nodeTypes), 'No (constant) wildcard in sink state, why does this state exist?'
    self.stateAuxData[s] = StateAuxiliary(e, V, path=path)

    PWithConstWC = PatternHelper.patternsWithConstWCAt(V, path)
    PWithNotConstWC = PatternHelper.patternsWithWCAt(V, path)

    if NodeType.Wildcard in nodeTypes:
      eSink = copy.deepcopy(e)
      WCState = str(self.localGetNext())
      self.automaton.addState(WCState)
      self.automaton.addTransition(Notequal, s, WCState)
      st = PrefixTree(Notequal, 0)
      eSink.replaceAt(path, st)
      self.createAutomaton(WCState, eSink, PWithNotConstWC)
    else:
      divergingSink = self.closestDivergingSink(s)
      if divergingSink is not None:
        self.automaton.addTransition(Notequal, s, divergingSink)

    if NodeType.ConstWildcard in nodeTypes:
      eCWC = copy.deepcopy(e)
      ConstWCState = str(self.localGetNext())
      self.automaton.addState(ConstWCState)
      self.automaton.addTransition(ConstWC, s, ConstWCState)
      st = PrefixTree(ConstWC, 0)
      eCWC.replaceAt(path, st)
      self.createAutomaton(ConstWCState, eCWC, PWithConstWC)

  def closestDivergingSink(self, s):
    dfa = self.automaton.graph
    parents = [s]
    markedStates = set([])
    while len(parents) is not 0:
      curState = parents.pop()
      for src,edg in dfa.items():
        for sym,dst in edg.items():
          if curState is dst[0] and curState not in markedStates:
            parents.append(src)
            markedStates.add(curState)
            if Notequal in dfa[src] and curState not in dfa[src][Notequal]:
              return dfa[src][Notequal][0]
    return None

  # s : current state
  # e : prefix tree
  # P : list of patterns
  def createAutomaton(self, s, e, P):
    assert(len(P) is not 0), "Can't generate automaton using 0 patterns"
    #print("s:{}\te:{}\tP:{}".format(s, e.symbol, len(P)))
    # M = set(p for p in P if p.src_tree.subsumes(e))
    M = [p for p in P if p.src_tree.subsumes(e)]
    if len(M) is not 0 and self.acceptancCondition(P, M):
      self.automaton.finalizeState(s)
      m = M.pop()
      while (len(M) > 0):
        n = M.pop()
        if self.priority(n) > self.priority(m):
          m = n
      sink = self.closestDivergingSink(s)
      if sink is not None:
        self.automaton.addTransition(Notequal, s, sink)
      self.stateAuxData[s] = StateAuxiliary(copy.deepcopy(e), [m], accepting=True, sink=sink)
    else:
      path = self.chooser.makeChoice(e, P)
      self.stateAuxData[s] = StateAuxiliary(e, P, path=path)
      V = PatternHelper.patternsWithVariablesAt(P, path)
      F =  PatternHelper.symbolsAt(path, P)
      if len(V) != 0:
        eDeepcopy = copy.deepcopy(e)
        sinkState = str(self.localGetNext())
        self.automaton.addState(sinkState)
        self.automaton.addTransition(Notequal, s, sinkState)
        st = PrefixTree(Notequal, 0)
        eDeepcopy.replaceAt(path, st)
        self.createSink(sinkState, eDeepcopy, V, path)
      else:
        divergingSink = self.closestDivergingSink(s)
        if divergingSink is not None:
          self.automaton.addTransition(Notequal, s, divergingSink)

      for f in F:
        eDeepcopy = copy.deepcopy(e)
        freshState = str(self.localGetNext())
        self.automaton.addState(str(freshState))
        self.automaton.addTransition(f, s, str(freshState))
        st = PrefixTree(f, PrefixTree.arity(f))
        recursP = AutomataBuilder.recursiveP(f, P, path)
        eDeepcopy.replaceAt(path, st)
        self.createAutomaton(str(freshState), eDeepcopy, recursP)

######################################################
######################################################
######################################################
###############    codegen below    ##################
######################################################
######################################################
######################################################

class TopDownCodeGenerator(CodeGenerator):
  def __init__(self):
    super(TopDownCodeGenerator, self).__init__()
    self.duplicate = {}
  
  def bound(self, var):
    # Constants are never considered bound
    if isinstance(var, Constant):
      return False

    if isinstance(var, Value):
      return var in self.value_names and \
        self.value_names[var] in self.name_type
    
    return var in self.name_type

  
  def get_cexp(self, var):
    'Return a CExp referring to this name or value, also considering the type of variable'

    if isinstance(var, Constant):
      return var.get_Value(self)
    
    if isinstance(var, Value):
      name = var.getName()
      if name[0] is 'C':
        return CVariable(name)
      else:
        return CVariable(self.get_name(var))

# Basically a topdown version of the visit_source methods
class SourceVisitor(object):
  @staticmethod
  def visit(manager, tree, coordinate):
    val = tree.subtree(coordinate).expr
    if isinstance(val, BinOp):
      return SourceVisitor.BinOpVisit(manager, tree, coordinate)
    elif isinstance(val, Icmp):
      return SourceVisitor.IcmpVisit(manager, tree, coordinate)
    elif isinstance(val, Select):
      return SourceVisitor.SelectVisit(manager, tree, coordinate)
    elif isinstance(val, ConversionOp):
      return SourceVisitor.ConOpVisit(manager, tree, coordinate)
    else:
      # If all else fails, use the default visit_source
      mb = TopDownMatchBuilder(manager, val)
      return val.visit_source(mb), mb

  @staticmethod
  def BinOpVisit(manager, tree, coordinate):
    st = tree.subtree(coordinate)
    mb = TopDownMatchBuilder(manager, st.expr)
    r1_coordinate = copy.deepcopy(coordinate)
    r2_coordinate = copy.deepcopy(coordinate)
    r1_coordinate.append(1)
    r2_coordinate.append(2)
    r1 = mb.value_emit(st.childAt(1), r1_coordinate)
    r2 = mb.value_emit(st.childAt(2), r2_coordinate)

    op = BinOp.caps[st.expr.op]

    if 'nsw' in st.expr.flags and 'nuw' in st.expr.flags:
      return CFunctionCall('match',
        mb.get_my_ref(),
        CFunctionCall('m_CombineAnd',
          CFunctionCall('m_NSW' + op, r1, r2),
          CFunctionCall('m_NUW' + op,
            CFunctionCall('m_Value'),
            CFunctionCall('m_Value')))), mb

    if 'nsw' in st.expr.flags:
      return mb.simple_match('m_NSW' + op, r1, r2), mb

    if 'nuw' in st.expr.flags:
      return mb.simple_match('m_NUW' + op, r1, r2), mb

    if 'exact' in st.expr.flags:
      return CFunctionCall('match',
        mb.get_my_ref(),
        CFunctionCall('m_Exact', CFunctionCall('m_' + op, r1, r2))), mb
  
    # cast = CFunctionCall('static_cast<Instruction*>', mb.get_my_ref())
    # nswCheck = CFieldAccess(cast, \
    #   'hasNoSignedWrap()', direct=False)
    # nuwCheck = CFieldAccess(cast, \
    #   'hasNoUnsignedWrap()', direct=False)
    # exactCheck = CFieldAccess(cast, 'isExact()', direct=False)

    # if 'nsw' in st.expr.flags and 'nuw' in st.expr.flags:
    #   mb.extras.extend([nswCheck, nuwCheck])
    # elif 'nsw' in st.expr.flags:
    #   mb.extras.append(nswCheck)
    # elif 'nuw' in st.expr.flags:
    #   mb.extras.append(nuwCheck)
    # elif 'exact' in st.expr.flags:
    #   mb.extras.append(exactCheck)

    return mb.simple_match('m_' + op, r1, r2), mb

  @staticmethod
  def IcmpVisit(manager, tree, coordinate):
    st = tree.subtree(coordinate)
    mb = TopDownMatchBuilder(manager, st.expr)
    mb_precondition = TopDownMatchBuilder(TopDownCodeGenerator(), st.expr)
    r1_coordinate = copy.deepcopy(coordinate)
    r2_coordinate = copy.deepcopy(coordinate)
    r1_coordinate.append(1)
    r2_coordinate.append(2)
    r1 = mb.value_emit(st.childAt(1), r1_coordinate)
    r2 = mb.value_emit(st.childAt(2), r2_coordinate)

    if st.expr.op == Icmp.Var:
      opname = st.expr.opname if st.expr.opname else 'Pred ' + st.expr.name
      name = mb.manager.get_key_name(opname)  #FIXME: call via mb?
      rp = mb.binding(name, st.expr.PredType)

      return mb.simple_match('m_ICmp', rp, r1, r2), mb

    # Using a new match builder to prevent conflicts between multiple new_name calls
    # when variable P already exists
    pvar = mb_precondition.new_name(createVarUsingPath('P', coordinate))
    rp = mb_precondition.binding(pvar, st.expr.PredType)

    # Add to normal mb s.t. we can emit the variable itself
    if not mb.manager.bound(pvar):
      mb.binding(pvar, st.expr.PredType)

    matcher = CBinExpr('&&',
      mb.simple_match('m_ICmp', rp, r1, r2),
      CBinExpr('==', CVariable(pvar), CVariable(Icmp.op_enum[st.expr.op])))
    return matcher, mb
  
  @staticmethod
  def SelectVisit(manager, tree, coordinate):
    st = tree.subtree(coordinate)
    mb = TopDownMatchBuilder(manager, st.expr)
    c_coordinate = copy.deepcopy(coordinate)
    r1_coordinate = copy.deepcopy(coordinate)
    r2_coordinate = copy.deepcopy(coordinate)
    c_coordinate.append(1)
    r1_coordinate.append(2)
    r2_coordinate.append(3)
    c = mb.value_emit(st.childAt(1), c_coordinate)
    r1 = mb.value_emit(st.childAt(2), r1_coordinate)
    r2 = mb.value_emit(st.childAt(3), r2_coordinate)

    return mb.simple_match('m_Select', c, r1, r2), mb
  
  @staticmethod
  def ConOpVisit(manager, tree, coordinate):
    st = tree.subtree(coordinate)
    mb = TopDownMatchBuilder(manager, st.expr)
    v_coordinate = copy.deepcopy(coordinate)
    v_coordinate.append(1)
    r = mb.value_emit(st.childAt(1), v_coordinate)

    if st.expr.op == ConversionOp.ZExtOrTrunc:
      return CFunctionCall('match',
        mb.get_my_ref(),
        CFunctionCall('m_CombineOr',
          CFunctionCall('m_ZExt', r),
          CFunctionCall('m_ZTrunc', r)))

    return mb.simple_match(ConversionOp.matcher[st.expr.op], r), mb

class TopDownMatchBuilder(MatchBuilder):
  def subpattern(self, value):
    'Return a CExpr which matches the operand value and binds its variable (top-down version)'
    # TODO: generalize match builder

    assert isinstance(value, (Instr, Input, ConstantVal))

    if value not in self.bound:
      # removed the m_Specific matcher since we don't look for multiple same variables in TD
      self.bound.append(value)
      name = self.manager.get_name(value)
      # add equivalence condition for duplicates
      if value in self.manager.duplicate and \
          name in self.manager.duplicate[value]:
        dup = self.manager.duplicate[value]
        dup.remove(name)
        for d in dup:
          self.extras.append(CBinExpr('==', CVariable(name), CVariable(d)))
    else:
      # FIXME: if number of duplicates > 2, we're in trouble
      origin_name = self.manager.get_name(value)
      dupl_set = self.manager.duplicate[value] - set([origin_name])
      assert(len(dupl_set) == 1)
      name = list(dupl_set)[0]

    return CFunctionCall('m_Value', CVariable(name))
  
  def value_emit(self, tree, current_coordinate):
    value = tree.expr

    assert isinstance(value, (Instr, Input, ConstantVal))

    if value not in self.bound:
      self.bound.append(value)
      name = createVar(current_coordinate)
    else:
      # FIXME: if number of duplicates > 2, we're in trouble
      origin_name = self.manager.get_name(value)
      dupl_set = self.manager.duplicate[value] - set([origin_name])
      assert(len(dupl_set) == 1)
      name = list(dupl_set)[0]
    
    return CFunctionCall('m_Value', CVariable(name))

  @staticmethod
  def match_value(manager, tree, coordinate):
    ret, mb = SourceVisitor.visit(manager, tree, coordinate)
    return ret

def generate_precondition(manager, tree, coordinate):
  ret, mb = SourceVisitor.visit(manager, tree, coordinate)
  # add equivalence condition for duplicates
  for val,dup in mb.manager.duplicate.items():
    if len(dup) >= 2:
      name = dup.pop()
      for d in dup:
        mb.extras.append(CBinExpr('==', CVariable(name), CVariable(d)))
  return mb.extras

def generate_replacement(phopt):
  '''Takes a the peephole optimization for which we
  want to generate the replacement code'''
  rule = phopt.rule
  name = phopt.name
  pre = phopt.pre
  src = phopt.source
  tgt = phopt.target
  tgt_skip = phopt.target_skip
  cg = phopt.cg
  src_tree = phopt.src_tree

  root = local_get_root(src)
  clauses = []

  # This looks weird, but trust me, I know what I'm doing (he said, lying to himself)
  todo = [[]]

  while todo:
    coordinate = todo.pop(0)
    tree = src_tree.subtree(coordinate)
    if isinstance(tree.expr, Instr):
      precondition = generate_precondition(cg, src_tree, coordinate)
      clauses.extend(precondition)
      for i in range(1, tree.numOfChildren() + 1):
        next_coordinate = copy.deepcopy(coordinate)
        next_coordinate.append(i)
        todo.append(next_coordinate)
    tree.expr.register_types(cg)
      
  cg.phase = cg.Target
  
  pre.register_types(cg)

  for name in cg.named_types:
    cg.unify(*cg.named_types[name])
  
  tgt_vals = [v for k,v in tgt.iteritems() if not (isinstance(v,Input) or k in tgt_skip)]

  for value in tgt_vals:
    value.register_types(cg)
  
  root_name = root.getName()
  new_root = tgt[root_name]
  cg.unify(root, new_root)
  clauses.extend(cg.clauses)

  for v,t in cg.guaranteed.iteritems():
    if not cg.bound(v): continue

    clauses.extend(minimal_type_constraints(cg.get_llvm_type(v), cg.required[v], t))

  if not isinstance(pre, TruePred):
    clauses.append(pre.visit_pre(cg))
  
  if DO_STATS and LIMITER:
    clauses.append(CBinExpr('<', CVariable('Rule' + str(rule)), CVariable('10000')))

  body = []

  if DO_STATS:
    body = [CUnaryExpr('++', CVariable('Rule' + str(rule)))]

  for value in tgt_vals:
    if isinstance(value, Instr) and value != new_root:
      body.extend(value.visit_target(cg, True))
  
  if isinstance(new_root, CopyOperand):
    body.append(
      CDefinition.init(
        cg.PtrInstruction,
        cg.get_cexp(tgt[root_name]),
        CFunctionCall('replaceInstUsesWith', CVariable('*I'), cg.get_cexp(new_root.v))))
  else:
    body.extend(new_root.visit_target(cg, False))

  body.append(CReturn(cg.get_cexp(new_root)))

  return clauses, body

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
      out.write('STATISTIC(Rule{0}, "{1}.{0}. {2}");\n'.format(rule, src_root, name))

#   if SIMPLIFY:
#     out.write('''
#   if (Value *V = SimplifyInstruction(I, SQ)) {
#     return replaceInstUsesWith(*I, V);
#   }
# ''')

  phs = []

  # sort opts by root opcode
  for rule, opt in opts:
    root_opts[local_get_root(opt[4]).getOpName()].append(opt)
    name, pre, src_bb, tgt_bb, src, tgt, src_used, tgt_used, tgt_skip = opt
    phs.append(TDpeepholeopt(rule, name, pre, src, tgt, tgt_skip))

  topo = TreeTopoGraph()

  for ph1 in phs:
    topo.addVertex(ph1)
    for ph2 in phs:
      if ph1.src_tree == ph2.src_tree or ph1.src_tree.isNotComparable(ph2.src_tree):
        continue
      elif ph1.src_tree.subsumes(ph2.src_tree):
        topo.addEdge(ph2, ph1)
      elif ph2.src_tree.subsumes(ph1.src_tree):
        topo.addEdge(ph1, ph2)

  topo.show('nonreduced')
  topo.reduction()
  topo.show('reduced')

  priority = topo.topologicalSort()
  #PriorityLookup = {p:(len(phs) - i) for i,p in enumerate(priority)}
  PriorityLookup = {p:(len(phs) - i) for i,p in enumerate(phs)}

  prefixDc = PrefixTree(None, 0)
  
  ABdc = AutomataBuilder(discriminatingChoice, PriorityLookup)

  startStateDc = ABdc.localGetNext()

  ABdc.automaton.addState(str(startStateDc))
  ABdc.automaton.initializeState(str(startStateDc))
  ABdc.createAutomaton(str(startStateDc), prefixDc, phs)

  ABdc.show('automaton_discriminating')

  # Emit C++ code
  AB = ABdc
  autom = AB.automaton
  q = deque([autom.init])
  marked = set()
  stateFunctions = []
  usedVariables = {}
  maxVal = 0
  # There should be a better way than iterating and having this whole blob of code
  while len(q) is not 0:
    current = q.popleft()
    marked.add(current)
    dfa = autom.graph
    if current in dfa.keys():
      for sym,dsts in dfa[current].items():
        for dst in dsts:
          if dst not in marked:
            marked.add(dst)
            q.append(dst)
    
    stateFunctionBody = []
    currentStateAux = AB.stateAuxData[current]
    coordinate = currentStateAux.path

    print("current state processed: {}".format(current))

    if currentStateAux.accepting:
      originalName = list(currentStateAux.patterns)[0].name
      nm = originalName
      # Sanitize for graphviz
      sanitize = {' ' : '', ':': '_'}
      for b,a in sanitize.items():
        nm = nm.replace(b, a)
      
      # TODO: generate the replacement without basically creating pattern matching
      # of the old generator
      clauses,replacement = generate_replacement(list(currentStateAux.patterns)[0])
      comment = seq('//', originalName)
      stateFunctionBody.append(comment)
      if clauses:
        # In case the precondition fails, we need to check whether there exists a 
        # less specific state to fall back on. Note that this implicit transition
        # is NOT shown in the automaton
        if currentStateAux.sink is not None:
          elsebody = [CGoto(CLabel('state_{}'.format(currentStateAux.sink)))]
        else:
          elsebody = [CReturn(CVariable('nullptr'))]
        cif = CIf(CBinExpr.reduce('&&', clauses), \
          replacement, elsebody)
        stateFunctionBody.append(cif)
      else:
        stateFunctionBody.extend(replacement)

    else:
      #FIXME: a lot of matchbuilding is done here instead of its designated class
      iflist = []
      sink = False
      #for sym,ddst in dfa[current].items():
      for sym,ddst in sorted(dfa[current].items(), key=lambda s: len(s[0]), reverse=True):
        rooted_prefix = currentStateAux.prefix.subtree(coordinate)
        if sym is Notequal:
          sink = ddst[0]
        elif RepresentsInt(sym):
          source_tree = list(currentStateAux.patterns)[0].src_tree.subtree(coordinate)
          ifc_var = CVariable(sym)
          ifc_subexpr = CFunctionCall('m_SpecificInt', ifc_var)
          ifc = CFunctionCall('match', CVariable(createVar(coordinate)), ifc_subexpr)
          ifb = CGoto(CLabel('state_{}'.format(ddst[0])))
          iflist.append((ifc, [ifb]))
        elif sym is ConstWC:
          P = PatternHelper.patternsWithConstWCAt(currentStateAux.patterns, coordinate)
          assert(len(P) > 0), \
            'There should exists at least 1 pattern with const variable'
          body = []
          pat = list(P)[0]
          source_tree = pat.src_tree.subtree(coordinate)
          subexpr_str = str(source_tree.expr)
          ifc_var = CVariable(subexpr_str)
          ifc_subexpr = CFunctionCall('m_ConstantInt', ifc_var)
          ty = CPtrType(CTypeName('ConstantInt'))
          # Add to variables to emit
          if subexpr_str not in usedVariables:
            usedVariables[subexpr_str] = ty
          ifc = CFunctionCall('match', CVariable(createVar(coordinate)), ifc_subexpr)
          ifb = CGoto(CLabel('state_{}'.format(ddst[0])))
          accountedFor = set()
          accountedFor.add(subexpr_str)
          for p in P:
            pSubtree = p.src_tree.subtree(coordinate)
            pStr = str(pSubtree.expr)
            if pStr not in accountedFor:
              accountedFor.add(pStr)
              body.append(CAssign(CVariable(pStr), ifc_var))
              if pStr not in usedVariables:
                usedVariables[pStr] = ty
          body.append(ifb)
          iflist.append((ifc, body))
        else:
          P = PatternHelper.patternsWithSymbAt(currentStateAux.patterns, \
            coordinate, \
            sym)
          assert(len(P) > 0), \
            'There should exists at least 1 pattern for symbol {}'.format(sym)
          
          for p in P:
            exprtree = p.src_tree.subtree(coordinate)
            p.cg.value_names[exprtree.expr] = createVar(coordinate)
            if not p.cg.bound(exprtree.expr):
              p.cg.bind_value(exprtree.expr)
            for i in range(1, exprtree.numOfChildren() + 1):
              child = exprtree.childAt(i)
              assert(child is not None)
              childpath = list(coordinate)
              childpath.append(i)
              varName = createVar(childpath)
              #ctype = p.cg.value_ctype(child.expr)
              ctype = CPtrType(CTypeName('Value'))
              if child.expr not in p.cg.value_names:
                p.cg.value_names[child.expr] = varName
                p.cg.duplicate[child.expr] = set()
              p.cg.bind_name(varName, ctype)
              p.cg.duplicate[child.expr].add(varName)
          
          # Pick any pattern and continue with codegen
          pat = list(P)[0]
          source_tree = pat.src_tree.subtree(coordinate)
          cg = pat.cg
          ifc = TopDownMatchBuilder.match_value(cg, pat.src_tree, coordinate)
          ifb = CGoto(CLabel('state_{}'.format(ddst[0])))
          iflist.append((ifc, [ifb]))

          for n,t in cg.name_type.items():
            if n not in usedVariables:
              usedVariables[n] = t
      
      if sink:
        elsebody = [CGoto(CLabel('state_{}'.format(sink)))]
      else:
        # Cheating here, nullptr is technically not a variable
        elsebody = [CReturn(CVariable('nullptr'))]

      if len(iflist) > 0:
        stateFunctionBody.append(CElseIf(iflist, elsebody))
      else:
        stateFunctionBody.append(CMultiStatement(elsebody))

    functionString = 'state_{}'.format(current)
    stateFunctions.append((functionString, stateFunctionBody))


  maxVal = 0
  for s,e in autom.graph.items():
    maxVal += len(e)
    
  print("Number of edges: {}".format(maxVal))

  out.write('Instruction *InstCombiner::runOnInstruction(Instruction *I) {\n')
  varDecl_it = CDefinition.block((t, CVariable(n)) for n,t in usedVariables.iteritems())
  varDecl = iter_seq(line + d.format() for d in varDecl_it)
  varNest = nest(2, varDecl)
  out.write(varNest.format() + '\n')
  out.write('  x = I;\n  goto state_0;\n\n')

  for fn,b in stateFunctions:
    body_iter = (line + s.format() for s in b)
    body = seq(line, '{', iter_seq(body_iter), line, '}')
    case = nest(2, seq(line, fn + ':', body))
    out.write(case.format())

  out.write('\n}')
