from enum import Enum
from language import *

# FIXME: Replace these enums with classes considering python 2.7 doesn't
# support enums unless installing the backported version
class NodeType(Enum):
  ConstVal = 1
  ConstWildcard = 2
  Wildcard = 3
  Operation = 4

# General methods for patterns
class PatternHelper(object):
  @staticmethod
  def patternsWithTypesAt(path, P, types):
    F = set()
    for ph in P:
      p = ph.src_tree
      f = p.subtree(path)
      if f is not None:
        if f.nodeType() in types:
          F.add(ph)
    return F

  @staticmethod
  def symbolsAt(path, P):
    F = PatternHelper.patternsWithTypesAt(path, P, \
      [NodeType.Operation, NodeType.ConstVal])
    R = set()
    for f in F:
      subtree = f.src_tree.subtree(path)
      R.add(subtree.getSymbol())
    return R

  @staticmethod
  def patternsWithSymbAt(P, path, symb):
    F = set()
    for ph in P:
      p = ph.src_tree
      f = p.subtree(path)
      if f is not None and f.getSymbol() == symb:
        F.add(ph)
    return F

  @staticmethod
  def patternsWithWCAt(P, path):
    return list(PatternHelper.patternsWithTypesAt(path, P, [NodeType.Wildcard]))

  @staticmethod
  def patternsWithConstWCAt(P, path):
    return list(PatternHelper.patternsWithTypesAt(path, P, [NodeType.ConstWildcard]))

  @staticmethod
  def patternsWithVariablesAt(P, path):
    return list(PatternHelper.patternsWithTypesAt(path, P, \
      [NodeType.Wildcard, NodeType.ConstWildcard]))

class TreeNode(object):
  def __init__(self, symbol, numOfChildren):
    self.symbol = symbol
    self.children = []
    for i in range(numOfChildren):
      self.children.append(None)
  
  def getSymbol(self):
    return self.symbol
  
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
    elif p2 is None or p2.getSymbol() is None:
      return False
    # if p1 is a constant wildcard (e.g. C, C1, C2, ...), then only true if
    # p2 is either a constant wildcard or constant value (e.g. -1, 1, 2, 3, ...)
    elif p1.nodeType() is NodeType.ConstWildcard and \
        (p2.nodeType() is NodeType.ConstWildcard or p2.nodeType() is NodeType.ConstVal):
      return True
    # true if p1 and p2 are (the same) constant values
    elif p1.nodeType() is NodeType.ConstVal and p2.nodeType() is NodeType.ConstVal and \
          p1.getSymbol() == p2.getSymbol():
      return True
    # if both are operations and their symbols match, recurs on their children.
    # if all children of p1 subsume children of p2, return true
    elif p1.nodeType() is NodeType.Operation and p2.nodeType() is NodeType.Operation and \
          p1.getSymbol() == p2.getSymbol():
          p1OperandNum = p1.numOfChildren()
          p2OperandNum = p2.numOfChildren()
          assert(p1OperandNum == p2OperandNum), "Operation with multiple possible arities is not possible"
          for i in range(1, p1OperandNum + 1):
            if TreeNode.subsumes(p1.childAt(i), p2.childAt(i)) is False:
              return False
          return True
    # catch all, return false
    else:
      return False
  
  def equals(self, p):
    return (self.subsumes(p) and p.subsumes(self))
  
  def __eq__(self, other):
    return self.equals(other)

  def __ne__(self, other):
    return not self.equals(other)

  # There exists a pattern p in P where (self == p)
  def equalsExists(self, P):
    for p in P:
      if self == p:
        return True
    return False
  
  # check if self is comparable with p
  def isNotComparable(self, p):
    return not (self.subsumes(p) or p.subsumes(self))
  
  # self subsumes p if p is an instance of self
  def subsumes(self, p):
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
    print(str(prefix) + infix + str(self.getSymbol()))
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
          expression.getOpName() == 'select':
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


class peepholeoptimization(object):
  def __init__(self, rule, name, pre, source, target, target_skip):
    self.rule = rule
    self.name = name
    self.pre = pre
    self.source = source
    self.target = target
    self.target_skip = target_skip