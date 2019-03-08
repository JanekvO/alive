from treepatternmatching import *
from value import Type
from common import *
from pdb import set_trace

class BUTypeFactory:
  @staticmethod
  def BUType(exprType):
    if isinstance(exprType, UnknownType):
      ty = BUUnknownType()
    elif isinstance(exprType, IntType):
      if exprType.defined:
        ty = BUIntType(size=exprType.size)
      else:
        ty = BUIntType()
    elif isinstance(exprType, PtrType):
      if exprType is not None:
        auxTy = BUTypeFactory.BUType(exprType.type)
      else:
        auxTy = None
      ty = BUPtrType(type=auxTy)
    elif isinstance(exprType, ArrayType):
      ty = BUArrayType()
    else:
      assert(False)
    return ty

# Need to use different types since the types as defined in value.py contain
# z3 constains for SMT solving, and z3 uses ctypes which cannot be pickled.
# An alternative approach is to augment the python bindings for z3 to support
# pickling, but using a isolated new type system will suffice for now.
class BUUnknownType(Type):
  def __init__(self, d = 0):
    self.types = {
      self.Int: BUIntType(),
      self.Ptr: BUPtrType(depth = d),
      self.Array: BUArrayType(depth = d)
    }
    self.myType = self.Unknown

  def __repr__(self):
    ret = 'Unknown('
    for tref,ty in self.types.items():
      ret = ret + repr(ty) + ','
    ret = ret + ')'
    return ret

  def ensureIntPtrOrVector(self):
    del self.types[self.Array]
    return self

  def ensureFirstClass(self):
    return self.ensureIntPtrOrVector()

class BUNameType(UnknownType):
  def __init__(self, name):
    UnknownType.__init__(self)
    self.type = UnknownType
    self.name = name

  def __repr__(self):
    return self.name + str(self.types)

class BUIntType(Type):
  def __init__(self, size = None):
    if size == None:
      self.defined = False
      return
    self.size = size
    self.defined = True
    assert(isinstance(self.size, int))

  def __repr__(self):
    if self.defined:
      return 'int(' + self.size + ')'
    else:
      return 'int(?)'

class BUPtrType(Type):
  def __init__(self, type = None, depth = 0):
    if type is None:
      if depth >= 0:
        type = BUIntType()
      else:
        type = BUUnknownType(depth + 1)
    self.type = type
    assert(isinstance(self.type, Type))

  def __repr__(self):
    return 'ptr(' + repr(self.type) + ')'

class BUArrayType(Type):
  id = 0
  def __init__(self, elems = None, type = None, depth = 0):
    if elems == None:
      assert type == None
      if depth >= 0:
        type = BUIntType()
      else:
        type = BUUnknownType(depth + 1)
      elems = BUInput('#' + str(self.uniqueId()), 0)
      elems.type = IntType(4)
    # TODO:
    # self.elems = TypeFixedValue(elems, 1, 7)
    # self.type = type
    # assert(self.type, Type)

  def __repr__(self):
    return 'ArrayType'

  @classmethod
  def uniqueId(cls):
    ret = cls.id
    cls.id = cls.id + 1
    return ret

class BUExprTree(ExpressionTree):
  def __init__(self, symbol, numChildren):
    self.name = ''
    self.type = Type.Unknown
    self.coordinate = ()
    self.symbol = symbol
    self.children = []
    self.flags = []
    self.auxiliaryOp = None
    self.relatedRuleId = None
    for i in xrange(numChildren):
      self.children.append(self.createWC())

  def __hash__(self):
    return hash(repr(self))

  ##############################################################################
  # Note that this rule is highly dependent on the input order of peephole
  # optimizations. If the order differs, bad things happen. Currently there is
  # no support for pickling the original tree expressions so this is the next
  # best thing in regards to relating the expression trees with original
  # expressions.
  # TL;DR:  ensure the order of peephole opt in phs is the same as
  #         rule (definitely when loading match sets from a file).
  ##############################################################################
  def setRelatedRule(self, rule):
    self.relatedRuleId = rule

  def getSymbol(self):
    s = self.symbol
    if self.symbol == 'icmp':
      s = s + Icmp.opnames[self.auxiliaryOp]
    elif self.symbol in BinOp.opids:
      for f in self.flags:
        s = s + f
    return s
  
  # Still not a fan of deriving these using the symbol string...
  # However, symbol string is basically the only information provided from
  # which we can derive the node type
  def nodeType(self):
    if self.symbol[0] == 'C':
      return NodeType.ConstWildcard
    elif self.symbol[0] == '%':
      return NodeType.Wildcard
    elif self.numOfChildren() > 0:
      if isinstance(self, BUCnstBinaryOp) or \
          isinstance(self, BUCnstFunction) or \
          isinstance(self, BUCnstUnaryOp):
        return NodeType.ConstOperation
      else:
        return NodeType.Operation
    elif RepresentsInt(self.symbol) or \
      isinstance(self, BUConstantVal) or \
      isinstance(self, BUUndefVal):
      return NodeType.ConstVal
    else:
      assert(False), 'tree should have a nodeType'

  def isBool(self):
    return False

  def get_APInt_or_u64(self, cgm):
    assert(False)

  def get_APInt(self, cgm):
    nt = self.nodeType()
    if nt == NodeType.ConstVal or nt == NodeType.ConstOperation:
      return CFunctionCall('APInt',
        cgm.get_llvm_type(self).arr('getScalarSizeInBits', []),
        self.get_APInt_or_u64(cgm))

  def get_Value(self, cgm):
    nt = self.nodeType()
    if nt == NodeType.ConstVal or nt == NodeType.ConstOperation:
      return CFunctionCall('ConstantInt::get',
        cgm.get_llvm_type(self),
        self.get_APInt_or_u64(cgm))
    assert(False)

  @staticmethod
  def createWithExpr(expr, coordinate):
    if isinstance(expr, Input):
      tree = BUInput(expr.getName(), 0)
      tree.name = tree.symbol
      tree.type = BUTypeFactory.BUType(expr.type)
      tree.coordinate = tuple(coordinate)
      return tree
    elif isinstance(expr, ConstantVal):
      tree = BUConstantVal(expr.getName(), 0)
      tree.name = tree.symbol
      tree.val = expr.val
      tree.type = BUTypeFactory.BUType(expr.type)
      tree.coordinate = tuple(coordinate)
      return tree
    elif isinstance(expr, UndefVal):
      tree = BUUndefVal(expr.getName(), 0)
      tree.name = tree.symbol
      tree.type = BUTypeFactory.BUType(expr.type)
      tree.coordinate = tuple(coordinate)
      return tree
    elif isinstance(expr, CnstUnaryOp):
      tree = BUCnstUnaryOp(CnstUnaryOp.opnames[expr.op], 0)
    elif isinstance(expr, CnstBinaryOp):
      tree = BUCnstBinaryOp(CnstBinaryOp.opnames[expr.op], 0)
    elif isinstance(expr, CnstFunction):
      tree = BUCnstFunction(CnstFunction.opnames[expr.op], 0)
      tree.type = BUTypeFactory.BUType(expr.type)
      tree.children = []
      tree.coordinate = tuple(coordinate)
      chNum = 1
      for arg in expr.args:
        tree.children.append(BUExprTree.createWithExpr(arg, coordinate + [chNum]))
        chNum += 1
      return tree
    elif isinstance(expr, CopyOperand):
      tree = BUCopyOperand(expr.getName(), 0)
    elif isinstance(expr, BinOp):
      tree = BUBinOp(expr.getOpName(), 0)
      tree.flags = expr.flags
    elif isinstance(expr, ConversionOp):
      tree = BUConversionOp(expr.getOpName(), 0)
      tree.stype = BUTypeFactory.BUType(expr.stype)
    elif isinstance(expr, Icmp):
      tree = BUIcmp(expr.getOpName(), 0)
      tree.auxiliaryOp = expr.op
      tree.stype = BUTypeFactory.BUType(expr.stype)
    elif isinstance(expr, Instr) and expr.getOpName() == 'select':
      tree = BUSelect(expr.getOpName(), 0)
    tree.name = expr.getName()
    tree.type = BUTypeFactory.BUType(expr.type)
    children = ExpressionTree.retrieveOperands(expr)
    tree.children = []
    tree.coordinate = tuple(coordinate)
    chNum = 1
    for c in children:
      tree.children.append(BUExprTree.createWithExpr(c, coordinate + [chNum]))
      chNum += 1
    return tree

  @staticmethod
  def createWC():
    return BUExprTree('%', 0)

  @staticmethod
  def createConstWC():
    return BUExprTree('C', 0)
  
  def findSimilarTree(self, trees):
    for t in trees:
      if t == self:
        return t
    return None
  
  # FIXME:  we're basically re-inventing the wheel with these set 
  #         operations. I.e., implement python set support
  #         for tree class(es)
  
  @staticmethod
  def union(*args):
    # Input is multiple iterables containing trees
    unionized = list()
    for it in args:
      for element in it:
        if not element.equalsExists(unionized):
          unionized.append(element)
    return unionized
  
  @staticmethod
  def intersect(*args):
    # Input is multiple iterables containing trees
    intersection = list(args[0])
    toRemove = list()
    for it in args:
      for element in intersection:
        if not element.equalsExists(it):
          toRemove.append(element)
    for t in toRemove:
      if t in intersection:
        intersection.remove(t)
    return intersection
  
  @staticmethod
  def difference(s1, s2):
    newS1 = list(s1)
    for t1 in newS1:
      if t1.equalsExists(s2):
        newS1.remove(t1)
        continue
    return newS1

class BUInput(BUExprTree):
  def register_types(self, cgm):
    if self.nodeType() == NodeType.ConstWildcard:
      min = BUIntType()
    else:
      min = BUUnknownType()

    cgm.register_type(self, self.type, min)

  def get_APInt_or_u64(self, cgm):
    return self.get_APInt(cgm)

  def get_APInt(self, cgm):
    assert(self.name[0] == 'C')
    return cgm.get_cexp(self).arr('getValue', [])

class BUConstantVal(BUExprTree):
  def register_types(self, cgm):
    if isinstance(self.type, BUPtrType):
      min = BUPtrType()
    else:
      min = BUIntType()

    cgm.register_type(self, self.type, min)

  def get_APInt_or_u64(self, cgm):
    return CVariable(str(self.val))

  def isBool(self):
    return self.getSymbol() in ['true', 'false']

class BUUndefVal(BUExprTree):
  def register_types(self, cgm):
    cgm.register_type(self, self.type, BUUnknownType())

  def get_Value(self, cgm):
    return CFunctionCall('UndefValue::get', cgm.get_llvm_type(self))

class BUCnstUnaryOp(BUExprTree):
  def register_types(self, cgm):
    self.childAt(1).register_types(cgm)
    cgm.register_type(self, self.type, BUIntType())
    cgm.unify(self, self.childAt(1))

  def get_APInt_or_u64(self, cgm):
    return CUnaryExpr(self.symbol, self.childAt(1).get_APInt_or_u64(cgm))

  def get_APInt(self, cgm):
    return CUnaryExpr(self.symbol, self.childAt(1).get_APInt(cgm))

class BUCnstBinaryOp(BUExprTree):
  def register_types(self, cgm):
    self.childAt(1).register_types(cgm)
    self.childAt(2).register_types(cgm)
    cgm.register_type(self, self.type, BUIntType())
    cgm.unify(self, self.childAt(1), self.childAt(2))

  def get_APInt_or_u64(self, cgm):
    return self.get_APInt(cgm)

  _cfun = {
      '&':  lambda a,b: CBinExpr('&', a, b),
      '|':   lambda a,b: CBinExpr('|', a, b),
      '^':  lambda a,b: CBinExpr('^', a, b),
      '+':  lambda a,b: CBinExpr('+', a, b),
      '-':  lambda a,b: CBinExpr('-', a, b),
      '*':  lambda a,b: CBinExpr('*', a, b),
      '/':  lambda a,b: a.dot('sdiv', [b]),
      '/u': lambda a,b: a.dot('udiv', [b]),
      '%':  lambda a,b: a.dot('srem', [b]),
      '%u': lambda a,b: a.dot('urem', [b]),
      '>>': lambda a,b: a.dot('ashr', [b]),
      'u>>': lambda a,b: a.dot('lshr', [b]),
      '<<':  lambda a,b: CBinExpr('<<', a,  b),
    }

  def get_APInt(self, cgm):
    op = self._cfun[self.symbol]
    opand1 = self.childAt(1).get_APInt(cgm)
    if self.symbol in ['+', '-', '>>', 'u>>', '<<']:
      opand2 = self.childAt(2).get_APInt_or_u64(cgm)
    else:
      opand2 = self.childAt(2).get_APInt(cgm)
    return op(opand1, opand2)

class BUCnstFunction(BUExprTree):
  def register_types(self, cgm):
    for i in xrange(1, self.numOfChildren() + 1):
      self.childAt(i).register_types(cgm)
    cgm.register_type(self, self.type, BUIntType())

    if self.symbol in ['abs', 'computeKnownOneBits', 'computeKnownZeroBits']:
      cgm.unify(self, self.childAt(1))
    elif self.symbol in ['lshr', 'max', 'umax']:
      cgm.unify(self, self.childAt(1), self.childAt(2))

  def _get_cexp(self, cgm):
    if CnstFunction.opids[self.symbol] == CnstFunction.abs:
      return False, self.childAt(1).get_APInt(cgm).dot('abs', [])

    if CnstFunction.opids[self.symbol] == CnstFunction.sbits:
      return True, CFunctionCall('ComputeNumSignBits', cgm.get_cexp(self.childAt(1)))

    if CnstFunction.opids[self.symbol] == CnstFunction.obits:
      return False, CFunctionCall('computeKnownOneBits',
        cgm.get_cexp(self.childAt(1)), CVariable('I'))

    if CnstFunction.opids[self.symbol] == CnstFunction.zbits:
      return False, CFunctionCall('computeKnownZeroBits',
        cgm.get_cexp(self.childAt(1)), CVariable('I'))

    if CnstFunction.opids[self.symbol] == CnstFunction.ctlz:
      return True, self.childAt(1).get_APInt(cgm).dot('countLeadingZeros', [])

    if CnstFunction.opids[self.symbol] == CnstFunction.cttz:
      return True, self.childAt(1).get_APInt(cgm).dot('countTrailingZeros', [])

    if CnstFunction.opids[self.symbol] == CnstFunction.log2:
      return True, self.childAt(1).get_APInt(cgm).dot('logBase2', [])

    if CnstFunction.opids[self.symbol] == CnstFunction.lshr:
      return False, self.childAt(1).get_APInt(cgm).dot('lshr',
        [self.childAt(2).get_APInt_or_u64(cgm)])

    if CnstFunction.opids[self.symbol] == CnstFunction.max:
      return False, CFunctionCall('APIntOps::smax',
        self.childAt(1).get_APInt(cgm), self.childAt(2).get_APInt(cgm))

    if CnstFunction.opids[self.symbol] == CnstFunction.sext:
      return False, self.childAt(1).get_APInt(cgm).dot('sext',
        [cgm.get_llvm_type(self).arr('getScalarSizeInBits', [])])

    if CnstFunction.opids[self.symbol] == CnstFunction.trunc:
      return False, self.childAt(1).get_APInt(cgm).dot('trunc',
        [cgm.get_llvm_type(self).arr('getScalarSizeInBits', [])])

    if CnstFunction.opids[self.symbol] == CnstFunction.umax:
      return False, CFunctionCall('APIntOps::umax', 
        self.childAt(1).get_APInt(cgm), self.childAt(2).get_APInt(cgm))

    if CnstFunction.opids[self.symbol] == CnstFunction.width:
      return True, cgm.get_llvm_type(self.childAt(1)).arr('getScalarSizeInBits', [])

    if CnstFunction.opids[self.symbol] == CnstFunction.zext:
      return False, self.childAt(1).get_APInt(cgm).dot('zext', 
        [cgm.get_llvm_type(self).arr('getScalarSizeInBits',[])])

    assert(False)

  def get_APInt(self, cgm):
    wrap, cexp = self._get_cexp(cgm)
    if wrap:
      return CFunctionCall('APInt', \
        cgm.get_llvm_type(self).arr('getScalarSizeInBits', []), cexp)
    return cexp

  def get_APInt_or_u64(self, cgm):
    return self._get_cexp(cgm)[1]

class BUCopyOperand(BUExprTree):
  def targetVisit(self, path, cgm, use_builder=False):
    instr = cgm.get_cexp(self.childAt(1))

    if use_builder:
      instr = CVariable('Builder').dot('Insert', [instr])

    if self.nodeType() == NodeType.Operation:
      ctype = cgm.PtrInstruction
    else:
      ctype = cgm.PtrValue

    # FIXME: Fix the following return for bottom-up
    return [CDefinition.init(ctype, cgm.get_cexp(self), instr)]

  def register_types(self, cgm):
    cgm.register_type(self, self.type, BUUnknownType())
    cgm.unify(self, self.childAt(1))

class BUBinOp(BUExprTree):
  def initialVisit(self, path, eg):
    path_1 = copy.deepcopy(path).append(1)
    path_2 = copy.deepcopy(path).append(2)
    eg.processSubtree(path_1)
    eg.processSubtree(path_2)

  _LLVM_BinOp_Name = {
    'add' : 'Add',
    'sub':  'Sub',
    'mul':  'Mul',
    'udiv': 'UDiv',
    'sdiv': 'SDiv',
    'urem': 'URem',
    'srem': 'SRem',
    'shl':  'Shl',
    'ashr': 'AShr',
    'lshr': 'LShr',
    'and':  'And',
    'or':   'Or',
    'xor':  'Xor',
  }

  def targetVisit(self, path, cgm, use_builder=False):
    opand1 = self.childAt(1)
    opand2 = self.childAt(2)
    cons = CFunctionCall('BinaryOperator::Create' + self._LLVM_BinOp_Name[self.symbol],
      cgm.get_cexp(opand1), cgm.get_cexp(opand2))

    if use_builder:
      cons = CVariable('Builder').dot('Insert', [cons])

    gen = [CDefinition.init(CPtrType(CTypeName('BinaryOperator')), cgm.get_cexp(self), cons)]

    for f in self.flags:
      setter = {'nsw': 'setHasNoSignedWrap', 'nuw': 'setHasNoUnsignedWrap', 'exact': 'setIsExact'}[f]
      gen.append(cgm.get_cexp(self).arr(setter, [CVariable('true')]))

    return gen

  def register_types(self, cgm):
    cgm.register_type(self, self.type, BUIntType())
    cgm.unify(self, self.childAt(1), self.childAt(2))

class BUConversionOp(BUExprTree):
  def __init__(self, symbol, numChildren):
    super(BUConversionOp, self).__init__(symbol, numChildren)
    self.stype = Type.Unknown

  def initialVisit(self, path, eg):
    path_1 = copy.deepcopy(path).append(1)
    eg.processSubtree(path_1)

  _constr = {
    'trunc' : 'TruncInst',
    'zext' : 'ZExtInst',
    'sext' : 'SExtInst',
    'ptrtoint' : 'PtrToIntInst',
    'inttoptr' : 'IntToPtrInst',
    'bitcast' : 'BitCastInst',
  }

  def targetVisit(self, path, cgm, use_builder=False):
    if self.symbol == 'ZExtOrTrunc':
      assert use_builder  #TODO: handle ZExtOrTrunk in root position
      instr = CVariable('Builder').dot('CreateZExtOrTrunc',
        [cgm.get_cexp(self.childAt(1)), cgm.get_llvm_type(self)])
      return [CDefinition.init(
        cgm.PtrValue,
        cgm.get_cexp(self),
        instr)]

    else:
      instr = CFunctionCall('new ' + self._constr[self.symbol],
        cgm.get_cexp(self.childAt(1)), cgm.get_llvm_type(self))

      if use_builder:
        instr = CVariable('Builder').dot('Insert', [instr])

    return [CDefinition.init(
      cgm.PtrInstruction,
      cgm.get_cexp(self),
      instr)]

  @staticmethod
  def enforceIntSrc(sym):
    return sym in ['trunc', 'zext', 'sext', 'ZExtOrTrunc', 'inttoptr']

  @staticmethod
  def enforcePtrSrc(sym):
    return sym in ['ptr2int']

  @staticmethod
  def enforceIntTgt(sym):
    return sym in ['trunc', 'zext', 'sext', 'ZExtOrTrunc', 'ptrtoint']

  @staticmethod
  def enforcePtrTgt(sym):
    return sym == 'inttoptr'

  def register_types(self, cgm):
    if self.enforceIntSrc(self.symbol):
      cgm.register_type(self.childAt(1), self.stype, BUIntType())
    elif self.enforcePtrSrc(self.symbol):
      cgm.register_type(self.childAt(1), self.stype, BUPtrType())
    else:
      cgm.register_type(self.childAt(1), self.stype, BUUnknownType())

    if self.enforceIntTgt(self.symbol):
      cgm.register_type(self, self.type, BUIntType())
    elif self.enforcePtrTgt(self.symbol):
      cgm.register_type(self, self.type, BUPtrType())
    else:
      cgm.register_type(self, self.type, BUUnknownType())

class BUIcmp(BUExprTree):
  def __init__(self, symbol, numChildren):
    super(BUIcmp, self).__init__(symbol, numChildren)
    self.stype = Type.Unknown

  def initialVisit(self, path, eg):
    path_1 = copy.deepcopy(path).append(1)
    path_2 = copy.deepcopy(path).append(2)
    eg.processSubtree(path_1)
    eg.processSubtree(path_2)
    # TODO: icmp with variable predicate

  def targetVisit(self, path, cgm, use_builder=False):
    # determine the predicate
    if self.auxiliaryOp == Icmp.Var:
      key = self.symbol if self.symbol else 'Pred ' + self.name
      opname = cgm.get_key_name(key)
      assert cgm.bound(opname)
      # TODO: confirm type

    else:
      opname = Icmp.op_enum[self.auxiliaryOp]

    instr = CFunctionCall('new ICmpInst', CVariable(opname),
      cgm.get_cexp(self.childAt(1)), 
      cgm.get_cexp(self.childAt(2)))

    if use_builder:
      instr = CVariable('Builder').dot('Insert', [instr])

    return [
      CDefinition.init(cgm.PtrInstruction, cgm.get_cexp(self), instr)]

  def register_types(self, cgm):
    cgm.register_type(self, self.type, BUIntType(1))
    cgm.register_type(self.childAt(1), self.stype, BUUnknownType().ensureIntPtrOrVector())
    cgm.unify(self.childAt(1), self.childAt(2))

class BUSelect(BUExprTree):
  def initialVisit(self, path, eg):
    path_c = copy.deepcopy(path).append(1)
    path_1 = copy.deepcopy(path).append(2)
    path_2 = copy.deepcopy(path).append(3)
    eg.processSubtree(path_c)
    eg.processSubtree(path_1)
    eg.processSubtree(path_2)

  def targetVisit(self, path, cgm, use_builder=False):
    instr = CFunctionCall('SelectInst::Create',
      cgm.get_cexp(self.childAt(1)),
      cgm.get_cexp(self.childAt(2)),
      cgm.get_cexp(self.childAt(3)))

    if use_builder:
      instr = CVariable('Builder').dot('Insert', [instr])

    return [CDefinition.init(cgm.PtrInstruction, cgm.get_cexp(self), instr)]

  def register_types(self, cgm):
    cgm.register_type(self, self.type, BUUnknownType().ensureFirstClass())
    cgm.register_type(self.childAt(1), self.childAt(1).type, BUIntType(1))
    cgm.unify(self, self.childAt(2), self.childAt(3))
