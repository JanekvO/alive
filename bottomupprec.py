
from codegen import *
from bottomuptree import *
from precondition import *
import copy

class BUBoolPred:
  def __init__(self):
    self.children = []

  @staticmethod
  def predToBUPred(pred):
    if isinstance(pred, TruePred):
      return BUTruePred()
    elif isinstance(pred, PredNot):
      v = BUBoolPred.predToBUPred(pred.v)
      return BUOpPred('not', [v])
    elif isinstance(pred, PredAnd):
      return BUOpPred('and', \
        [BUBoolPred.predToBUPred(arg) for arg in pred.args])
    elif isinstance(pred, PredOr):
      return BUOpPred('or', \
        [BUBoolPred.predToBUPred(arg) for arg in pred.args])
    elif isinstance(pred, BinaryBoolPred):
      v1 = BUExprTree.createWithExpr(pred.v1)
      v2 = BUExprTree.createWithExpr(pred.v2)
      return BUCompOpPred(BinaryBoolPred.opnames[pred.op], [v1, v2])
    elif isinstance(pred, LLVMBoolPred):
      return BULLVMPred(pred.op,\
        [BUExprTree.createWithExpr(arg) for arg in pred.args])
    else:
      assert(False)

class BUTruePred(BUBoolPred):
  def __repr__(self):
    return 'true'

  def register_types(self, cgm):
    pass

  def visitPrecondition(self, cgm):
    return CVariable('true')

class BUOpPred(BUBoolPred):
  _pred = {
    'not' : '!',
    'and' : '&&',
    'or' : '||',
  }

  def __init__(self, op, children):
    self.op = op
    self.children = copy.deepcopy(children)

  def __repr__(self):
    if len(self.children) == 1:
      return self.op + repr(self.children[0])
    elif len(self.children) == 2:
      return repr(self.children[0]) + self.op + repr(self.children[1])
    assert(False)

  def register_types(self, cgm):
    for ch in self.children:
      ch.register_types(cgm)

  def visitPrecondition(self, cgm):
    return CBinExpr.reduce(self._pred[self.op], (ch.visitPrecondition(cgm) \
      for ch in self.children))

class BUCompOpPred(BUBoolPred):
  opnames = ['==', '!=', '<', '<=', '>', '>=', 'u<', 'u<=', 'u>', 'u>=']
  def __init__(self, op, children):
    assert(op in self.opnames and len(children) == 2)
    self.op = op
    self.children = copy.deepcopy(children)

  def __repr__(self):
    return repr(self.children[0]) + self.op + repr(self.children[1])

  def register_types(self, cgm):
    self.children[0].register_types(cgm)
    self.children[1].register_types(cgm)
    cgm.unify(self.children[0], self.children[1])

  gens = {
    '==':  lambda a,b: CBinExpr('==', a, b),
    '!=':  lambda a,b: CBinExpr('!=', a, b),
    '<': lambda a,b: a.dot('slt', [b]),
    '<=': lambda a,b: a.dot('sle', [b]),
    '>': lambda a,b: a.dot('sgt', [b]),
    '>=': lambda a,b: a.dot('sge', [b]),
    'u<': lambda a,b: a.dot('ult', [b]),
    'u<=': lambda a,b: a.dot('ule', [b]),
    'u>': lambda a,b: a.dot('ugt', [b]),
    'u>=': lambda a,b: a.dot('uge', [b]),
  }

  def visitPrecondition(self, cgm):
    def untyped(op):
      return isinstance(op, BUConstantVal) or \
        (isinstance(op, BUCnstFunction) and op.symbol in ['countLeadingZeros', 'countTrailingZeros', 'log2', 'width'])

    if untyped(self.children[0]) and untyped(self.children[1]):
      _conv = {
        'u<' : '<',
        'u<=' : '<=', 
        'u>' : '>',
        'u>=' : '>='
      }

      if self.op in _conv:
        cmp = _conv[self.op]
      else:
        cmp = self.op

      return CBinExpr(cmp, \
        self.children[0].get_APInt_or_u64(cgm), \
        self.children[1].get_APInt_or_u64(cgm))

    return self.gens[self.op]( \
      self.children[0].get_APInt(cgm), \
      self.children[1].get_APInt_or_u64(cgm))

class BULLVMPred(BUBoolPred):
  def __init__(self, op, args):
    self.op = op
    self.children = list(args)

  def register_types(self, cgm):
    for ch in self.children:
      ch.register_types(cgm)

    if self.op in {LLVMBoolPred.maskZero, LLVMBoolPred.NSWAdd}:
      cgm.unify(self.children[0], self.children[1])

  def visitPrecondition(self, cgm):
    if self.op == LLVMBoolPred.eqptrs:
      raise AliveError('eqptrs not currently supported')

    if self.op == LLVMBoolPred.isPower2:
      a = self.children[0]
      nt = a.nodeType()
      #if isinstance(a, Constant):
      if nt == NodeType.ConstVal or nt == NodeType.ConstOperation:
        return a.get_APInt(cgm).dot('isPowerOf2', [])

      return CFunctionCall('isKnownToBeAPowerOfTwo', cgm.get_cexp(a))

    if self.op == LLVMBoolPred.isPower2OrZ:
      return CFunctionCall('isKnownToBeAPowerOfTwo',
        cgm.get_cexp(self.children[0]), CVariable('true'))

    if self.op == LLVMBoolPred.NUWAdd:
      return CBinExpr('==',
        CFunctionCall('computeOverflowForUnsignedAdd',
          cgm.get_cexp(self.children[0]),
          cgm.get_cexp(self.children[1]),
          CVariable('I')),
        CVariable('OverflowResult::NeverOverflows'))

    if self.op == LLVMBoolPred.NUWMul:
      return CBinExpr('==',
        CFunctionCall('computeOverflowForUnsignedMul',
          cgm.get_cexp(self.children[0]),
          cgm.get_cexp(self.children[1]),
          CVariable('I')),
        CVariable('OverflowResult::NeverOverflows'))

    if self.op == LLVMBoolPred.NSWMul:
      return CFunctionCall(LLVMBoolPred.opnames[self.op], 
        cgm.get_cexp(self.children[0]),
        cgm.get_cexp(self.children[1]),
        CVariable('*I'))

    opname = LLVMBoolPred.opnames[self.op]
    args = []
    for i in range(LLVMBoolPred.num_args[self.op]):
      if LLVMBoolPred.arg_types[self.op][i] == 'const':
        args.append(self.children[i].get_APInt(cgm))
      else:
        args.append(cgm.get_cexp(self.children[i]))

    if self.op == LLVMBoolPred.isShiftedMask:
      return args[0].dot(LLVMBoolPred.opnames[self.op], [])

    if self.op == LLVMBoolPred.isSignBit:
      return args[0].dot('isSignMask', [])

    if self.op == LLVMBoolPred.OneUse:
      return args[0].arr('hasOneUse', [])

    if self.op in {LLVMBoolPred.NSWAdd, LLVMBoolPred.NSWSub,
        LLVMBoolPred.NUWSub}:
      return CFunctionCall(LLVMBoolPred.opnames[self.op], args[0], args[1], CVariable('*I'))
      # TODO: obtain root from cgm?

    return CFunctionCall(LLVMBoolPred.opnames[self.op], *args)
