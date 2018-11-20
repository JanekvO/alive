from treepatternmatching import *
from itertools import product, izip, count
from gen import get_root
import pickle

from pdb import set_trace

DO_STATS = True
SIMPLIFY = True
LIMITER = False

class BUpeepholeopt(peepholeoptimization):
  def __init__(self, rule, name, pre, source, target, target_skip):
    super(BUpeepholeopt, self).__init__(rule, name, pre, source, target, target_skip)
    self.src_tree = BUExprTree.createWithExpr(get_root(source))
    self.tgt_tree = get_root(target)

class BUExprTree(ExpressionTree):
  def __init__(self, symbol, numChildren):
    self.symbol = symbol
    self.children = []
    self.flags = []
    self.auxiliaryOp = None
    for i in xrange(numChildren):
      self.children.append(self.createWC())
    
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
      return NodeType.Operation
    elif RepresentsInt(self.symbol):
      return NodeType.ConstVal
    else:
      return None
  
  @staticmethod
  def createWithExpr(expr):
    tree = BUExprTree.createWC()
    tree.initializeUsingExpr(expr)
    return tree
  
  def initializeUsingExpr(self, expr):
    nt = ExpressionTree.retrieveExprType(expr)
    if nt == NodeType.ConstVal:
      self.symbol = str(expr.val)
    elif nt == NodeType.ConstWildcard or nt == NodeType.Wildcard:
      self.symbol = expr.getName()
    elif nt == NodeType.Operation:
      self.symbol = expr.getOpName()
      if isinstance(expr, Icmp):
        self.auxiliaryOp = expr.op
      elif isinstance(expr, BinOp):
        self.flags = expr.flags
      children = ExpressionTree.retrieveOperands(expr)
      self.children = []
      for c in children:
        self.children.append(BUExprTree.createWithExpr(c))

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

# Minimizes tables by taking an intermediate step in terms of table
# So instead of mapping y1 x y2 x ... x yn to a value we first take the mapping function f of each value which maps to a smaller table
# i.e. f(y1) x f(y2) x ... x f(yn) which maps to the smaller variant of the smaller table
class MinimizedTables(object):
  def __init__(self, mapping):
    self.mapping = mapping
    self.tableMap = dict()
    self.tables = dict()
    self.defaultInit = None
  
  def setDefault(self, matchset):
    self.defaultInit = self.getStateId(matchset)
  
  def initializeTable(self, currentElement, currentDepth, children):
    for ch in children[currentDepth]:
      newDepth = currentDepth + 1
      if newDepth == len(children):
        currentElement[ch] = self.defaultInit
      else:
        currentElement[ch] = dict()
        self.initializeTable(currentElement[ch], newDepth, children)

  def initializeTables(self, usedIndices):
    for sym,chIndices in usedIndices.items():
      self.tables[sym] = dict()
      indices = list()
      for ch,idcs in chIndices.items():
        indices.append(idcs)
      self.initializeTable(self.tables[sym], 0, indices)

  @staticmethod
  def dimensionCheckWithType(label, collection, ty):
    dimen = 0
    val = collection[label]
    while isinstance(val, ty):
      val = val[0]
      dimen = dimen + 1
    return dimen

  def dimension(self, label):
    return MinimizedTables.dimensionCheckWithType(label, self.tables, dict)

  def retrieveIntermediateMap(self, label, child, stateId):
    return self.tableMap[label][child][stateId]

  @staticmethod
  def stateId(mapping, matchSet):
    for stateId,ms in mapping.items():
      if TableBuilder.areCollectionEqual(ms, matchSet):
        return stateId
    return None

  def getStateId(self, matchSet):
    return MinimizedTables.stateId(self.mapping, matchSet)
  
  def getMatchSet(self, stateId):
    return self.mapping[stateId]

  def retrieveValue(self, label, *arg):
    val = self.tables[label]
    child = 1
    for ar in arg:
      mappedAr = self.retrieveIntermediateMap(label, child, ar)
      child = child + 1
      val = val[mappedAr]
    return val

  def assignValue(self, label, value, *arg):
    numArg = len(arg)
    if numArg == 0:
      self.tables[label] = value
      return
    
    if label not in self.tables:
      self.tables[label] = dict()

    val = self.tables[label]
    for i in xrange (0, numArg):
      if arg[i] not in val:
        val[arg[i]] = dict()

      if i == numArg - 1:
        val[arg[i]] = value
      else:
        val = val[arg[i]]

class TableBuilder(object):
  def __init__(self, peepholeopts):
    self.peepholeopts = peepholeopts
    self.patterns = list()
    for opt in self.peepholeopts:
      self.patterns.append(opt.src_tree)
    self.PF = self.generatePatternForest(self.patterns)
    self.iteration = list()
    self.representerSet = dict()
    self.childSets = dict()

  def createChildSets(self):
    for p in self.PF:
      s = p.getSymbol()
      if p.numOfChildren() > 0 and s not in self.childSets:
        self.childSets[s] = dict()
        for i in xrange(1, p.numOfChildren()+1):
          self.childSets[s][i] = list()

    for p in self.PF:
      numChildren = p.numOfChildren()
      s = p.getSymbol()
      if numChildren > 0:
        for i in xrange(1, p.numOfChildren() + 1):
          self.childSets[s][i] = BUExprTree.union(self.childSets[s][i], [p.childAt(i)])

  @staticmethod
  def areCollectionEqual(collectionA, collectionB):
    # checks if collection of trees are equal
    if len(collectionA) != len(collectionB):
      return False
    for a in collectionA:
      if not a.equalsExists(collectionB):
        return False
    return True

  @staticmethod
  def containsCollection(collecElement, collec):
    # check if list of trees exists in list of list of trees...
    if len(collec) == 0:
      return False
    for c in collec:
      if TableBuilder.areCollectionEqual(collecElement, c):
        return True
    return False

  @staticmethod
  def treeCollectionsEqual(treeCollecA, treeCollecB):
    # Check if collection A contains the same collection of trees as collection B
    if len(treeCollecA) != len(treeCollecB):
      return False
    for a in treeCollecA:
      if not TableBuilder.containsCollection(a, treeCollecB):
        return False
    return True

  @staticmethod
  def getLastIteration(iterationSet):
    return iterationSet[len(iterationSet)-1]

  def retrieveSymbols(self):
    F = dict()
    for p in self.PF:
      if p.numOfChildren() > 0 and p.getSymbol() not in F:
        F[p.getSymbol()] = p
    return F

  def initRepresenterSet(self):
    F = self.retrieveSymbols()
    for sym,tree in F.items():
      self.representerSet[sym] = dict()
      for i in xrange(1, tree.numOfChildren() + 1):
        self.representerSet[sym][i] = list()

  def updateRepresenterSet(self, iterationSet):
    F = self.retrieveSymbols()
    for sym,tree in F.items():
      for ch in xrange(1, tree.numOfChildren() + 1):
        represent = list()
        for it in iterationSet:
          intersec = BUExprTree.intersect(self.childSets[sym][ch], it)
          if not TableBuilder.containsCollection(intersec, represent):
            represent.append(intersec)
        self.representerSet[sym][ch].append(represent)

  def initIteration(self, hasWC, hasConstWC):
    ret = list()
    # Initial iteration, only contains symbols of arity 0 after this
    for p in self.PF:
      if p.numOfChildren() == 0:
        local = list()
        WC = BUExprTree.createWC()
        ConstWC = BUExprTree.createConstWC()
        if hasWC and p != WC and WC.subsumes(p):
          local.append(WC)
        if hasConstWC and p != ConstWC and ConstWC.subsumes(p):
          local.append(ConstWC)
        local.append(p)
        ret.append(local)
    # Create sets of patterns that can occur as a child of a particular function
    self.createChildSets()
    # Initialize representer sets where the intersection between child set and
    # iteration set is stored.
    self.initRepresenterSet()
    self.updateRepresenterSet(ret)
    return ret

  def tupleAlreadyCovered(self, tup, sym):
    lastIter = len(self.iteration) - 2
    if lastIter < 0:
      return False
    for i,s in self.representerSet[sym].items():
      currentSet = s[lastIter]
      if not TableBuilder.containsCollection(tup[i-1], currentSet):
        return False
    # every element in every tuple exists in the representer set of 2 iterations ago
    # i.e. we already got this scenario covered
    return True

  def iterate(self, hasWC):
    # create dictionary of labels
    lastiter = len(self.iteration) - 1
    ret = list(self.iteration[lastiter])
    F = self.retrieveSymbols()

    for sym,tree in F.items():
      MSP = list()
      representProduct = list()
      for ch,s in self.representerSet[sym].items():
        representProduct.append(TableBuilder.getLastIteration(s))
      # FIXME: what if a set is empty?
      R = product(*representProduct)
      for r in R:
        # if tuple is already done in one of the previous iterations, we should skip it
        if not self.tupleAlreadyCovered(r, sym):
          MSP.append(list(product(*r)))

      for m in MSP:
        withSym = list()
        if hasWC:
          withSym.append(BUExprTree.createWC())
        for tup in m:
          localTree = BUExprTree(sym, len(tup))
          for i in xrange(1, len(tup) + 1):
            localTree.addChild(tup[i-1], i)
          withSym.append(localTree)
        intersectResult = BUExprTree.intersect(self.PF, withSym)
        if not TableBuilder.containsCollection(intersectResult, ret):
          ret.append(intersectResult)
    self.updateRepresenterSet(ret)
    return ret

  def isLastIteration(self):
    F = self.retrieveSymbols()
    iterlen = len(self.iteration)
    for sym,tree in F.items():
      for childidx in xrange(1, len(self.representerSet[sym]) + 1):
        if not TableBuilder.treeCollectionsEqual(\
            self.representerSet[sym][childidx][iterlen-1],
            self.representerSet[sym][childidx][iterlen-2]):
          return False
    return True

  def generateMatchSet(self):
    wc = BUExprTree.createWC()
    cwc = BUExprTree.createConstWC()
    wildcardInPF = wc.equalsExists(self.PF)
    constWilcardInPF = cwc.equalsExists(self.PF)

    self.iteration.append(self.initIteration(wildcardInPF, constWilcardInPF))
    print('Initializing:{}'.format(self.iteration[0]))

    while True:
      self.iteration.append(self.iterate(wildcardInPF))
      iterlen = len(self.iteration)
      print('Generating:{}'.format(self.iteration[iterlen-1]))
      if self.isLastIteration():
        break

  @staticmethod
  def reduceMatchSet(matchset):
    reducedMS = list(matchset)
    toRemove = list()

    for i in xrange(0, len(reducedMS)):
      for j in xrange(0, len(reducedMS)):
        if reducedMS[i].subsumes(reducedMS[j]) and i != j:
          toRemove.append(reducedMS[i])
          break

    for rm in toRemove:
      reducedMS.remove(rm)

    return reducedMS

  @staticmethod
  def computeMatchingTuples(MS, mapping, usedIndices):
    ''' Computes list of stateId tuples that subsume match set`s (MS) children. Used to compute which table entries map to MS. '''
    wc = BUExprTree.createWC()
    childMapping = list()

    # initializing childMappings
    for tree in MS:
      if tree != wc:
        for i in xrange(1, tree.numOfChildren() + 1):
          childMapping.append(dict())
        break
    for tree in MS:
      if tree != wc:
        for child,indices in usedIndices.items():
          for idx in indices:
            childMapping[child-1][idx] = mapping[idx]

    # remove match sets from childMapping that can't possibly map to MS
    for tree in MS:
      if tree != wc:
        for i in xrange(1, tree.numOfChildren() + 1):
          child = tree.childAt(i)
          for stateId,matchset in childMapping[i-1].items():
            for matchtree in matchset:
              if not child.subsumes(matchtree) and not (TableBuilder.matchSetSubset({child}, matchset) and len(matchset) > 1):
                del childMapping[i-1][stateId]
                break
            # Can't possibly find a tuple of indices, therefore return the empty generator
            if len(childMapping[i-1]) == 0:
              return list()
    
    ret = product(*childMapping)
    return ret

  @staticmethod
  def retrieveRootedLabel(matchset):
    wc = BUExprTree.createWC()
    cwc = BUExprTree.createConstWC()
    for t in matchset:
      if t != wc and t != cwc:
        return t.getSymbol()
    return None

  @staticmethod
  def setSubsume(tree, matchset):
    # check if tree subsumes all patterns in matchset
    for msTree in matchset:
      if tree.isNotComparable(msTree) or not tree.subsumes(msTree):
        return False
    return True

  @staticmethod
  def containsTree(tree, collection):
    for c in collection:
      if tree == c:
        return True
    return False

  @staticmethod
  def matchSetSubset(MS1, MS2):
    # check if MS1 is a subset of MS2
    for t1 in MS1:
      if not TableBuilder.containsTree(t1, MS2):
        return False
    return True

  @staticmethod
  def mostSpecificMatchSet(MS1, MS2):
    ms1Diff2 = BUExprTree.difference(MS1, MS2)
    ms2Diff1 = BUExprTree.difference(MS2, MS1)

    # e.g. MS2 = {add(0,%)} and MS1 = {add(0,%), sub(%,%)}
    if len(ms1Diff2) > len(ms2Diff1) and len(ms2Diff1) == 0:
      return MS1
    # e.g. MS1 = {add(0,%)} and MS2 = {add(0,%), sub(%,%)}
    elif len(ms1Diff2) < len(ms2Diff1) and len(ms1Diff2) == 0:
      return MS2
    # e.g. MS1 = {sub(C,*)} and MS2 = {sub(*,*)}
    else:
      for t1 in ms1Diff2:
        if not TableBuilder.setSubsume(t1, ms2Diff1):
          return MS1
      return MS2
  
  @staticmethod
  def isComparable(MS1, MS2):
    for t1 in MS1:
      for t2 in MS2:
        if t1.isNotComparable(t2):
          return False
    return True

  def generateTables(self):
    # while there is a lot of overlap with matching set generation
    # I think it's best if table generation and matching set generation are seperated
    wc = BUExprTree.createWC()
    cwc = BUExprTree.createConstWC()
    wildcardInPF = wc.equalsExists(self.PF)

    finalIterIdx = len(self.iteration) - 1
    finalIter = list(self.iteration[finalIterIdx])

    stateMapping = dict()
    usedIndices = dict()

    # numbering matching sets to be used for states
    for i in xrange(0, len(finalIter)):
      stateMapping[i] = finalIter[i]

    tables = MinimizedTables(stateMapping)

    if wildcardInPF:
      tables.setDefault([wc])

    # Initialize
    F = self.retrieveSymbols()
    for sym,tree in F.items():
      tables.tableMap[sym] = dict()
      usedIndices[sym] = dict()
    for sym,tree in F.items():
      for ch in xrange(1, tree.numOfChildren() + 1):
        tables.tableMap[sym][ch] = list()
        usedIndices[sym][ch] = list()

    # Create table map
    for sym,tree in F.items():
      for ch in xrange(1, tree.numOfChildren() + 1):
        localMSMap = dict()
        for i,ms in stateMapping.items():
          # At this point we can safely assume we know the childsets
          intersect = BUExprTree.intersect(ms, self.childSets[sym][ch])
          nextStateId = i
          nextMS = intersect
          for li,lms in localMSMap.items():
            if TableBuilder.areCollectionEqual(lms, intersect):
              nextStateId = li
              nextMS = lms
              break
          tables.tableMap[sym][ch].append(nextStateId)
          localMSMap[i] = nextMS

    # Reduce the indices to only the used ones
    for sym,tree in F.items():
      for ch in xrange(1, tree.numOfChildren() + 1):
        for idx in tables.tableMap[sym][ch]:
          if idx not in usedIndices[sym][ch]:
            usedIndices[sym][ch].append(idx)
    
    # Initialize minimized tables in tables object
    tables.initializeTables(usedIndices)
    
    # Reduce the match sets in the mapping s.t. only the most specific remain
    reducedStateMapping = dict()
    for stateId,matchset in stateMapping.items():
      reducedStateMapping[stateId] = TableBuilder.reduceMatchSet(matchset)

    # Fill tables
    for stateId,matchset in reducedStateMapping.items():
      # Fill tables for symbols of arity=0
      for tree in matchset:
        if tree != wc and tree != cwc and tree.numOfChildren() == 0:
          tables.assignValue(tree.getSymbol(), stateId)

      rootLabel = self.retrieveRootedLabel(matchset)
      if rootLabel in usedIndices:
        allowedTuples = TableBuilder.computeMatchingTuples(matchset, reducedStateMapping, usedIndices[rootLabel])

        for tupl in allowedTuples:
          setAtTupl = tables.retrieveValue(rootLabel, *tupl)
          if setAtTupl is not None:
            msAtTupl = reducedStateMapping[setAtTupl]
            # FIXME: split mostSpecificMatchSet for different cases (i.e. subsumption and subset)
            mostSpecific = TableBuilder.mostSpecificMatchSet(msAtTupl, matchset)
            tables.assignValue(rootLabel, MinimizedTables.stateId(reducedStateMapping, mostSpecific), *tupl)

    return tables
  
  def generate(self, pickled = False):
    tbos = 'TableBuilderObject.obj'
    if not pickled:
      self.generateMatchSet()
      fileobj = open(tbos,'wb')
      pickle.dump(self.patterns, fileobj)
      pickle.dump(self.PF,fileobj)
      pickle.dump(self.iteration,fileobj)
      pickle.dump(self.representerSet,fileobj)
      pickle.dump(self.childSets,fileobj)
      fileobj.close()
    else:
      fileobj = open(tbos,'rb')
      self.patterns = pickle.load(fileobj)
      self.PF = pickle.load(fileobj)
      self.iteration = pickle.load(fileobj)
      self.representerSet = pickle.load(fileobj)
      self.childSets = pickle.load(fileobj)
      fileobj.close()

    tables = self.generateTables()
    return tables

  @staticmethod
  def generatePatternForest(patterns):
    PF = set()
    todo = set(patterns)

    while todo:
      p = todo.pop()
      if not p.equalsExists(PF):
        PF.add(p)
      for i in xrange(1, p.numOfChildren() + 1):
        todo.add(p.childAt(i))
    return PF
  
  @staticmethod
  def dumpiter(iteration):
    for st in iteration:
      print('set:'),
      for s in st:
        print(s.getSymbol()),
      print('')

def generate_tables(opts, out):
  root_opts = defaultdict(list)
  opts = list(izip(count(1), opts))

  # gather names of testcases
  if DO_STATS:
    for rule, opt in opts:
      name = opt[0]
      # TODO: abstract this
      src_root = get_root(opt[4]).getOpName()

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
    root_opts[get_root(opt[4]).getOpName()].append(opt)
    name, pre, src_bb, tgt_bb, src, tgt, src_used, tgt_used, tgt_skip = opt
    phs.append(BUpeepholeopt(rule, name, pre, src, tgt, tgt_skip))

  tb = TableBuilder(phs)
  tables = tb.generate(False)
  for i,ms in tables.mapping.items():
    print("{}:\t{}".format(i, ms))
  
  for f,t in tables.tableMap.items():
    print("mapping: {} : {}".format(f, t))
  
  for f,t in tables.tables.items():
    print('###########')
    print(f)
    print(t)
    print("dimension of {}: {}".format(f, tables.dimension(f)))
  set_trace()

