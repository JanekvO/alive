from treepatternmatching import *
from itertools import product

from pdb import set_trace

class TmpTree(TreeNode):
  def nodeType(self):
    if self.symbol == '%':
      return NodeType.Wildcard
    elif self.numOfChildren() == 0:
      return NodeType.ConstVal
    else:
      return NodeType.Operation

  def __repr__(self):
    strbuild = self.getSymbol()
    if self.numOfChildren() > 0:
      strbuild = strbuild + '('
      for i in range (1, self.numOfChildren() + 1):
        strbuild = strbuild + self.childAt(i).__repr__()
        if i != self.numOfChildren():
          strbuild = strbuild + ','
      strbuild = strbuild + ')'
    return strbuild

  @staticmethod
  def createWC():
    return TmpTree('%', 0)
  
  def findSimilarTree(self, trees):
    for t in trees:
      if t == self:
        return t
    return None
  
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

class MatchingSet(object):
  def __init__(self, state_id, patterns, accepting=None):
    self.id = state_id
    self.patterns = patterns
    self.accepting = accepting

class Tables(object):
  def __init__(self, mapping):
    self.mapping = mapping  # int -> matching set
    self.tables = dict()    # function symbol -> n-dimension table
  
  @staticmethod
  def initializeTable(dimension, size, initval=None):
    # initializes a table of dimension=dimension with 
    # each dimension having size=size
    if dimension == 0:
      return initval
    elif dimension > 0:
      tmp = list()
      for i in range(size):
        tmp.append(Tables.initializeTable(dimension-1, size, initval))
      return tmp
  
  def addTable(self, symbol, dimension, initval=None):
    if symbol not in self.tables:
      self.tables[symbol] = Tables.initializeTable(dimension, \
        len(self.mapping), initval)
  
  @staticmethod
  def stateId(mapping, matchSet):
    for stateId,ms in mapping.items():
      if TableBuilder.areCollectionEqual(ms, matchSet):
        return stateId
    return None

  def getStateId(self, matchSet):
    return Tables.stateId(self.mapping, matchSet)
  
  def getMatchSet(self, stateId):
    return self.mapping[stateId]
  
  def assignValue(self, label, value, *arg):
    numArg = len(arg)
    if numArg == 0:
      self.tables[label] = value
      return

    val = self.tables[label]
    for i in range (0, numArg):
      if i == numArg - 1:
        val[arg[i]] = value
      else:
        val = val[arg[i]]
  
  def retrieveValue(self, label, *arg):
    val = self.tables[label]
    for ar in arg:
      val = val[ar]
    return val

class TableBuilder(object):
  # TODO: change interface for peephole optimizations
  def __init__(self, trees):
    self.patterns = trees
    self.PF = self.generatePatternForest(self.patterns)
    self.iteration = list()
  
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

  def initIteration(self, hasWC):
    ret = list()
    if hasWC:
      fs = list()
      fs.append(TmpTree.createWC())
      ret.append(fs)
    for p in self.PF:
      if p.numOfChildren() == 0 and p != TmpTree.createWC():
        local = list()
        if hasWC:
          local.append(TmpTree.createWC())
        local.append(p)
        ret.append(local)
    return ret
  
  def iterate(self, hasWC):
    # create dictionary of labels
    F = dict()
    lastiter = len(self.iteration) - 1
    ret = list(self.iteration[lastiter])
    for p in self.PF:
      if p.numOfChildren() > 0 and p.getSymbol() not in F:
        F[p.getSymbol()] = p
    
    for sym,tree in F.items():
      MSP = list()
      numChildren = tree.numOfChildren()
      R = product(self.iteration[lastiter], repeat=numChildren)
      for r in R:
        lst = list()
        for i in r:
          lst.append(i)
        MSP.append(list(product(*lst)))

      for m in MSP:
        withSym = list()
        if hasWC:
          withSym.append(TmpTree.createWC())
        for pair in m:
          localTree = TmpTree(sym, len(pair))
          for i in range(1, len(pair) + 1):
            localTree.addChild(pair[i-1], i)
          withSym.append(localTree)
        intersectResult = TmpTree.intersect(self.PF, withSym)
        if not TableBuilder.containsCollection(intersectResult, ret):
          ret.append(intersectResult)
    return ret

  @staticmethod
  def treeCollectionsEqual(treeCollecA, treeCollecB):
    # Check if collection A contains the same collection of trees as collection B
    if len(treeCollecA) != len(treeCollecB):
      return False
    for a in treeCollecA:
      if not TableBuilder.containsCollection(a, treeCollecB):
        return False
    return True

  def generateMatchSet(self):
    wc = TmpTree.createWC()
    wildcardInPF = wc.equalsExists(self.PF)

    self.iteration.append(self.initIteration(wildcardInPF))

    while True:
      self.iteration.append(self.iterate(wildcardInPF))
      iterlen = len(self.iteration)
      if TableBuilder.treeCollectionsEqual(self.iteration[iterlen - 1], self.iteration[iterlen - 2]):
        break
    
  @staticmethod
  def reduceMatchSet(matchset):
    reducedMS = list(matchset)
    toRemove = list()

    for i in range(0, len(reducedMS)):
      for j in range(0, len(reducedMS)):
        if reducedMS[i].subsumes(reducedMS[j]) and i != j:
          toRemove.append(reducedMS[i])
          break

    for rm in toRemove:
      reducedMS.remove(rm)
    
    return reducedMS

  @staticmethod
  def computeMatchingTuples(MS, mapping):
    ''' Computes list of stateId tuples that subsume match set`s (MS) children. Used to compute which table entries map to MS. '''
    wc = TmpTree.createWC()
    childMapping = list()
    
    # initializing childMappings
    for tree in MS:
      if tree != wc:
        for i in range(1, tree.numOfChildren() + 1):
          childMapping.append(dict(mapping))
        break

    # remove match sets from childMapping that can't possibly map to MS
    for tree in MS:
      if tree != wc:
        for i in range(1, tree.numOfChildren() + 1):
          child = tree.childAt(i)
          for stateId,matchset in childMapping[i-1].items():
            for matchtree in matchset:
              #if not child.subsumes(matchtree) and not child.unifiesWith(matchtree):
              if not child.subsumes(matchtree) and not (TableBuilder.matchSetSubset({child}, matchset) and len(matchset) > 1):
                del childMapping[i-1][stateId]
                break
    
    ret = product(*childMapping)
    return ret

  @staticmethod
  def retrieveRootedLabel(matchset):
    wc = TmpTree.createWC()
    for t in matchset:
      if t != wc:
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
    if TableBuilder.matchSetSubset(MS1, MS2):
      return MS2
    elif TableBuilder.matchSetSubset(MS2, MS1):
      return MS1

    for t1 in MS1:
      if not TableBuilder.setSubsume(t1, MS2):
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
    wc = TmpTree.createWC()
    wildcardInPF = wc.equalsExists(self.PF)

    finalIterIdx = len(self.iteration) - 1
    finalIter = list(self.iteration[finalIterIdx])

    stateMapping = dict()

    # numbering matching sets to be used for states
    for i in range(0, len(finalIter)):
      stateMapping[i] = finalIter[i]
    
    tables = Tables(stateMapping)

    # Create tables for each label found in matching sets
    for stateId, matchset in stateMapping.items():
      for tree in matchset:
        # If wildcard exists in PF, initialize using state with only the wildcard
        initialValue = None
        if wildcardInPF:
          tmpList = list()
          tmpList.append(wc)
          initialValue = tables.getStateId(tmpList)
        if tree != wc:
          tables.addTable(tree.getSymbol(), tree.numOfChildren(), initialValue)
    
    # reduce the match sets in the mapping s.t. only the most specific remain
    reducedStateMapping = dict()
    for stateId,matchset in stateMapping.items():
      reducedStateMapping[stateId] = TableBuilder.reduceMatchSet(matchset)

    for stateId,matchset in reducedStateMapping.items():
      for tree in matchset:
        if tree != wc and tree.numOfChildren() == 0:
          tables.assignValue(tree.getSymbol(), stateId)
      
      rootLabel = self.retrieveRootedLabel(matchset)
      allowedTuples = TableBuilder.computeMatchingTuples(matchset, reducedStateMapping)

      for tupl in allowedTuples:
        if rootLabel is not None:
          setAtTupl = tables.retrieveValue(rootLabel, *tupl)
          if setAtTupl is not None:
            msAtTupl = reducedStateMapping[setAtTupl]
            # FIXME: split mostSpecificMatchSet for different cases (i.e. subsumption and subset)
            mostSpecific = TableBuilder.mostSpecificMatchSet(msAtTupl, matchset)
            tables.assignValue(rootLabel, Tables.stateId(reducedStateMapping, mostSpecific), *tupl)
      
    return tables
  
  def generate(self):
    self.generateMatchSet()
    return self.generateTables()

  @staticmethod
  def generatePatternForest(patterns):
    PF = set()
    todo = set(patterns)

    while todo:
      p = todo.pop()
      if not p.equalsExists(PF):
        PF.add(p)
      for i in range(1, p.numOfChildren() + 1):
        todo.add(p.childAt(i))
    return PF
  
  @staticmethod
  def dumpiter(iteration):
    for frozenst in iteration:
      print('frozenset:'),
      for s in frozenst:
        print(s.getSymbol()),
      print('')

def generate_tables(opts, out):
  trees = list()
  t1 = TmpTree('A', 2)
  t1_2 = TmpTree('B', 0)
  t1_1 = TmpTree('A', 2)
  t1_1_1 = TmpTree('B', 0)
  t1_1_2 = TmpTree('%', 0)
  
  t1_1.addChild(t1_1_1, 1)
  t1_1.addChild(t1_1_2, 2)

  t1.addChild(t1_1, 1)
  t1.addChild(t1_2, 2)

  t2 = TmpTree('A', 2)
  t2_1 = TmpTree('A', 2)
  t2_2 = TmpTree('C', 0)
  t2_1_1 = TmpTree('%', 0)
  t2_1_2 = TmpTree('C', 0)

  t2_1.addChild(t2_1_1, 1)
  t2_1.addChild(t2_1_2, 2)

  t2.addChild(t2_1, 1)
  t2.addChild(t2_2, 2)

  trees.append(t1)
  trees.append(t2)

  tb = TableBuilder(trees)
  tbs = tb.generate()
  print(tbs.tables)
