from treepatternmatching import *
from bottomuptree import *
from itertools import product, izip, count
from gen import get_root
from codegen import *
from gen import llvm_opcode
from language import Icmp
from bottomupprec import *
from topologicalorder import *
import pickle

from pdb import set_trace

DO_STATS = True
SIMPLIFY = True
LIMITER = False

PICKLED = True
#PICKLEOBJ = "MatchSets.obj"
PICKLEOBJ = "suiteopt.obj"

class BUpeepholeopt(peepholeoptimization):
  def __init__(self, rule, name, pre, source, target, target_skip):
    super(BUpeepholeopt, self).__init__(rule, name, pre, source, target, target_skip)
    self.src_root = get_root(source)
    self.tgt_root = get_root(target)
    self.pred = BUBoolPred.predToBUPred(pre)
    self.src_tree = BUExprTree.createWithExpr(self.src_root, ['s'])
    self.tgt_tree = BUExprTree.createWithExpr(self.tgt_root, ['t'])
    self.src_tree.setRelatedRule(rule)

# Minimizes tables by taking an intermediate step in terms of table
# So instead of mapping y1 x y2 x ... x yn to a value we first take the mapping function f of each value which maps to a smaller table
# i.e. f(y1) x f(y2) x ... x f(yn) which maps to the smaller variant of the smaller table
class MinimizedTables(object):
  def __init__(self, statemapping, symbolMapping):
    self.mapping = statemapping
    self.symMap = symbolMapping
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

    tables = MinimizedTables(stateMapping, self.retrieveSymbols())

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

  def save(self, filename = 'TableBuild.obj'):
    fileobj = open(filename,'wb')
    pickle.dump(self.patterns, fileobj)
    pickle.dump(self.PF,fileobj)
    pickle.dump(self.iteration,fileobj)
    pickle.dump(self.representerSet,fileobj)
    pickle.dump(self.childSets,fileobj)
    fileobj.close()

  def load(self, filename = 'TableBuild.obj'):
    fileobj = open(filename,'rb')
    self.patterns = pickle.load(fileobj)
    self.PF = pickle.load(fileobj)
    self.iteration = pickle.load(fileobj)
    self.representerSet = pickle.load(fileobj)
    self.childSets = pickle.load(fileobj)
    fileobj.close()

  def generate(self, pickled = False):
    #tbos = 'TableBuilderObject.obj'
    #tbos = 'suiteopt.obj'
    if not pickled:
      self.generateMatchSet()
      self.save(PICKLEOBJ)
    else:
      self.load(PICKLEOBJ)

    tables = self.generateTables()
    return tables

  @staticmethod
  def generatePatternForest(patterns):
    PF = list()
    todo = list(patterns)

    while todo:
      p = todo.pop()
      if not p.equalsExists(PF):
        PF.append(p)
      else:
        # there might be a q in PF for which p == q, except p also has code transformation information
        if p.relatedRuleId != None:
          for q in PF:
            # FIXME: Support multiple tree patterns with differing constrains
            if p == q and q.relatedRuleId == None:
              PF.remove(q)
              PF.append(p)
      for i in xrange(1, p.numOfChildren() + 1):
        todo.append(p.childAt(i))
    return PF
  
  @staticmethod
  def dumpiter(iteration):
    for st in iteration:
      print('set:'),
      for s in st:
        print(s.getSymbol()),
      print('')

######################################################
######################################################
######################################################
###############    codegen below    ##################
######################################################
######################################################
######################################################

class SwitchCaseHelp(object):
  def __init__(self, switchValue):
    self.switchValue = switchValue
    self.cases = dict()
    self.default = []

  def addCase(self, caseValue, code):
    self.cases[tuple(caseValue)] = code

  def addToExistingCase(self, existing, addition):
    for case in self.cases:
      if existing in case:
        lst = list(case)
        lst.append(addition)
        newtup = tuple(lst)
        self.cases[newtup] = self.cases[case]
        del self.cases[case]
        break

  def setDefault(self, code):
    assert(isinstance(code, list))
    self.default = code

  def addToDefault(self, code):
    self.default.append(code)

  def generate(self, codePrepareFunction = None):
    if codePrepareFunction == None:
      return CSwitchCase(self.switchValue, self.cases, self.default)

class BUCodeGenHelper(object):
  def __init__(self, tables, phs, out):
    self.tables = tables
    self.phs = phs
    self.out = out

  # Emit code that doesn't change regardless of input patterns
  def emit_constant_code(self):
    constantStr = '\n' +\
    '#include \"llvm/ADT/DenseMap.h\"\n' +\
    '#include <array>\n' +\
    '#include <vector>\n' +\
    '\n' +\
    'static unsigned retrieveStateValue(Value *V, DenseMap<Value*,unsigned> &sa);\n' +\
    'static unsigned retrieveStateValue(ConstantInt *C);\n' +\
    'static unsigned retrieveStateValue(Instruction *I, DenseMap<Value*,unsigned> &sa);\n' +\
    '\n'
    self.out.write(constantStr)

  def normalizeMapping(self):
    # We need to "normalize" the mapping s.t. the numbers go in sequential
    # order instead of having mappings like [0, 4, 7]
    self.normalizedMapping = {}

    # Initialize
    for sym,tree in self.tables.symMap.items():
      self.normalizedMapping[sym] = dict()
      for i in xrange(1, tree.numOfChildren() + 1):
        self.normalizedMapping[sym][i] = dict()

    mapLen = len(self.tables.mapping)

    # Normalize
    for sym,tree in self.tables.symMap.items():
      numCh = tree.numOfChildren()
      if numCh > 0:
        lst = self.tables.tables[sym]
        curCh = 1
        localMapping = 0
        while isinstance(lst, dict):
          for element in lst:
            if element not in self.normalizedMapping[sym][curCh]:
              self.normalizedMapping[sym][curCh][element] = localMapping
              localMapping += 1
          curCh += 1
          lst = lst[element]
          localMapping = 0

  def emit_statemapping(self):
    mapLen = len(self.tables.mapping)
    nrMap = len(self.tables.symMap)
    startStr = 'static const std::array<std::vector<' +\
      'std::array<unsigned,{}>>,{}> computeMap = {{{{\n'.format( \
      mapLen, nrMap)
    endStr = '}};\n\n'
    mapStr = ''
    # Use the order as defined in symMap
    for sym,tree in self.tables.symMap.items():
      if tree.numOfChildren() > 0:
        mapStr = mapStr + '  {{ // ' + sym + '\n'
        multiplyOffset = 1
        for ch,stateMapping in self.tables.tableMap[sym].items():
          mapStr = mapStr + '    {{'
          for i in xrange(mapLen):
            value = stateMapping[i]
            normalizedValue = self.normalizedMapping[sym][ch][value]
            # Apply offset for easier lookup in generated code
            multipliedValue = normalizedValue * multiplyOffset
            mapStr = mapStr + str(multipliedValue) + ','
          multiplyOffset *= len(self.normalizedMapping[sym][ch])
          mapStr = mapStr + '}},\n'
        mapStr = mapStr + '  }},\n'

    self.out.write(startStr)
    self.out.write(mapStr)
    self.out.write(endStr)

  def emit_tables(self):
    outStr = ''
    computeTables = list()
    for sym, tree in self.tables.symMap.items():
      outStr += 'static const unsigned {}ComputeTable['.format(sym)
      computeTables.append('{}ComputeTable'.format(sym))
      chNum = tree.numOfChildren()
      if chNum > 0:
        childrenList = list()
        curChild = self.tables.tables[sym]
        for i in xrange(1, chNum + 1):
          lenValue = len(self.normalizedMapping[sym][i])
          childList = list()
          outStr += str(lenValue)
          if i != chNum:
            outStr += '*'
          for stateId in curChild:
            childList.append(stateId)
          curChild = curChild[stateId]
          childrenList.append(childList)
        # All these reversals seem stupid, but they enforce the order in which
        # the values should occur
        childrenList.reverse()
        chCartProd = product(*childrenList)
        outStr += '] = {'
        for el in chCartProd:
          idx = reversed(el)
          tableValue = self.tables.retrieveValue(sym, *idx)
          outStr += str(tableValue) + ','
      outStr += '};\n'
    symMapLen = len(self.tables.symMap)
    outStr += '\nstatic const unsigned *computeTables[{}] = '.format(symMapLen)
    outStr += '{\n'
    for cc in computeTables:
      outStr += '  ' + cc + ',\n'
    outStr += '};\n'

    self.out.write(outStr)

  PossibleBinopWithFlags = {
    'add' : 0b11,
    'sub' : 0b11,
    'mul' : 0b11,
    'udiv' : 0b1,
    'sdiv' : 0b1,
    'shl' : 0b11,
    'ashr' : 0b1,
    'lshr' : 0b1,
  }

  PossibleFlags = {
    'exact' : 0b1,
    'nuw' : 0b01,
    'nsw' : 0b10,
  }

  def emit_exist_mapping(self):
    mappingExistsStart = '\nstatic bool opcodeMappingExists(const Instruction *I) {\n'
    mappingExistsEnd = '\n}\n'
    retTrue = CReturn(CVariable('true'))
    retFalse = CReturn(CVariable('false'))
    var = CVariable('I')
    existsSC = SwitchCaseHelp(var.arr('getOpcode', ''))
    existsSubSC = dict()

    for sym,tree in self.tables.symMap.items():
      caseVar = CVariable(llvm_opcode[tree.symbol])
      if tree.symbol in self.PossibleBinopWithFlags:
        if tree.symbol not in existsSubSC:
          rhs = var.arr('getRawSubclassOptionalData', '')
          lhs = CVariable(hex(self.PossibleBinopWithFlags[tree.symbol]))
          existsSubSC[tree.symbol] = SwitchCaseHelp(\
            CBinExpr('&', rhs, lhs))
          existsSubSC[tree.symbol].addToDefault(retFalse)
        val = 0b00
        for f in tree.flags:
          val = val | self.PossibleFlags[f]
        cVal = CVariable(hex(val))
        existsSubSC[tree.symbol].addCase([cVal], [retTrue])
      elif tree.symbol == 'icmp':
        # FIXME:  Currently doesn't support variable predicates. Are variable
        #         predicates even used?
        if tree.symbol not in existsSubSC:
          existsSubSC[tree.symbol] = SwitchCaseHelp(\
            CFunctionCall('cast<CmpInst>', var).arr('getPredicate', ''))
            #var.arr('getPredicate', ''))
          existsSubSC[tree.symbol].addToDefault(retFalse)
        cVal = CVariable(Icmp.op_enum[tree.auxiliaryOp])
        existsSubSC[tree.symbol].addCase([cVal], [retTrue])
      else:
        existsSC.addCase([caseVar], [retTrue])

    for c,sw in existsSubSC.items():
      existsSC.addCase([CVariable(llvm_opcode[c])], [sw.generate()])

    existsSC.addToDefault(retFalse)

    mappingExists = nest(2, existsSC.generate().format())

    self.out.write(mappingExistsStart)
    self.out.write(mappingExists.format())
    self.out.write(mappingExistsEnd)

  def emit_mapping(self):
    mappingStart = '\nstatic unsigned opcodeMapping(const Instruction *I) {\n'
    mappingEnd = '\n}\n'
    curMap = 0
    var = CVariable('I')
    unreachFunc = CFunctionCall('llvm_unreachable', CCharArray('Function should not be called manually.'))
    existsSC = SwitchCaseHelp(var.arr('getOpcode', ''))
    existsSubSC = dict()

    for sym,tree in self.tables.symMap.items():
      caseVar = CVariable(llvm_opcode[tree.symbol])
      cRet = CReturn(CVariable(str(curMap)))
      if tree.symbol in self.PossibleBinopWithFlags:
        if tree.symbol not in existsSubSC:
          rhs = var.arr('getRawSubclassOptionalData', '')
          lhs = CVariable(hex(self.PossibleBinopWithFlags[tree.symbol]))
          existsSubSC[tree.symbol] = SwitchCaseHelp(\
            CBinExpr('&', rhs, lhs))
        val = 0b00
        for f in tree.flags:
          val = val | self.PossibleFlags[f]
        cVal = CVariable(hex(val))
        existsSubSC[tree.symbol].addCase([cVal], [cRet])
      elif tree.symbol == 'icmp':
        # FIXME:  Currently doesn't support variable predicates. Are variable
        #         predicates even used?
        if tree.symbol not in existsSubSC:
          existsSubSC[tree.symbol] = SwitchCaseHelp(\
            CFunctionCall('cast<CmpInst>', var).arr('getPredicate', ''))
            #var.arr('getPredicate', ''))
        cVal = CVariable(Icmp.op_enum[tree.auxiliaryOp])
        existsSubSC[tree.symbol].addCase([cVal], [cRet])
      else:
        existsSC.addCase([caseVar], [cRet])
      curMap = curMap + 1

    for c,sw in existsSubSC.items():
      existsSC.addCase([CVariable(llvm_opcode[c])], [sw.generate(), unreachFunc])

    mappingSC = nest(2, seq(existsSC.generate().format(), unreachFunc.format()))

    self.out.write(mappingStart)
    self.out.write(mappingSC.format())
    self.out.write(mappingEnd)
  
  def emit_retrieveStateValue_ConstantInt(self):
    start = '\nstatic unsigned retrieveStateValue(ConstantInt *C) {\n'
    end = '\n}\n'
    cGetVal = CVariable('C').arr('getValue','').dot('getSExtValue','')
    switchCase = SwitchCaseHelp(cGetVal)

    for idState,ms in self.tables.mapping.items():
      caseCode = CReturn(CVariable(str(idState)))
      reducedms = TableBuilder.reduceMatchSet(ms)
      if len(reducedms) == 1:
        msVal = reducedms[0]
        if msVal.nodeType() == NodeType.ConstWildcard:
          switchCase.setDefault([caseCode])
        elif msVal.nodeType() == NodeType.ConstVal:
          caseValue = CVariable(str(reducedms[0].val))
          switchCase.addCase([caseValue], [caseCode])

    switchCaseCode = nest(2, switchCase.generate().format())

    self.out.write(start)
    self.out.write(switchCaseCode.format())
    self.out.write(end)

  def emit_retrieveStateValue_InstMap(self):
    start = '\nstatic unsigned retrieveStateValue(Instruction *I, ' +\
      'DenseMap<Value*,unsigned> &sa) {\n'
    end = '}\n'

    assert(self.tables.defaultInit is not None), \
      'No wildcard not supported yet for bottom-up matching'
    
    body = \
    '  unsigned offset = 0;\n' +\
    '  unsigned child = 0;\n' +\
    '  if(!opcodeMappingExists(I))\n' +\
    '    return {};\n'.format(self.tables.defaultInit) +\
    '  for (Value *op : I->operands()) {\n' +\
    '    unsigned ms = {};\n'.format(self.tables.defaultInit) +\
    '    if(!sa.count(op)) {\n' +\
    '      ms = retrieveStateValue(op, sa);\n' +\
    '      sa.insert(std::make_pair(op, ms));\n' +\
    '    } else {\n' +\
    '      ms = sa[op];\n' +\
    '    }\n' +\
    '    offset += computeMap[opcodeMapping(I)][child][ms];\n' +\
    '    child++;\n' +\
    '  }\n' +\
    '  const unsigned *computeTable = computeTables[opcodeMapping(I)];\n' +\
    '  return computeTable[offset];\n'

    self.out.write(start)
    self.out.write(body)
    self.out.write(end)

  def emit_retrieveStateValue_ValMap(self):
    start = '\nstatic unsigned retrieveStateValue(Value *V, ' +\
      'DenseMap<Value*, unsigned> &sa) {\n'
    end = '\n}\n'
    vVar = CVariable('V')
    saVar = CVariable('sa')

    isaConstCall = CFunctionCall('isa<ConstantInt>', vVar)
    isaInstCall = CFunctionCall('isa<Instruction>', vVar)
    ConstIntCast = CFunctionCall('cast<ConstantInt>', vVar)
    InstCast = CFunctionCall('cast<Instruction>', vVar)
    ConstIntRet = CReturn(CFunctionCall('retrieveStateValue', ConstIntCast))
    InstRet = CReturn(CFunctionCall('retrieveStateValue', InstCast, saVar))

    ifList = [
      (isaConstCall, [ConstIntRet]),
      (isaInstCall, [InstRet])
    ]

    elseBody = [CReturn(CVariable(str(self.tables.defaultInit)))] \
      if self.tables.defaultInit is not None else []
    cifelse = CElseIf(ifList, elseBody)

    cifelseCode = cifelse.format()

    self.out.write(start)
    self.out.write(cifelseCode.format())
    self.out.write(end)

  def emit_runOnInst(self, topoSort):
    start = 'Instruction *InstCombiner::runOnInstruction(Instruction*I, ' +\
      'DenseMap<Value*,unsigned> &sa) {\n'
    mid = ['x = cast<Value>(I);',
          'unsigned tableValue = retrieveStateValue(I, sa);',
          'sa.insert(std::make_pair(x, tableValue));']
    end = '}\n'

    mapping = self.tables.mapping
    exprToMatchsets = dict()
    switchCase = SwitchCaseHelp(CVariable('tableValue'))
    defaultCode = [CReturn(CVariable('nullptr'))]
    switchCase.setDefault(defaultCode)
    usedVars = {}

    for stateId,ms in mapping.items():
      self.out.write("// {}: {}\n".format(stateId, ms))
      red = TableBuilder.reduceMatchSet(ms)
      # TODO: figure out a way to process multiple unified tree patterns.
      # For now we process the first one.
      for t in red:
        if t.relatedRuleId is not None:
          if t not in exprToMatchsets:
            exprToMatchsets[t.relatedRuleId] = list()
          exprToMatchsets[t.relatedRuleId].append(stateId)
          break

    # Creating phony cases that are never jumped towards using the switch case and only used as fallback options
    phonyId = len(mapping) + 1
    for ph in self.phs:
      if ph.rule not in exprToMatchsets:
        exprToMatchsets[ph.rule] = [phonyId]
        phonyId += 1

    cur = 1
    for r,ms in exprToMatchsets.items():
      e = self.phs[r].src_tree
      transformHelper = TransformationHelper(e, self.phs, topoSort)
      gen = transformHelper.generateTransformation()
      caseVar = []
      for i in ms:
        caseVar.append(CVariable(i))
      switchCase.addCase(caseVar, gen)
      for v,t in transformHelper.cgm.name_type.iteritems():
        if v not in usedVars:
          usedVars[v] = t
      cur = cur + 1

    decl_it = CDefinition.block((t, CVariable(v))
      for v,t in usedVars.iteritems())
    decl = iter_seq(line + d.format() for d in decl_it)

    switchCaseCode = nest(2, seq(decl, line,
                                  mid[0], line,
                                  mid[1], line,
                                  mid[2], line,
          switchCase.generate().format()))

    self.out.write(start)
    self.out.write(switchCaseCode.format())
    self.out.write('\n' + end)

  def emit_code(self, topoSort):
    self.emit_constant_code()
    self.normalizeMapping()
    self.emit_statemapping()
    self.emit_tables()
    self.emit_exist_mapping()
    self.emit_mapping()
    self.emit_retrieveStateValue_ConstantInt()
    self.emit_retrieveStateValue_InstMap()
    self.emit_retrieveStateValue_ValMap()
    self.emit_runOnInst(topoSort)

class EquivalenceGenerator(object):
  def __init__(self, manager, tree):
    self.tree = tree
    self.manager = manager
    self.bound = {}

  def processSubtree(self, path):
    subtree = self.tree.subtree(path)
    var = createVar(path)
    # Seems a bit unnecessary to check whether multiple
    # equivalent constant values are the same
    if subtree.nodeType() == NodeType.ConstVal:
      return

    assert(len(subtree.name) > 0)

    if subtree.name not in self.bound:
      self.bound[subtree.name] = [var]
    else:
      self.bound[subtree.name].append(var)

  def equivalenceCode(self):
    eqclauses = []
    for st,lst in self.bound.items():
      lstlen = len(lst)
      if lstlen >= 2:
        for i in xrange(1, lstlen):
          e1 = lst[i-1]
          e2 = lst[i]
          eqclauses.append(CBinExpr('==', CVariable(e1), CVariable(e2)))
    return eqclauses

class TransformationHelper(object):
  binop = ['add', 'sub', 'mul', 'udiv', 'sdiv', 'urem', 'srem', 'shl', 'ashr',
           'lshr', 'and', 'or', 'xor']
  convop = ['trunc', 'zext', 'sext', 'ZExtOrTrunc', 'ptrtoint',
            'inttoptr', 'bitcast']

  def __init__(self, tree, phs, topo):
    self.tree = tree
    self.topo = topo
    self.phs = phs
    self.cgm = CodeGeneratorManager()
    self.eg = EquivalenceGenerator(self.cgm, tree)

  # Blatantly copy-pasted from gen.py
  @staticmethod
  def minimal_type_constraints(ty_exp, required, guaranteed):
    if isinstance(required, BUIntType):
      if not isinstance(guaranteed, BUIntType):
        if required.defined:
          return [CFunctionCall('isa<IntegerType>', ty_exp),
            CBinExpr('==',
              ty_exp.arr('getScalarSizeInBits', []),
              CVariable(str(required.size)))]

        return [CFunctionCall('isa<IntegerType>', ty_exp)]

      if required.defined and not guaranteed.defined:
        return [CBinExpr('==',
          ty_exp.arr('getScalarSizeInBits', []),
          CVariable(str(required.size)))]

      return []

    if isinstance(required, BUPtrType):
      if not isinstance(guaranteed, BUPtrType):
        raise AliveError("Pointer types not supported")

      return []

    if isinstance(required, BUArrayType):
      raise AliveError("Array types not supported")

    assert(isinstance(required, BUUnknownType))

    reqs = required.types.keys()
    reqs.sort()

    guars = guaranteed.types.keys()
    guars.sort()

    if reqs == [Type.Int, Type.Ptr] and Type.Array in guars:
      return [CVariable('<int-or-ptr>')]

    return []

  def generateTransformation(self):
    rule = self.tree.relatedRuleId
    clauses = []  # if statement clauses
    body = [] # code body
    initialize = [] # variables initialize code

    todo = [[]]

    print("Currently processing rule {}: {}".format(rule, self.phs[rule].name))

    # if rule == 3:
    #   set_trace()

    while todo:
      #coordinate = todo.pop(0)
      coordinate = todo.pop()
      tree = self.tree.subtree(coordinate)
      if tree.numOfChildren() > 0:
        toAdd = []
        for i in range(1, tree.numOfChildren() + 1):
          next_coor = copy.deepcopy(coordinate)
          next_coor.append(i)
          toAdd.append(next_coor)
        todo.extend(reversed(toAdd))
      if coordinate:
        coorVar = CVariable(createVar(coordinate))
        parentVar = CVariable(createVar(coordinate[:-1]))
        cast = CFunctionCall('cast<Instruction>', parentVar).arr('getOperand', [CVariable(coordinate[-1] - 1)])
        initialize.append(CAssign(coorVar, cast))
      if not self.cgm.bound(tree):
        self.cgm.bind_tree(tree)
        tree.register_types(self.cgm)
      self.cgm.add_path_var(tree, coordinate)
      self.eg.processSubtree(coordinate)

    self.cgm.phase = self.cgm.Target

    pred = self.phs[rule].pred
    pred.register_types(self.cgm)

    for name in self.cgm.named_types:
      self.cgm.unify(*self.cgm.named_types[name])

    tgt_tree = self.phs[rule].tgt_tree

    todo = [[]]
    todoTgtTyRegister = []


    # while todo:
    #   coordinate = todo.pop(0)
    #   tree = tgt_tree.subtree(coordinate)
    #   if tree.numOfChildren() > 0:
    #     for i in range(1, tree.numOfChildren() + 1):
    #       next_coor = copy.deepcopy(coordinate)
    #       next_coor.append(i)
    #       todo.append(next_coor)
    #   tree.register_types(self.cgm)
    while todo:
      coordinate = todo.pop(0)
      tree = tgt_tree.subtree(coordinate)
      if (tree.nodeType() == NodeType.ConstVal and tree.coordinate[0] == 's') \
        or isinstance(tree, BUInput):
        continue
      if tree.numOfChildren() > 0 and tree.nodeType() != NodeType.ConstOperation:
        toAdd = []
        for i in range(1, tree.numOfChildren() + 1):
          next_coor = copy.deepcopy(coordinate)
          next_coor.append(i)
          toAdd.append(next_coor)
        todo.extend(reversed(toAdd))
      todoTgtTyRegister.append(tree)
    
    todoTgtTyRegister.reverse()

    # if rule == 3:
    #   set_trace()

    for t in todoTgtTyRegister:
      t.register_types(self.cgm) 

    self.cgm.unify(self.tree, tgt_tree)
    tgt_name = '_' + re.sub('[^a-zA-Z0-9_]', '', tgt_tree.name)
    self.cgm.value_names[tgt_tree] = tgt_name
    clauses.extend(self.cgm.clauses)

    for v,t in self.cgm.guaranteed.iteritems():
      if not self.cgm.bound(v) or v.nodeType() == NodeType.ConstVal:
        continue
      clauses.extend(self.minimal_type_constraints(\
        self.cgm.get_llvm_type(v), \
        self.cgm.required[v], \
        t))

    if not isinstance(pred, BUTruePred):
      clauses.append(pred.visitPrecondition(self.cgm))

    if DO_STATS and LIMITER:
      clauses.append(CBinExpr('<', CVariable('Rule' + str(rule)), CVariable('10000')))

    if DO_STATS:
      body = [CUnaryExpr('++', CVariable('Rule' + str(rule)))]

    todo = [[]]
    transformCode = []
    skip = set()

    while todo:
      coordinate = todo.pop(0)
      tree = tgt_tree.subtree(coordinate)
      if tree.numOfChildren() > 0:
        for i in range(1, tree.numOfChildren() + 1):
          next_coor = copy.deepcopy(coordinate)
          next_coor.append(i)
          todo.append(next_coor)
      nt = tree.nodeType()
      if tree != tgt_tree and tree not in skip and (nt == NodeType.Operation or isinstance(tree, BUCopyOperand)):
        skip.add(tree)
        transformCode.append(tree.targetVisit(coordinate, self.cgm, True)) 

    transformCode.reverse()
    for t in transformCode:
      body.extend(t)

    if isinstance(tgt_tree, BUCopyOperand):
      body.append(
        CDefinition.init(
          self.cgm.PtrInstruction,
          self.cgm.get_cexp(tgt_tree),
          CFunctionCall('replaceInstUsesWith', \
            CVariable('*I'), \
            self.cgm.get_cexp(tgt_tree.childAt(1)))))
    else:
      body.extend(tgt_tree.targetVisit([], self.cgm, False))

    body.append(CReturn(self.cgm.get_cexp(tgt_tree)))

    # Force equivalence code to occur prior to the other clauses
    clauses = self.eg.equivalenceCode() + clauses

    initialize.append(CLabel('transformation_' + str(rule)))

    const_casts = list()
    for c,p in self.cgm.const_path.items():
      pathVar = CVariable(createVar(p))
      constVar = CVariable(c)
      cast = CFunctionCall('dyn_cast<ConstantInt>', pathVar)
      const_casts.append(CAssign(constVar, cast))

    clauses = const_casts + clauses

    if clauses:
      if self.topo.hasChild(rule):
        childRule = self.topo.next(rule)
        childStr = 'transformation_' + str(childRule)
        cif = CIf(CBinExpr.reduce('&&', clauses), body, [CGoto(CLabel(childStr))])
      else:
        cif = CIf(CBinExpr.reduce('&&', clauses), body, [CReturn(CVariable('nullptr'))])
      return initialize + [cif]
    else:
      return initialize + body

# Not inheriting the CG in gen.py since we don't have the old expression
# and we don't care about source part matching since that's covered by the
# BU tree pattern matcher
class CodeGeneratorManager(object):
  Initialization, Target = range(2)

  PtrConstantInt = CPtrType(CTypeName('ConstantInt'))
  PtrValue = CPtrType(CTypeName('Value'))
  PtrInstruction = CPtrType(CTypeName('Instruction'))

  def __init__(self):
    self.const_path = dict() # value -> path
    self.value_names = {} # value -> name
    self.key_names = {}   # key -> name
    self.names = set()    # all created names
    self.name_type = {}   # name -> ctype
    self.bound_vl = set() # value -> path
    self.reps = {}        # coordinate tuple -> value
    self.coor_values = {} # coordinate tuple -> value
    self.required = {}    # value -> type
    self.guaranteed = {}  # value -> type
    self.named_types = defaultdict(set)
    self.phase = self.Initialization
    self.clauses = []

  # As derived from get_most_specific_type in gen.py.
  @staticmethod
  def get_most_specific_BUtype(t1, t2):
    if isinstance(t1, BUUnknownType):
      if isinstance(t2, BUIntType):
        return CodeGeneratorManager.get_most_specific_BUtype(t1.types[Type.Int], t2)
      elif isinstance(t2, BUPtrType):
        return CodeGeneratorManager.get_most_specific_BUtype(t1.types[Type.Ptr], t2)
      elif isinstance(t2, BUArrayType):
        return CodeGeneratorManager.get_most_specific_BUtype(t1.types[Type.Array], t2)

      types = [(s, CodeGeneratorManager.get_most_specific_BUtype(t, t2.types[s]))
        for (s,t) in t1.types.iteritems() if s in t2.types]

      assert(len(types))

      if len(types) == 1:
        return types[0][1]

      retTy = BUUnknownType()
      retTy.types = dict(types)
      return retTy

    if isinstance(t2, BUUnknownType):
      return CodeGeneratorManager.get_most_specific_BUtype(t2, t1)

    assert(t1.__class__ == t2.__class__)
    if isinstance(t1, BUIntType):
      if t1.defined:
        return t1
      else:
        return t2

    if isinstance(t1, BUPtrType):
      return BUPtrType(CodeGeneratorManager.get_most_specific_BUtype(t1.type, t2.type))

    # Not sure how to interpret the order of types when talking about arraytype
    if isinstance(t1, BUArrayType):
      return t1

    assert(False)

  def dumpReps(self):
    for c in self.reps:
      print("{}: {}".format(self.coor_values[c], self.reps[c]))

  def dumpReq(self):
    for v,t in self.required.items():
      print("{} : {}".format(v, t.__class__))

  # Retrieves the tree whose type is unified with the input tree's.
  def get_rep(self, tree):
    # coor = tree.coordinate
    # # if we're currently processing a target tree, copy the
    # # reps information
    # if coor not in self.reps and coor[0] == 't' and \
    #     tree.nodeType() != NodeType.ConstVal:
    #   for c,t in self.coor_values.items():
    #     if t == tree:
    #       print("NEW DUPLICATE REPS FOR {} \t -> \t {} ".format(coor, c))
    #       self.coor_values[coor] = tree
    #       self.reps[coor] = self.reps[c]
    #       break

    # if coor not in self.reps:
    #   self.reps[coor] = None
    #   self.coor_values[coor] = tree
    #   return tree
    # rep = self.reps[coor]
    # if not isinstance(rep, BUExprTree) and rep == None:
    #   return tree
    # rep = self.get_rep(self.reps[coor])
    # self.reps[coor] = rep
    # self.coor_values[coor] = tree
    # return rep

    if tree.nodeType() == NodeType.ConstVal or \
       tree.nodeType() == NodeType.ConstOperation:
      keyVal = tree.coordinate
      self.coor_values[keyVal] = tree
    else:
      keyVal = tree

    if keyVal not in self.reps:
      self.reps[keyVal] = None
      return tree

    rep = self.reps[keyVal]
    if not isinstance(rep, BUExprTree) and rep == None:
      return tree

    rep = self.get_rep(self.reps[keyVal])
    self.reps[keyVal] = rep
    return rep

  def get_llvm_type(self, tree):
    rep = self.get_rep(tree)
    assert(self.bound(rep))
    return self.get_cexp(rep).arr('getType', [])

  @staticmethod
  def value_ctype(tree):
    if tree.nodeType() == NodeType.ConstWildcard:
      return CodeGeneratorManager.PtrConstantInt
    else:
      return CodeGeneratorManager.PtrValue

  def get_cexp(self, var):
    if var.nodeType() == NodeType.ConstVal or \
        var.nodeType() == NodeType.ConstOperation:
      return var.get_Value(self)
    elif var.nodeType() == NodeType.ConstWildcard:
      return CVariable(var)
    elif var in self.value_names:
      name = self.value_names[var]
      return CVariable(name)
    elif len(var.name) > 0:
      name = '_' + re.sub('[^a-zA-Z0-9_]', '', var.name)
      return CVariable(name)
    else:
      assert(False)

  def get_ctype(self, name):
    return self.name_type[name]

  # make a distinction between the constants
  def bound(self, var):
    assert isinstance(var, BUExprTree)
    if var.nodeType() == NodeType.ConstVal or \
       var.nodeType() == NodeType.ConstOperation:
      return var.coordinate in self.bound_vl
    else:
      return var in self.bound_vl

  def bind_tree(self, tree):
    assert tree not in self.bound_vl
    assert isinstance(tree, BUExprTree)

    if tree.nodeType() == NodeType.ConstVal or \
       tree.nodeType() == NodeType.ConstOperation:
      self.bound_vl.add(tree.coordinate)
    else:
      self.bound_vl.add(tree)

  def add_path_var(self, tree, path):
    assert isinstance(tree, BUExprTree)

    if tree.nodeType() == NodeType.ConstWildcard and \
        tree.getSymbol() not in self.names:
      self.add_path_name(tree.getSymbol(), self.PtrConstantInt)
      self.const_path[tree.getSymbol()] = path

    name = createVar(path)
    self.value_names[tree] = name
    self.add_path_name(name, self.PtrValue)

  def add_path_name(self, name, ctype):
    assert name not in self.name_type
    assert isinstance(name, str)
    assert name not in self.names

    self.names.add(name)
    self.name_type[name] = ctype

  def register_type(self, tree, actual, minimal):
    rep = self.get_rep(tree)
    if isinstance(actual, BUNameType):
      self.named_types[actual.type].add(rep)
      actual = actual.type
    if isinstance(minimal, BUNameType):
      minimal = minimal.type

    actual = self.get_most_specific_BUtype(actual, minimal)
    if rep in self.required:
      self.required[rep] = self.get_most_specific_BUtype(actual, self.required[rep])
    else:
      self.required[rep] = actual

    if self.phase == self.Initialization:
      if rep in self.guaranteed:
        self.guaranteed[rep] = self.get_most_specific_BUtype(minimal, self.guaranteed[rep])
      else:
        self.guaranteed[rep] = minimal

  def unify(self, *trees):
    it = iter(trees)
    v1 = it.next()
    r1 = self.get_rep(v1)

    for v2 in it:
      r2 = self.get_rep(v2)
      if r1 == r2:
        continue

      if self.phase == self.Target and self.bound(r1) and self.bound(r2):
        self.clauses.append(
          CBinExpr('==', self.get_llvm_type(r1), self.get_llvm_type(r2)))

      if self.bound(r2) and not self.bound(r1):
        r1, r2 = r2, r1

      if r2.nodeType() == NodeType.ConstVal or \
         r2.nodeType() == NodeType.ConstOperation:
        self.reps[r2.coordinate] = r1
        self.coor_values[r2.coordinate] = r2
      else:
        self.reps[r2] = r1

      if r2 in self.required:
        self.required[r1] = self.get_most_specific_BUtype\
          (self.required[r1], self.required[r2])
        del self.required[r2]

      if r2 in self.guaranteed:
        self.guaranteed[r1] = self.get_most_specific_BUtype\
          (self.guaranteed[r1], self.guaranteed[r2])
        del self.guaranteed[r2]

def buildTables(phs):
  tb = TableBuilder(phs)
  return tb.generate(PICKLED)

def emitCode(tables, phs, out, topoSort):
  buch = BUCodeGenHelper(tables, phs, out)
  buch.emit_code(topoSort)

def generate_tables(opts, out):
  root_opts = defaultdict(list)
  opts = list(izip(count(), opts))

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

  topo = TreeTopoGraph()

  for ph1 in phs:
    for ph2 in phs:
      if ph1.src_tree == ph2.src_tree or ph1.src_tree.isNotComparable(ph2.src_tree):
        continue
      elif ph1.src_tree.subsumes(ph2.src_tree):
        topo.addEdge(ph2.rule, ph1.rule)
      elif ph2.src_tree.subsumes(ph1.src_tree):
        topo.addEdge(ph1.rule, ph2.rule)

  topo.show('nonreduced')
  topo.reduction()
  topo.show('reduced')

  tables = buildTables(phs)

  for i,ms in tables.mapping.items():
    print("{}:\t{}".format(i, ms))
  
  for f,t in tables.tableMap.items():
    print("mapping: {} : {}".format(f, t))
  
  for f,t in tables.tables.items():
    print('###########')
    print(f)
    print(t)
    print("dimension of {}: {}".format(f, tables.dimension(f)))
  
  emitCode(tables, phs, out, topo)

