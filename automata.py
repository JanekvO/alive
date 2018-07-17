
from graphviz import Digraph

Epsilon = u'\u03B5'

# A graph is a dictionary where the key is the source, and the value is another
# dictionary with the transition label as key with a list of destinations as
# values
# E.g.  '{ '0' : { 'a' : [ '1', '2' ] } }' which means that vertex 0 has two outgoing 
# 'a' symbol transitions towards verteces 1 and 2
class FiniteAutomata(object):
  def __init__(self):
    self.graph = {}
    self.final = set()
    self.states = set()

  # Add state to final state
  def finalizeState(self, state):
    if state not in self.states:
      self.addState(state)
    self.final.add(state)

  # Add state to initial state
  def initializeState(self, state):
    if state not in self.states:
      self.addState(state)
    self.init = state

  # Add new state to states
  def addState(self, state):
    self.states.add(state)

  # Add new transition
  def addTransition(self, symbol, source, destination):
    assert(source in self.states), "Add source to a state first!"
    assert(destination in self.states), "Add destination to a state first!"

    if source in self.graph:
      if symbol in self.graph[source]:
        if destination not in self.graph[source][symbol]:
          self.graph[source][symbol].append( destination )
      else:
        self.graph[source].update( { symbol : [ destination ] } )
    else:
      self.graph.update( { source : { symbol : [ destination ] } } )

  # Show graphical representation of finite automata
  def show(self,name):
    addedNodes = []
    dot = Digraph(format='png')
    addedNodes.append(self.init)
    for fs in self.final:
      addedNodes.append(fs)
    dot.node(str(self.init), 'initial')
    for fs in self.final:
      dot.node(fs, fs, { 'color' : 'green' })
    for src,edg in self.graph.items():
      if src not in addedNodes:
        dot.node(str(src), str(src))
      addedNodes.append(src)
      for sym,dst in edg.items():
        for d in dst:
          if d not in addedNodes:
            addedNodes.append(d)
            dot.node(str(d), str(d))
          dot.edge(str(src), str(d), sym)
    dot.render(name, cleanup=True)
  
  def dump(self):
    print('Init: ' + str(self.init))
    print('final: ' + str(self.final))
    for src,dst in self.graph.items():
      print(src , dst)

class NFA(FiniteAutomata):
  def __init__(self, symbol = None):
    super(NFA, self).__init__()
  
  # Adding an epsilon transition
  def addEpsilonTransition(self, source, destination):
    super(NFA, self).addTransition(Epsilon, source, destination)

  # Check if this NFA is constrained enough to be a DFA already
  # i.e. (1) check if all transitions from same state, using same symbol
  # have only 1 destination, and (2) check whether there are any epsilon
  # transitions. 
  def canBeDFA(self):
    for src,edg in self.graph.items():
      for sym,dst in edg.items():
        if len(dst) > 1 or sym is Epsilon:
          return False
    return True
  
  # If it already conforms to the constraints of a DFA, just cast it directly
  # instead of having to apply subset/powerset construction.
  def castToDFA(self):
    assert(self.canBeDFA()), "NFA is not constrained enough to be a DFA."
    df = DFA()
    df.graph = self.graph
    df.init = self.init
    df.final = self.final
    return df

class DFA(FiniteAutomata):
  def __init__(self):
    super(DFA,self).__init__()

  def addTransition(self, symbol, source, destination):
    assert(symbol is not Epsilon), "No epsilon transitions allowed in NFAs"
    assert(source not in self.graph or (source in self.graph and symbol not in self.graph[source])), \
      "Transition from '{0}' using symbol '{1}' already exists".format(source, symbol)
    super(DFA,self).addTransition(symbol, source, destination)

  def minimize(self):
    F = frozenset(self.final)
    notF = frozenset(s for s in self.graph.keys() if s not in F)

    PPartition = set([F, notF])
    WPartition = set([F])

    print('Num of states before: {}'.format(len(self.graph.keys())))

    while len(WPartition) is not 0:
      A = WPartition.pop()
      X = {}
      for src,edg in self.graph.items():
        for sym,dst in edg.items():
          if dst[0] in A:
            if sym not in X:
              X[sym] = set(src)
            else:
              X[sym].add(src)

      for sym in X.keys():
        newPPartition = set(PPartition)
        for Y in newPPartition:
          inter = Y & X[sym]
          dif = Y - X[sym]

          if len(inter) is not 0 and len(dif) is not 0 and Y in PPartition:
            PPartition.remove(Y)
            PPartition.add(frozenset(inter))
            PPartition.add(frozenset(dif))
            if Y in WPartition:
              WPartition.remove(Y)
              WPartition.add(frozenset(inter))
              WPartition.add(frozenset(dif))
            else:
              if len(inter) <= len(dif):
                WPartition.add(frozenset(inter))
              else:
                WPartition.add(frozenset(dif))

    for P in PPartition:
      rep = list(P)[0]
      for r in P:
        if r is not rep:
          for src,edg in self.graph.items():
            for sym,dst in edg.items():
              if r is dst[0]:
                self.graph[src][sym].remove(r)
                self.graph[src][sym].append(rep)
        if len(P) > 1 and r is not rep:
          if r in self.graph.keys():
            del self.graph[r]
          if r in self.states:
            self.states.remove(r)
          if r in self.final:
            self.final.remove(r)

    print('Num of states after: {}'.format(len(self.graph.keys())))
