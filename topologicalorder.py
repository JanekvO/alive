from graphviz import Digraph
from pdb import set_trace

# Tree topological graph, using subsumption partial order
class TreeTopoGraph:
  def __init__(self):
    self.graph = dict()       # graph representation as adjacency list
    self.referenced = set()   # set of references vertices
    self.references = dict()  # hash table to keep count of number of 
                              # references per vertex

  def addVertex(self, vertex):
    if vertex not in self.graph:
      self.graph[vertex] = list()

  def isReferenced(self, vertex):
    return vertex in self.referenced

  def hasDirectRelation(self, src_vertex, dst_vertex):
    return dst_vertex in self.graph[src_vertex]

  def hasTransitiveRelation(self, src_vertex, dst_vertex):
    todo = [src_vertex]

    while todo:
      vertex = todo.pop()
      if dst_vertex in self.graph[vertex]:
        return True
      else:
        todo.extend(self.graph[vertex])

    return False

  def addEdge(self, src, dst):
    if src not in self.graph:
      self.graph[src] = list()
    if dst not in self.references:
      self.references[dst] = 0
    if dst not in self.graph[src]:
      self.graph[src].append(dst)
      self.referenced.add(dst)
      self.references[dst] += 1

  def hasChild(self, node):
    return node in self.graph

  # return next, less specific tree
  def next(self, node):
    assert(self.hasChild(node))
    return self.graph[node][0]

  def topologicalSort(self):
    count = dict()
    sortedList = list()
    todo = []

    for vertex in self.graph:
      if not self.isReferenced(vertex):
        todo.append(vertex)
      else:
        count[vertex] = 0
    
    for vertex in self.referenced:
      count[vertex] = 0
  
    while todo:
      vertex = todo.pop()
      sortedList.append(vertex)
      if vertex in self.graph:
        for dst in self.graph[vertex]:
          count[dst] += 1
          if count[dst] == self.references[dst]:
            todo.append(dst)
    
    return sortedList

  # Applies transitive reduction to practically generate a hasse diagram
  # which can then be used to derive an order.
  def reduction(self):
    src_todo = []

    for vertex in self.graph:
      if not self.isReferenced(vertex):
        src_todo.append(vertex)

    while src_todo:
      src = src_todo.pop()
      toRemove = set()
      for src_ch in self.graph[src]:
        if src_ch not in self.graph: continue
        dst_todo = [src_ch]
        while dst_todo:
          dst = dst_todo.pop()
          for dst_ch in self.graph[dst]:
            if dst_ch in self.graph[src]:
              toRemove.add(dst_ch)
            if dst_ch in self.graph:
              dst_todo.append(dst_ch)
        if src_ch in self.graph:
          src_todo.append(src_ch)
      for tr in toRemove:
        self.graph[src].remove(tr)
        self.references[tr] -= 1

  def show(self, name):
    addedNodes = []
    dot = Digraph(format='png')
    for src,dsts in self.graph.items():
      if src not in addedNodes:
        dot.node(str(src), str(src))
      addedNodes.append(src)
      for dst in dsts:
        if dst not in addedNodes:
          dot.node(str(dst), str(dst))
          addedNodes.append(dst)
        dot.edge(str(src), str(dst))
    dot.render(name, cleanup=True)

def test():
  a = 'a'
  b = 'b'
  c = 'c'
  d = 'd'
  e = 'e'
  f = 'f'

  ttg = TreeTopoGraph()
  ttg.addEdge(a, b)
  ttg.addEdge(a, c)
  ttg.addEdge(a, d)
  ttg.addEdge(a, e)
  ttg.addEdge(b, c)
  ttg.addEdge(b, d)
  ttg.addEdge(b, e)
  ttg.addEdge(c, d)
  ttg.addEdge(c, e)
  ttg.addEdge(d, e)
  ########
  # ttg.addEdge(a,b)
  # ttg.addEdge(a,f)
  # ttg.addEdge(a,c)
  # ttg.addEdge(b,c)
  # ttg.addEdge(c,f)
  # ttg.addEdge(a,d)
  # ttg.addEdge(d,e)
  # ttg.addEdge(e,f)
  ########
  ttg.show('before')
  ttg.reduction()
  ttg.show('after')
  lst = ttg.topologicalSort()
  for l in lst:
    print(l)



if __name__ == "__main__":
  test()