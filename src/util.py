#TODO - 
#isListType


#utility class, provides a number of semantic functions on a world
import symbol
import env
import ast
import judge
import expSemantics


def interestingRoot(var):
  if isinstance(var, symbol.Id):
    return var.symbol.isInteresting()
  if isinstance(var, symbol.Symbol):
    return var.isInteresting()
  if isinstance(var, symbol.List):
    return interestingRoot(var.arg)
  #if isinstance(var, expSemantics.IndexVar):
  #  return True
  return True
    
def isAtomic(var):
  if isinstance(var, symbol.Id) or isinstance(var, symbol.Symbol):
    return True
  if isinstance(var, symbol.List):
    return isAtomic(var.arg)
  return False
  
def atomicType(var, symbols):
  type = var.type(symbols)
  if isAtomic(type):
    return type
  if isinstance(type, symbol.Seq):
    #find a supertype
    for s in symbols:
      if type.isSuperType(s, symbols):
        return s
  if isinstance(type, symbol.List):
    result = symbol.List(None)
    result.arg = atomicType(type.arg)
    return result
    
  raise Exception("Cannot find atomic supertype of " + type.shortString())


def maxListType(types, symbols):
  result = symbol.BottomType()
  for t in types:
    if t.isSuperType(result, symbols):
      continue
    elif result.isSuperType(t, symbols):
      result = t
      if not isListType(result, symbols):
        temp = result
        result = symbol.List(None)
        result.arg = temp
    else:
      raise Exception("Internal error, no common supertype of types: " + ", ".join(map(lambda x: x.shortString(), types)))
  return result
  
def maxType(types, symbols):
  result = symbol.BottomType()
  for t in types:
    if t.isSuperType(result, symbols):
      continue
    elif result.isSuperType(t, symbols):
      result = t
    else:
      raise Exception("Internal error, no common supertype of types: " + ", ".join(map(lambda x: x.shortString(), types)))
  return result  
  

def isFunType(t, symbols):
  if isinstance(t, symbol.Id):
    return isFunType(t.symbol, symbols)
    
  if isinstance(t, symbol.FunType):
    return t
    
  if isinstance(t, symbol.Seq) and len(t.syntax) == 1:
    return self.isFunType(t.syntax[0], symbols)
  
  ss = reduce(lambda x,y: x or y, map(lambda s: s if s != t and isFunType(s, symbols) else None, t.superClasses()), None)
  if ss:
    return ss
    
  for s in symbols:
    if s != t and t.isSuperType(s, symbols):
      ss = isFunType(s, symbols)
      if ss:
        return ss
      
  return None
 
  
  
def isListType(t, symbols, seen = []):
  if t in seen:
    return None
    
  if isinstance(t, symbol.List) or isinstance(t, symbol.SetType):
    return t
    
  if isinstance(t, symbol.Symbol):
    flag = reduce(lambda x,y: x and y, map(lambda x: isListType(x.syntax[0].type(symbols), symbols, []) if len(x.syntax) == 1 else False, t.cases), True)
    if flag and len(t.cases) > 0:
      #TODO
      return t
    return None
    
  if isinstance(t, symbol.Seq) and len(t.syntax) == 1:
    return self.isListType(t.syntax[0], symbols)
  
  sup = t.superClasses()
  sup.remove(t)
  return reduce(lambda x,y: x or y, map(lambda s: isListType(s, symbols, seen+[t]), sup), None)  
  

def fv(var, symbols):
  result = FVTable(var)
  for s in symbols:
    for c in s.cases:
      cc = idClone(c, symbols)
      cc.case = c
      cc.caseMatch = cc.isSuperType(c, symbols)
      result.addCase(s, cc, cc.fv(var, env.Env()))
    
    
  return result
  
def idClone(c, symbols):
  if isinstance(c, symbol.Id):
    return c
  if isinstance(c, symbol.Id):
    ast = ast.Ast(ast.ID)
    ast.val = c.name
    ast.mod = ""
    result = symbol.Id(ast, c)
    return result
  if isinstance(c, symbol.Case):
    result = symbol.Seq(None)
    result.case = c
    result.caseMatch = result.isSuperType(c.type(symbols), symbols)
    for s in c.syntax:
      result.syntax.append(idClone(s, symbols))
    return result
  if isinstance(c, symbol.Seq):
    result = symbol.Seq(None)
    result.case = c.case
    result.caseMatch = c.caseMatch
    for s in c.syntax:
      result.syntax.append(idClone(s, symbols))
    return result
  if isinstance(c, symbol.List):
    result = symbol.List(None)
    result.arg = idClone(c.arg, symbols)
    return result
    
  return c
  
def subst(var, symbols):
  st = SubstTable(var)
  for s in symbols:
    for c in s.cases:
      if var in c.deepVars():
        cc = renameForFresh(c, var.variable)
        cc.case = c
        cc.caseMatch = cc.isSuperType(c, symbols)
        vs = varInBinding(var, c.bindings)
        if vs:
          for b in vs:
            e = env.Env()
            cnstr = judge.InTest(None)
            cnstr.nt = False
            cnstr.lhs = var
            cnstr.rhs = b[0]
            e[var] = cnstr
            st.addCase(s, cc, cc.subst(var.variable, var, e, symbols), "where " + str(var) + " in " + str(b[0]))
            cnstr.nt = True
            st.addCase(s, cc, cc.subst(var.variable, var, e, symbols), "where " + str(var) + " not in " + str(b[0]))
        else:
          st.addCase(s, cc, cc.subst(var.variable, var, env.Env(), symbols))
      if var == c:
        fast = ast.Ast(ast.ID, None)
        fast.val = var.name
        fast.mod = "'"
        fresh = symbol.Id(fast, c.parent)
        fresh.repr = None
        st.addCase(s, fresh, fresh)
        
  return st

  
#assumes old is a symbol, should make this work for ids and Lists of ids/symbols at some point
def renameForFresh(s, old):
  ids = s.ids()
  if old.shortString() not in ids:
    return s

  fast = ast.Ast(ast.ID, None)
  fast.val = old.name
  fast.mod = ""
  new = symbol.Id(fast, old)
  new.repr = s.repr
  while new.shortString() in ids:  
    new.mod += "'"
  
  return rename(s, old, new)
  
def rename(s, old, new):
  if isinstance(s, symbol.Id):
    if s == old:
      return new
    else:
      return s
  elif isinstance(s, symbol.List):
    if isinstance(old, symbol.List):
      result = symbol.List(None)
      result.arg = rename(s.arg, old.arg, new.arg)
      result.repr = s.repr
      return result
    else:
      return s
  elif isinstance(s, symbol.Seq):
    result = symbol.Seq(None)
    result.syntax = map(lambda x: rename(x, old, new), s.syntax)
    result.repr = s.repr
    return result
  
  print "Internal error, could not handle " + str(s) + " in rename."
  return s
  
def varInBinding(var, bindings):
  result = []
  for b in bindings:
    if varMayBoundBy(var, b[0]):
      result.append(b)
  return result  
  
def varMayBoundBy(var, binder):
  if var == binder:
    return True
  if isinstance(binder, symbol.List):
    return varMayBoundBy(var, binder.arg)
  if isinstance(binder, symbol.Id) and var == binder.symbol:
    return True
  return False

  
  

class SubstTable:
  def __init__(self, var):
    self.var = var
    self.cases = dict()
    
  def addCase(self, symbol, lhs, rhs, desc = ""):
    if symbol not in self.cases:
      self.cases[symbol] = []
    self.cases[symbol].append((lhs, rhs, desc))
    
  def shortString(self):
    result = "Substitution for " + self.var.name + ":"
    substStr = self.var.variable.shortString() + "/" + self.var.name
    for s in self.cases:
      result += "\n[" + substStr + "] " +  s.name + ":"
      for (l,r,d) in self.cases[s]:
        result += "\n  {" + substStr + "} " + l.shortString() + "  =  " + r.shortString()
        if d:
          result += " (" + d + ")"
    return result
  
class FVTable:
  def __init__(self, var):
    self.var = var
    self.cases = dict()
    
  def addCase(self, symbol, lhs, rhs, desc = ""):
    if symbol not in self.cases:
      self.cases[symbol] = []
    self.cases[symbol].append((lhs, rhs, desc))
    
  def shortString(self):
    result = "Free variables for " + self.var.name + ":"
    preStr = "fv(" + self.var.name + "; "
    postStr = ")"
    for s in self.cases:
      result += "\n" + preStr + s.name + postStr + ":"
      for (l,r,d) in self.cases[s]:
        result += "\n  " + preStr + l.shortString() + postStr + "  =  " + r.shortString()
        if d:
          result += " (" + d + ")"
    return result
  

  
    
    
class StringFileAdapter:
  def __init__(self, s):
    self.s = s
    self.closed = False
    
  def next(self):
    if not self.s:
      raise StopIteration
    result = self.s
    self.s = ""
    return result
    
  def close(self):
    self.closed = True

    