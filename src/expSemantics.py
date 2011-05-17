from pretty import ppExp
import util
import symbol
import env
import judge


class ExpBase(symbol.Base):
  def __init__(self, ast):
    self.ast = ast
    self.repr = self

  def shortString(self):
    return ""
  
  def longString(self):
    return str(self.__class__) + " " + self.shortString()
  
  def type(self, symbols):
    return symbol.Errtype(symbols)
    
  def names(self):
    return []
    
  def ids(self):
    return []
    
  def vars(self):
    return []
    
  def eval(self, env, symbols):
    return "Oops!"
    
  def evalSubst(self, env, symbols):
    return "Oops!"
    
  def subst(self, new, old, env, symbols):
    raise Exception("subst not defined on: " + str(self))
    
  def isSuperType(self, other, symbols, infer = False):
    m = self.type(symbols).isSuperType(other, symbols, infer)
    if m:
      m.update(other, self)
    return m
    
  def fv(self, var, env):
    raise Exception("fv not defined on: " + str(self))
    
  def dom(self, envr, symbols):
    return None
    
  def subsumes(self, other, symbols):
    return False
 
class FunApp(ExpBase):
  def __init__(self, ast):
    ExpBase.__init__(self, ast)
    self.typeVarRes = dict()
    
  def isSuperType(self, other, symbols, infer = False):
    if isinstance(other, FunApp):
      if len(self.args) != len(other.args):
        return None
        
      result = symbol.SeqMatch(None)
      for m in map(lambda (s,o): s.isSuperType(o, symbols, infer), [(self.fun, other.fun)] + zip(self.args, other.args)):
        if m:
          result.addMatch(m)
        else:
          return None
      return result
    
    return ExpBase.isSuperType(self, other, symbols, infer)
  
  def shortString(self):
    return self.fun.shortString() + "((" + ";".join(map(lambda x: x.shortString(), self.args)) + "))"
    
  def substMatch(self, ms):
    result = FunApp(None)
    result.fun = self.fun.substMatch(ms)
    result.args = map(lambda x: x.substMatch(ms), self.args)
    if hasattr(self, "funInfo"):
      result.funInfo = self.funInfo
    return result
    
  def subsumes(self, other, symbols):
    if not isinstance(other, FunApp):
      return False
    return self.fun.subsumes(other.fun, symbols) and reduce(lambda x,y: x and y, map(lambda (s,o): s.subsumes(o, symbols), zip(self.args, other.args)), True)
  
  def type(self, symbols):
    t = reduce(lambda x,y: x or y, map(lambda x: self.typeHelper(x, symbols), self.fun.type(symbols).superClasses()), None)

    if t:
      t = t.rhs
      #type variables
      for v in self.typeVarRes:
        t = t.replace(v, self.typeVarRes[v])
      return t
    else:
      return symbol.ErrType()
    
    
  def typeHelper(self, ft, symbols):
    if isinstance(ft, symbol.FunType):
      return ft
    if isinstance(ft, symbol.Seq) and len(ft.syntax) == 1:
      return self.typeHelper(ft.syntax[0])
    ss = reduce(lambda x,y: x or y, map(lambda s: s if s != ft and self.typeHelper(s, symbols) else None, ft.superClasses()), None)
    if ss:
      return ss
      
    for s in symbols:
      if ft != s and ft.isSuperType(s,symbols):
        t = self.typeHelper(s, symbols)
        if t:
          return t      
    return None
    
    
  def names(self):
    return self.fun.names() + sum(map(lambda x: x.names(), self.args), [])
    
  def ids(self):
    return self.fun.ids() + sum(map(lambda x: x.ids(), self.args), [])
    
  def vars(self):
    return self.fun.vars() + sum(map(lambda x: x.vars(), self.args), [])
 
 
  def eval(self, env, symbols):
    leq = [self.fun]
    req = map(lambda x: [x], self.args)
    env.envClosure(leq)
    map(lambda x: env.envClosure(x), req)
    rc = self.combinations(req)
    for l in leq:
      for r in rc:
        result = self.evalHelper(env, symbols, l, r)
        if result:
          return result
        
    return "undefined"
  
  #returns a list of combinations from a list of lists
  #e.g., given [[a,b], [1,2,3]] you will get [[a,1],[a,2],[a,3],[b,1],[b,2],[b,3]]
  def combinations(self, aa):
    if not aa:
      return [[]]
    result = []
    for a in aa[0]:
      tails = self.combinations(aa[1:])
      result.extend(map(lambda x: [a] + x, tails))
    return result
  
  #what does this method do?
  def evalHelper(self, env, symbols, lhs, rhss):
    rhss = map(lambda r: r.eval(env, symbols), rhss)
    
    if isinstance(lhs, judge.FunDef): #the function is a user defined or built-in function
      return lhs.eval(env, symbols, rhss)
    elif len(rhss) == 1: #it's only worth looking for a mapping if there is only one argument to use (we don't support mappings from tuples)
    #print map(lambda x: x.shortString(), self.fun.type(symbols).superClasses())
      lhs = lhs.eval(env, symbols)
      if hasattr(self, "funInfo"):
        sym = self.funInfo
        #find a function type for the function part of the funapp
        t = reduce(lambda x,y: x or y, map(lambda x: self.typeHelper(x, symbols), self.fun.type(symbols).superClasses()), None)
        if t:
          left = t.lhs
          right = t.rhs
          
          left = left[0]

          #if the fun in the fun app is a concat or single element of a mapping, then we will try to match the rhs to one of the mapping elements
          els = [lhs]
          if hasattr(lhs, "elements"):
            els = lhs.elements
          
          for e in els:
            for c in sym.cases:
              m = e.isSuperType(c.type(symbols), symbols)
              if m:
                l = symbol.List(None)
                l.arg = left
                mm = m.match(l)
                if mm == rhss[0]:
                  l.arg = right
                  return m.match(l)       
            
    return None
    

  def evalSubst(self, env, symbols):
    result = FunApp(None)
    result.fun = self.fun.evalSubst(env, symbols)
    result.args = map(lambda x: x.evalSubst(env, symbols), self.args)
    return result
    
  def subst(self, new, old, env, symbols):
    result = FunApp(None)
    result.fun = self.fun.subst(new, old, env, symbols)
    result.args = map(lambda x: x.subst(new, old, env, symbols), self.args)
    return result

  def fv(self, kind, env):
    result = Union(None)
    result.elements = [self.fun.fv(kind, env)]
    result.elements.extend(map(lambda x: x.fv(kind, env), self.args))
    return result  
  
    
class Subst(ExpBase):
  def __init__(self, ast):
    ExpBase.__init__(self, ast)

    
  def subsumes(self, other, symbols):
    if not isinstance(other, Subst):
      return False
    return self.lhs.subsumes(other.lhs, symbols) and self.body.subsumes(other.body, symbols) and self.rhs == other.rhs

  def substMatch(self, ms):
    result = Subst(None)
    result.lhs = self.lhs.substMatch(ms)
    result.rhs = self.rhs.substMatch(ms)
    result.body = self.body.substMatch(ms)
    return result
    
  def type(self, symbols):
    envt = env.Env()
    lt = self.lhs.type(envt)
    rt = self.rhs.type(envt)
    llt = symbol.List(None)
    llt.arg = lt
    lrt = symbol.List(None)
    lrt.arg = rt
    #this is a bit of a hack, what we really want to do is subst at all levels of list nesting, but we only do one depth here because only one depth is supported in constraints etc.
    return self.body.type(symbols).subst(lt, rt, envt, symbols).subst(llt, lrt, envt, symbols)
    
  def names(self):
    return self.lhs.names() + self.rhs.names() + self.body.names()
    
  def ids(self):
    return self.lhs.ids() + self.rhs.ids() + self.body.ids()
    
  def vars(self):
    return self.lhs.vars() + self.rhs.vars() + self.body.vars()
    
  def evalSubst(self, env, symbols):
    return self.eval(env, symbols)
  
  def eval(self, env, symbols):
    return self.body.eval(env, symbols).subst(self.lhs.eval(env, symbols), self.rhs.eval(env, symbols), env, symbols)

  def subst(self, new, old, env, symbols):
    result = Subst(None)
    result.rhs = self.rhs
    if self.rhs.shortString() == old.shortString():
      result.body = self.body
      result.lhs = self.lhs.subst(new, old, env, symbols)
    else:
      newnew = new.subst(env.fresh(), self.old, env, symbols)
      result.body = self.body.subst(newnew, old, env, symbols)
      result.lhs = self.lhs.subst(newnew, old, env, symbols)
    
    return result
    
  def shortString(self):
    return "{" + self.lhs.shortString() + "/" + self.rhs.shortString() + "}" + self.body.shortString()
    
  def fv(self, kind, env):
    result = Union(None)
    result.addElement(self.lhs.fv(kind, env))
    r = SetSub(None)
    r.lhs = self.body.fv(kind, env)
    r.rhs = self.body.fv(kind, env)
    result.addElement(r)
    return result
    

class Concat(ExpBase):
  def __init__(self, ast):
    ExpBase.__init__(self, ast)
    self.elements = []
    
    
  def substMatch(self, ms):
    result = Concat(None)
    result.elements = map(lambda x: x.substMatch(ms), self.elements)
    result.typeF = self.typeF
    return result
    
  def subsumes(self, other, symbols):
    if not isinstance(other, Concat) or not len(self.elements) == len(other.elements):
      return False
    return reduce(lambda x,y: x and y, map(lambda (s,o): s.subsumes(o, symbols), zip(self.elements, other.elements)), True)
    
  def type(self, symbols):
    return self.typeF
    
  def names(self):
    return sum(map(lambda x: x.names(), self.elements), [])
    
  def ids(self):
    return sum(map(lambda x: x.ids(), self.elements), [])
    
  def vars(self):
    return sum(map(lambda x: x.vars(), self.elements), [])
    
  def eval(self, env, symbols):
    result = Concat(None)
    result.elements = map(lambda x: x.eval(env, symbols), self.elements)
    result.typeF = self.typeF
    return result
    
  def shortString(self):
    if not self.elements:
      return "[]"
    return ",".join(map(lambda x: x.shortString(), self.elements))

  def isSuperType(self, other, symbols, infer = False):
    if isinstance(other, Concat) and len(self.elements) == len(other.elements):
      ms = map(lambda (s,o): s.isSuperType(o, symbols, infer), zip(self.elements, other.elements))
      if not None in ms:
        result = symbol.SeqMatch(None)
        result.matches = ms
        return result
      
    m = self.type(symbols).isSuperType(other, symbols, infer)
    if m:
      m2 = self.concatMatch(map(lambda x: x.isSuperType(other, symbols, infer), self.elements))
      if m2:
        return m2
      else:
        return symbol.IdMatch(other, self)
      
    return None
  
  def concatMatch(self, ms):
    if not ms:
      return None
    if reduce(lambda x,y: x and y, map(lambda x: isinstance(x, symbol.IdMatch), ms), True):
      resCat = Concat(None)
      resCat.elements = map(lambda x: x.other, ms)
      resCat.typeF = ms[0].id
      return symbol.IdMatch(ms[0].id, resCat)
    if reduce(lambda x,y: x and y, map(lambda x: isinstance(x, symbol.SeqMatch), ms), True):
      print ms
      result = symbol.SeqMatch(ms[0].seq)
      for i in range(len(ms[0].matches)):
        result.addMatch(self.concatMatch(map(lambda x: x.matches[i], ms)))
      return result
      
    return None
  
    
  def evalSubst(self, env, symbols):
    result = Concat(None)
    result.elements = map(lambda x: x.evalSubst(env, symbols), self.elements)
    types = map(lambda x: x.type(symbols), result.elements)
    result.typeF = util.maxListType(types, symbols)
    return result    
  
  def subst(self, new, old, env, symbols):
    result = Concat(None)
    result.elements = map(lambda x: x.subst(new, old, env, symbols), self.elements)
    types = map(lambda x: x.type(symbols), result.elements)
    result.typeF = util.maxListType(types, symbols)
    return result    

  def fv(self, kind, env):
    result = Union(None)
    result.elements = map(lambda x: x.fv(kind, env), self.elements)
    return result

  def dom(self, envr, symbols):
    for sym in symbols:
      for case in sym.cases:
        m = self.isSuperType(case, symbols)
        #print self, case, m
        if m and sym.maps:
          l = symbol.List(None)
          l.arg = sym.maps[0]
          mm = m.match(l)
          if mm:
            return mm
            
    result = Concat(None)
    result.elements = map(lambda x: x.dom(envr, symbols), self.elements)
    result.typeF = util.maxListType(map(lambda x: x.type(symbols), result.elements), symbols)
    return result
    
    
    
    
class Elipses(symbol.BottomType,symbol.TopType,ExpBase):    
  def __init__(self, ast):
    ExpBase.__init__(self, ast)
    
    
  def substMatch(self, ms):
    return self
    
  def subsumes(self, other, symbols):
    return True
    
  def type(self, symbols):
    return self
    
    
  def evalSubst(self, env, symbols):
    return self
    
  def eval(self, env, symbols):
    return self
    
  def shortString(self):
    return "..."

  def subst(self, new, old, env, symbols):
    return self
    
  def fv(self, kind, env):
    result = Concat(None)
    result.elements.append(Empty(None))
    return result

  
    
    
    
class Subscript(ExpBase):
  def __init__(self, ast):
    ExpBase.__init__(self, ast)
    
  def substMatch(self, ms):
    result = Subscript(None)
    result.lhs = self.lhs.substMatch(ms)
    result.rhs = self.rhs.substMatch(ms)
    return result

    
  def subsumes(self, other, symbols):
    if not isinstance(other, Subscript):
      return False
    return self.lhs.subsumes(other.lhs, symbols) and self.rhs == other.rhs

  def type(self, symbols):
    return self.lhs.type(symbols)
    
  def names(self):
    return self.lhs.names() + self.rhs.names()
    
  def ids(self):
    return self.lhs.ids() + self.rhs.ids()
    
  def vars(self):
    return map(lambda x: symbol.listFromExp(x, None, x), self.lhs.vars()) + self.rhs.vars()
 
  def eval(self, env, symbols):
    result = Subscript(None)
    result.lhs = self.lhs.eval(env, symbols)
    result.rhs = self.rhs.eval(env, symbols)
    l = symbol.List(None)
    l.arg = result.lhs
    leq = [l]
    req = [result.rhs]
    env.envClosure(leq)
    env.envClosure(req)
    for r in req:
      if isinstance(r, Num):
        for l in leq:
          if isinstance(l, Concat):
            if r.val < len(l.elements):
              return l.elements[r.val]
            else:
              return "subscript out of range"
    #TODO subscripts into constraints                    
      
    return result
    
  def shortString(self):
    return self.lhs.shortString() + "_" + self.rhs.shortString()
    
  def evalSubst(self, env, symbols):
    result = Subscript(None)
    result.lhs = self.lhs.evalSubst(env, symbols)
    result.rhs = self.rhs.evalSubst(env, symbols)
    return result
    
  def subst(self, new, old, env, symbols):
    result = Subscript(None)
    result.lhs = self.lhs.subst(new, old, env, symbols)
    result.rhs = self.rhs.subst(new, old, env, symbols)
    return result
 
  def fv(self, kind, env):
    result = Union(None)
    result.elements.addElement(self.lhs.fv(kind, env))
    result.elements.addElement(self.rhs.fv(kind, env))
    return result

class Predicate(ExpBase):
  def __init__(self, ast):
    ExpBase.__init__(self, ast)
    self.rhs = None

  def substMatch(self, ms):
    result = self.__class__(None)
    result.rhs = self.rhs.substMatch(ms)
    return result
    
  def subsumes(self, other, symbols):
    if not isinstance(other, self.__class__):
      return False
    return self.rhs.subsumes(other.rhs, symbols)
    
  def type(self, symbols):
    return symbol.TopType()
  
  def evalSubst(env, symbols):
    result = self.__class__(None)
    result.rhs = self.rhs.evalSubst(env, symbols)
    return result
  
  def subst(self, new, old, env, symbols):
    result = self.__class__(None)
    result.rhs = self.rhs.subst(new, old, env, symbols)
    return result
    
  def fv(self, kind, env):
    return []
    
class FunOK(Predicate):    
  def __init__(self, ast):
    Predicate.__init__(self, ast)
    
  def shortString(self):
    return "fun((" + self.rhs.shortString() + "))"
        
  def eval(self, env, symbols):
    #TODO
    return True    
    
    
    
class BoolLit(ExpBase):
  def __init__(self, ast, val):
    ExpBase.__init__(self, ast)
    self.val = val

  def substMatch(self, ms):
    return self
    
  def subsumes(self, other, symbols):
    if self.val == False:
      return True
    if not isinstance(other, BoolLit):
      return False
    return self.val == other.val
    
    
  def type(self, symbols):
    return symbol.TopType()
  
  def eval(self, env, symbols):
    return self.val
    
  def shortString(self):
    return str(self.val)

  def evalSubst(env, symbols):
    return self
    
  def subst(self, new, old, env, symbols):
    return self
    
  def fv(self, kind, env):
    result = Concat(None)
    result.elements.append(Empty(None))
    return result

TRUE = BoolLit(None, True)
FALSE = BoolLit(None, False)

class ScopeOp(ExpBase):
  def __init__(self, ast):
    ExpBase.__init__(self, ast)
    rhs = None
    qVars = []
    
  def rename(self, old, new):
    result = self.__class__(None)
    result.rhs = rhs
    result.qVars = self.qVars
    for (o, n) in zip(old, new):
      if o in result.qVars:
        result.qVars[result.qVars.index(o)] = n
        result.rhs = result.rhs.substMatch([symbol.IdMatch(o, n)])
    return result
    
  def substMatch(self, ms):
    result = self.__class__(None)
    result.qVars = self.qVars
    ms2 = map(lambda x: x.remove(qVars), ms)
    result.rhs = self.rhs.substMatch(ms2)
    return result
    
  def subsumes(self, other, symbols):
    if not isinstance(other, self.__class__) or not len(self.qVars) == len(other.qVars):
      return False
    rnOther = other.rename(other.qVars, self.qVars)
    return self.rhs.subsumes(rnOther.rhs, symbols)
    
  def evalSubst(env, symbols):
    result = self.__class__(None)
    result.qVars = self.qVars
    result.rhs = map(lambda x: x.evalSubst(new, old), self.rhs)
    return result
    
  def subst(self, new, old, env, symbols):
    if old in qVars:
      return self
    result = self.__class__(None)
    result.qVars = self.qVars
    result.rhs = map(lambda x: x.subst(new, old, env, symbols), self.rhs)
    return result
    
  def names(self):
    return sum(map(lambda x: x.names(), self.qVars), []) + self.rhs.names()
    
  def ids(self):
    return sum(map(lambda x: x.ids(), self.qVars), []) + self.rhs.ids()
    
  def vars(self):
    return sum(map(lambda x: x.vars(), self.qVars), []) + self.rhs.vars()

  def fv(self, kind, env):
    result = SetSub(None)
    result.lhs = self.rhs.fv(kind, env)
    result.rhs = Concat(None)
    result.rhs.elements = self.qVars
    return result

  def type(self, symbols):
    return symbol.TopType()

class Exists(ScopeOp):    
  def __init__(self, ast):
    ScopeOp.__init__(self, ast)
    
  def shortString(self):
    return "exists " + ",".join(map(lambda x: x.shortString(), self.qVars)) + " . " + self.rhs.shortString()
    
  def eval(self, env, symbols):
    return self

class Forall(ScopeOp):    
  def __init__(self, ast):
    ScopeOp.__init__(self, ast)
    
  def shortString(self):
    return "forall " + ",".join(map(lambda x: x.shortString(), self.qVars)) + " . " + self.rhs.shortString()
    
  def eval(self, env, symbols):
    return self

    
class ManyOp(ExpBase):
  def __init__(self, ast):
    ExpBase.__init__(self, ast)
    self.elements = []
    
  def substMatch(self, ms):
    result = self.__class__(None)
    result.elements = map(lambda x: x.substMatch(ms), self.elements)
    return result
    
  def subsumes(self, other, symbols):
    if not isinstance(other, self.__class__) or not len(self.elements) == len(other.elements):
      return False
    return reduce(lambda x,y: x and y, map(lambda (s,o): s.subsumes(o, symbols), zip(self.elements, other.elements)), True)
    
  def evalSubst(env, symbols):
    result = self.__class__(None)
    result.elements = map(lambda x: x.evalSubst(env, symbols), self.elements)
    return result
    
  def subst(self, new, old, env, symbols):
    result = self.__class__(None)
    result.elements = map(lambda x: x.subst(new, old, env, symbols), self.elements)
    return result
    
  def names(self):
    return sum(map(lambda x: x.names(), self.elements), [])
    
  def ids(self):
    return sum(map(lambda x: x.ids(), self.elements), [])
    
  def vars(self):
    return sum(map(lambda x: x.vars(), self.elements), [])

  def fv(self, kind, env):
    result = self.__class__(None)
    result.elements = map(lambda x: x.fv(kind, env), self.elements)
    return result
    
class Union(ManyOp):
  def __init__(self, ast):
    ManyOp.__init__(self, ast)
    
  def addElement(self, e):
    if e not in self.elements:
      self.elements.append(e)
      
  def addElementNorm(self, e):
    if isinstance(e, Empty):
      return
    if isinstance(e, Concat) and (not e.elements or len(e.elements) == 1 and isinstance(e.elements[1], Empty)):
      return
    if isinstance(e, Union):
      map(lambda x: self.addElementNorm(x), e.elements)
      return
    if e not in self.elements:
      self.elements.append(e)
    
  def shortString(self):
    if not self.elements:
      return "[]"
    return " \/ ".join(map(lambda x: x.shortString(), self.elements))

  def type(self, symbols):
    return util.maxListType(self.elements, symbols) 
    
  def eval(self, env, symbols):
    result = Union(None)
    syntax = map(lambda x: x.eval(env, elements), self.syntax)
    cat = symbol.Concat(None)
    for s in syntax:
      if isinstance(s, symbol.Concat):
        cat.elements.extend(s.elements)
      else:
        result.elements.append(s)
        
    if cat.elements:
      cat.elements = set(cat.elements)
      if not result.elements:
        return cat
      else:
        result.elements.append(cat)
    return result
    

class BinOp(ExpBase):    
  def __init(self, ast):
    ExpBase.__init__(self, ast)
    self.lhs = None
    self.rhs = None
    
  def substMatch(self, ms):
    result = self.__class__(None)
    result.lhs = self.lhs.substMatch(ms)
    result.rhs = self.rhs.substMatch(ms)
    return result
    
  def subsumes(self, other, symbols):
    if not isinstance(other, self.__class__):
      return False
    return self.lhs.subsumes(other.lhs, symbols) and self.rhs.subsumes(other.rhs, symbols)
    
  def evalSubst(self, env, symbols):
    result = self.__class__(None)
    result.lhs = self.lhs.evalSubst(env, symbols)
    result.rhs = self.rhs.evalSubst(env, symbols)
    return result
    
    
  def subst(self, new, old, env, symbols):
    result = self.__class__(None)
    result.lhs = self.lhs.subst(new, old, env, symbols)
    result.rhs = self.rhs.subst(new, old, env, symbols)
    return result
    
  def names(self):
    return self.lhs.names() + self.rhs.names()
    
  def ids(self):
    return self.lhs.ids() + self.rhs.ids()
    
  def vars(self):
    return self.lhs.vars() + self.rhs.vars()

  def fv(self, kind, env):
    result = self.__class__(None)
    result.lhs = self.lhs.fv(kind, env)
    result.rhs = self.rhs.fv(kind, env)
    return result
    
    
    
class SetSub(BinOp):
  def __init(self, ast):
    BinOp.__init__(self, ast)
        
  def shortString(self):
    return "(" + self.lhs.shortString() + " - " + self.rhs.shortString() + ")"

  def type(self, symbols):
    return util.maxListType([self.lhs, self.rhs], symbols) 
    
  def eval(self, env, symbols):
    result = SetSub(None)
    result.lhs = self.lhs.eval(env, symbols)
    result.rhs = self.rhs.eval(env, symbols)
    
    if isinstance(result.lhs, Concat) and isinstance(result.rhs, Concat):
      rr = Concat(None)
      for e in result.lhs.elements:
        if not e in result.rhs.elements:
          rr.elements.append(e)
      return rr
    else:
      if result.lhs == result.rhs:
        return Concat(None)
      if isinstance(result.lhs, Concat) and isinstance(result.rhs, Id):
        rr = Concat(None)
        for e in result.lhs.elements:
          if not e == result.rhs:
            rr.elements.append(e)
        return rr
      return result
    
       
  def names(self):
    return self.lhs.names()
    
  def ids(self):
    return self.lhs.ids()
    
  def vars(self):
    return self.lhs.vars()
    
    
class Implies(BinOp):
  def __init(self, ast):
    BinOp.__init__(self, ast)
        
  def shortString(self):
    return "(" + self.lhs.shortString() + " => " + self.rhs.shortString() + ")"

  def type(self, symbols):
    return symbol.TopType()
    
  def eval(self, env, symbols):
    result = self.Implies(None)
    result.lhs = self.lhs.eval(env, symbols)
    result.rhs = self.rhs.eval(env, symbols)
    return result

    
class And(ManyOp):
  def __init(self, ast):
    ManyOp.__init__(self, ast)
        
  def shortString(self):
    return "(" + " /\ ".join(map(lambda x: x.shortString(), self.elements)) + ")"

  def type(self, symbols):
    return symbol.TopType()
    
  def eval(self, env, symbols):
    return reduce(lambda x,y: x and y, map(lambda x: x.eval(env, symbols), self.elements), True)
    
    
class Or(ManyOp):
  def __init(self, ast):
    ManyOp.__init__(self, ast)
        
  def shortString(self):
    return "(" + " \/ ".join(map(lambda x: x.shortString(), self.elements)) + ")"

  def type(self, symbols):
    return symbol.TopType()
    
  def eval(self, env, symbols):
    if not self.elements:
      return True
    return reduce(lambda x,y: x or y, map(lambda x: x.eval(env, symbols), self.elements), False)
    
 
class FV(ExpBase):
  def __init__(self, kind, arg, ast):
    ExpBase.__init__(self, ast)
    self.kind = kind
    self.arg = arg

  def substMatch(self, ms):
    result = Subst(None)
    result.kind = self.kind
    result.arg = self.arg.substMatch(ms)
    return result
    
    
  def subsumes(self, other, symbols):
    #TODO what if other is a FunApp and the lhs is fv? And vice versa
    #if isinstance(other, FunApp):
    #  if isinstance(other.lhs, judge.FVFun):
    #    return 
    
    if not isinstance(other, FV):
      return False
    return self.arg.subsumes(other.arg, symbols) and self.kind == other.kind
    
  def shortString(self):
    return "fv(" + self.kind.shortString() + ", " + self.arg.shortString() + ")"

  def type(self, symbols):
    return symbol.SetType(self.kind)
    
  def eval(self, env, symbols):
    return self.arg.fv(self.kind, env)
    
  def evalSubst(self, env, symbols):
    result = FV(self.kind, self.arg.evalSubst(env, symbols), None)
    return result
  
  def subst(self, new, old, env, symbols):
    #[e/x]fv(e') = fv(e) \/ fv(e')/x
    result = Union(None)
    result.addElement(FV(self.kind, new, None))
    result.addElement(SetSub(None))
    result.elements[1].lhs = self
    result.elements[1].rhs = old    
    return result
    
  def names(self):
    return self.arg.names()
    
  def ids(self):
    return self.arg.ids()
    
  def vars(self):
    return self.arg.vars()
    
  def fv(self, kind, env):
    if self.kind == kind:
      return self
    else:
      result = Concat(None)
      result.elements.append(Empty(None))
      return result
    
 
class Dom(ExpBase):
  def __init__(self, arg, type):
    ExpBase.__init__(self, None)
    self.arg = arg
    self.typeF = type
    
  def substMatch(self, ms):
    result = Subst(None)
    result.arg = self.arg.substMatch(ms)
    result.typeF = self.typeF
    return result

  def subsumes(self, other, symbols):
    #TODO what if other is a FunApp and the lhs is dom?
    if not isinstance(other, Dom):
      return False
    return self.arg.subsumes(other.arg, symbols)
    
  def shortString(self):
    return "dom(" + self.arg.shortString() + ")"

  def type(self, symbols):
    return symbol.SetType(self.typeF)
    
  def eval(self, env, symbols):
    return self.arg.dom(env, symbols)
    
  def evalSubst(self, env, symbols):
    result = Dom(self.arg.evalSubst(env, symbols), self.typeF)
    return result
    
  def subst(self, new, old, env, symbols):
    return self
    
  def names(self):
    return self.arg.names()
    
  def ids(self):
    return self.arg.ids()
    
  def vars(self):
    return self.arg.vars()
    
  def fv(self, kind, env):
    result = FV(kind, self, None)
    return result
    
    
    
    
class Num(ExpBase):
  def __init__(self, ast):
    ExpBase.__init__(self, ast)

  def substMatch(self, ms):
    return self
    
  def subsumes(self, other, symbols):
    if not isinstance(other, Num):
      return False
    return self.val == other.val
    
  def type(self, symbols):
    return symbol.IndexType()
  
    
  def eval(self, env, symbols):
    return self
    
  def shortString(self):
    return str(self.val)

  def evalSubst(self, env, symbols):
    return self
    
  def subst(self, new, old, env, symbols):
    return self
    
  def fv(self, kind, env):
    result = Concat(None)
    result.elements.append(Empty(None))
    return result
    
    
class IndexVar(ExpBase):
  def __init__(self, ast):
    ExpBase.__init__(self, ast)
    self.name = ""
    
  def substMatch(self, ms):
    return self

  def subsumes(self, other, symbols):
    if not isinstance(other, IndexVa):
      return False
    return self.name == other.name
    
  def type(self, symbols):
    return symbol.IndexType()
    
  def names(self):
    return [self.name]
    
  def ids(self):
    return [self.name]
    
  def vars(self):
    return [self]
    
  def shortString(self):
    return self.name
  
    
  def eval(self, env, symbols):
    return self
    
  def evalSubst(self, env, symbols):
    return self
    
  def subst(self, new, old, env, symbols):
    return self
    
  def fv(self, kind, env):
    result = Concat(None)
    result.elements.append(self)
    return result

  
class Empty(ExpBase):
  def __init__(self, ast):
    ExpBase.__init__(self, ast)

  def subsumes(self, other, symbols):
    return isinstance(other, Empty)  
    
  def substMatch(self, ms):
    return self
    
  def type(self, symbols):
    return self
    
  def shortString(self):
    return ""
    
  def longString(self):
    return "Empty"
    
  def isSuperType(self, other, infer = False):
    if isinstance(other, Empty):
      return True

    return None
    
  def eval(self, env, symbols):
    return self

  def evalSubst(self, env, symbols):
    return self
    
  def subst(self, new, old, env, symbols):
    return self

  def fv(self, kind, env):
    result = Concat(None)
    result.elements.append(Empty(None))
    return result


