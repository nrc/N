

class Base:
  def shortString(self):
    return ""

  def __eq__(self, other):
    if not isinstance(other, Base):
      return False
    return self.shortString() == other.shortString()
    
  def __ne__(self, other):
    if not isinstance(other, Base):
      return True
    return self.shortString() != other.shortString()
    
  def __hash__(self):
    return self.shortString().__hash__()
    
  def __str__(self):
    return self.shortString()
    
  def __repr__(self):
    return "<" + self.shortString() + ">"

    
class Type(Base):
  def shortString(self):
    return ""

  #symbols |- self <: other
  def isSuperType(self, other, symbols=[], infer = False):
    return None
    
  def superClasses(self, symbols = [], acc = -1):
    if acc == -1:
      acc = []
    acc.append(self)
    return acc
    
  def longString(self):
    return self.shortString()
    
  def replace(self, old, new):
    return self

    
    
class BottomType(Type):
  def __init__(self):
    self.repr = self
 
  def isSuperType(self, other, symbols=[], infer = False):
    return IdMatch(other, self)
    
  def shortString(self):
    return "_Bottom"
  
  
  def superClasses(self, symbols = [], acc = []):
    return symbols + [self]

class TopType(Type):
  def isSuperType(self, other, symbols=[], infer = False):
    return IdMatch(other, self) if self == other else None
    
  def shortString(self):
    return "_Top"


from pretty import ppExp
import env
import judge
import util

from expSemantics import Elipses
from expSemantics import Empty
from expSemantics import Subst
from expSemantics import Concat
from expSemantics import Union
from expSemantics import FV
from expSemantics import SetSub
from expSemantics import Dom

    
    

class Symbol(Type):
  def __init__(self, ast):
    self.ast = ast
    self.cases = []
    self.variable = None
    self.maps = None
    self.supertypes = []
    self.globe = False
    self.dvCache = -1
    self.repr = self
    
  def addNames(self, names):
    self.names = [(n.val, n) for n in names]
    self.name = names[0].val
    
  def substMatch(self, ms):
    for m in ms:
      mm = m.match(self)
      if mm:
        return mm
      
    return self
    
    
  def type(self, symbols):
    return self
    
  def shortString(self):
    return self.name
    
  def longString(self):
    return "Symbol " + self.name

    
    
  def setName(self, name):
    self.names = [(name, None)]
    self.name = name
    
  def addCase(self, c):
    self.cases.append(c)
    
  def matches(self, syntax, symbols=[], infer = False):
    if isinstance(syntax, Type):
      if syntax.isSuperType(self, [], infer):
        return IdMatch(self, syntax)    
  
    if hasattr(syntax, "symbol"):
      if syntax.symbol.isSuperType(self, infer = infer):
        return IdMatch(self, syntax)

    for c in self.cases:
      m = syntax.type(symbols).isSuperType(c.type(symbols), symbols, infer)
      if m:
        return IdMatch(self, syntax)
        
    return None
    

  #true if self <: other    
  def isSuperType(self, other, symbols=[], infer = False):
    if isinstance(other, TopType):
      return IdMatch(other, self)

    if other in self.superClasses(symbols, []):
      return IdMatch(other, self)
    
    if isinstance(other, Seq) and len(other.syntax) == 1 and self.isSuperType(other.syntax[0], infer = infer):
      return IdMatch(other.syntax[0], self)

    #if we are comparing with a list try promoting self to a List of self
    if isinstance(other, List):
      promo = List(None)
      promo.arg = self
      promo.repr = self
      m = promo.isSuperType(other, symbols, infer)
      if m:
        m.update(other, self)
        return m
      
    if isinstance(other, Id):
      m = self.isSuperType(other.symbol, symbols, infer)
      if m:
        m.switchIn(other.symbol, other)
        return m

    if not isinstance(other, Symbol):
      for s in self.superClasses(symbols, []):
        if not isinstance(s, Symbol):
          m2 = s.isSuperType(other, symbols, infer)
          if m2:
            result = IdMatch(other, self)
            result.trans = [IdMatch(s, self)] + m2.trans
            return result
    
    if infer and isinstance(other, TypeVar):
      return IdMatch(other, self)
      
    if self.cases and reduce(lambda x,y: x and y, map(lambda c: c.isSuperType(other, []), self.cases), True):
      return IdMatch(other, self)

    return None
  
  
  #compute transitive superclasses
  def superClasses(self, symbols = [], acc = -1):
    if acc == -1:
      acc = []
    acc.append(self)
    for s in self.supertypes:
      if s not in acc:
        acc.extend(s.superClasses(symbols, acc))
    return set(acc)
    
    
  def isInteresting(self):
    if self.globe:
      return False
      
    if not self.ast:
      return False
      
    if self.ast.subtype == "terminal":
      if self.ast.semantic or self.ast.label: return True
      else: return False
    
    return True
    
  def ids(self):
    return [self.name]
    
  def vars(self):
    return [self]
  
  def evalSubst(self, env, symbols):
    return self
    
  def subst(self, new, old, env, symbols):
    if self == old:
      #check bindings
      if old in env.boundVars(self):
        return self
      else:
        return new
    else:
      return self
      
  def fv(self, kind, envr):
    if self == kind and not envr.boundVars(self):
      return self
    else:
      return Concat(None)
      
  def dom(self, envr, symbols):
    if self.maps:
      return Dom(self, self.maps[0])
    return None
      
      
  def deepVars(self, binders = []):
    if self.dvCache == -1:
      self.dvCache = []
      if self.cases:
        self.cases.sort(lambda x,y: len(x.syntax) - len(y.syntax))
        for c in self.cases:
          self.dvCache.extend(c.deepVars(binders))
      else:
        if self.variable:
          self.dvCache = [self]
        else:
          self.dvCache = []
          
    return self.dvCache
        
  def orderByLength(self, cases):
    result = []
    

    
class Seq(Type):
  def __init__(self, ast):
    self.ast = ast
    self.typeCache = None
    self.syntax = []
    #self.superTypes = []
    self.case = None
    self.caseMatch = None
    self.repr = self
        
  def replace(self, old, new):
    result = Seq(self.ast)
    result.syntax = map(lambda x: x.replace(old, new), self.syntax)
    result.case = self.case
    result.caseMatch = self.caseMatch
    result.repr = self.repr
    return result

    
  def subsumes(self, other, symbols):
    if not isinstance(other, Seq) or not len(self.syntax) == len(other.syntax):
      return False
    return reduce(lambda x,y: x and y, map(lambda (s,o): s.subsumes(o, symbols), zip(self.syntax, other.syntax)), True)
    
  def names(self):
    return sum(map(lambda x: x.names(), self.syntax), [])
    
  def ids(self):
    return sum(map(lambda x: x.ids(), self.syntax), [])
    
  def vars(self):
    return sum(map(lambda x: x.vars(), self.syntax), [])
    
  def type(self, symbols):
    if not self.typeCache:
      self.typeCache = Seq(None)
      self.typeCache.syntax = map(lambda x: x.type(symbols), self.syntax)
      self.typeCache.case = self.case
      self.typeCache.caseMatch = self.caseMatch
    return self.typeCache
    
  # self <: other
  def isSuperType(self, other, symbols=[], infer = False):
    if isinstance(other, TopType):
      return IdMatch(other, self)

      
    if isinstance(other, Seq): #and len(self.syntax) == len(other.syntax):
#      return reduce(lambda x,y: x and y, map(lambda (x,y): x.isSuperType(y, symbols), zip(self.syntax, other.syntax)), True)

      result = []
      sIndex = 0
      last = None
      for o in other.syntax:
        if sIndex >= len(self.syntax):
          if isinstance(last, Elipses):
            cur = last
          else:
            result = None
            break
        else:
          cur = self.syntax[sIndex]
                  
                  
        m = cur.isSuperType(o, symbols, infer)
        #print sIndex, cur.longString(), o.longString(), m
        if not m:
          if isinstance(last, Elipses):
            sIndex -= 1
            result.append(IdMatch(o, last))
            cur = last
          else:
            result = []
            break
        else:
          result.append(m)
        sIndex += 1
        last = cur

      if result and sIndex >= len(self.syntax):
        m = SeqMatch(other)
        for r in result:
          m.addMatch(r)
        return m
        
    if len(self.syntax) == 1:
      m = self.syntax[0].isSuperType(other, symbols, infer)
      if m:
        return m      

    if isinstance(other, Symbol) and other in symbols and other.matches(self, symbols):
      return IdMatch(other, self)
    if infer and isinstance(other, TypeVar):
      for s in symbols:
        if s.matches(self, symbols) and s.isSuperType(other, symbols, infer):
          return IdMatch(other, s)
      
    if isinstance(other, Id):
      m = self.isSuperType(other.symbol, symbols, infer)
      if m:
        m.switchIn(other.symbol, other)
        return m

    #a nested syntax
    if hasattr(other, "syntax") and len(other.syntax) == 1:
      m = self.isSuperType(other.syntax[0], symbols, infer)
      if m:
        return m

    #if we are comparing with a list try promoting self to a List of self
    #try promoting to a list
    #if isinstance(other, List):
    if isinstance(other, (List,Symbol,FunType)):
      promo = List(None)
      promo.arg = self
      promo.repr = self
      promo.promo = True
      m = promo.isSuperType(other, symbols, infer)
      if m:
        if isinstance(other, List) and isinstance(other.arg, Seq) and len(other.arg.syntax) == len(self.syntax):
          for i in range(len(other.arg.syntax)):
            l = List(None)
            l.arg = other.arg.syntax[i]
            m.update(l, self.syntax[i])
        else:
          m.update(other, self)
        return m

    #print "fail", symbols
    #print ",".join(map(lambda x: str(x), symbols))
    return None

  def shortString(self):
    return " ".join(map(lambda x: x.shortString(), self.syntax))
  
  def longString(self):
    return "Seq (" + " ".join(map(lambda x: x.longString(), self.syntax)) + ")"
    
  def eval(self, env, symbols):
    result = Seq(None)
    result.syntax = map(lambda x: x.eval(env, symbols), self.syntax)
    return result
    
    
  def calcBindings(self, s):
    binder = []  #binding elements of the current element
    bound = dict()  #a mapping from an element to the variables bound in that element
    for b in self.case.bindings:
      #print s, b, self.caseMatch.idMatch(b[0])
      bbb = self.caseMatch.repMatch(b[0])
      for ss in s.vars():
        if isinstance(bbb, Concat):
          for bbbb in bbb.elements:
            if ss.repr is bbbb.repr:
              binder.append(ss)
        elif ss.repr is bbb.repr:
          binder.append(ss)
      if not binder:
        def addBoundVarToBound(be):
          if be not in bound:
            bound[be] = []
          if isinstance(bbb, Concat):
            bound[be].extend(bbb.elements)
          else:
            bound[be].append(bbb)
            
        for bb in b[1:]:
          for ss in s.vars():
            br = self.caseMatch.repMatch(bb).repr
                
            if ss.repr is br:
              addBoundVarToBound(ss)
            elif isinstance(br, Concat):
              for be in br.elements:
                if ss.repr is be:
                  addBoundVarToBound(ss)
              
          if s.repr is self.caseMatch.repMatch(bb).repr:
            addBoundVarToBound(s)
            
    return binder, bound

    
  def evalSubst(self, env, symbols):
    result = Seq(None)
    result.syntax = map(lambda x: x.evalSubst(env, symbols), self.syntax)
    return result
    
  def subst(self, new, old, envr, symbols):
    result = Seq(None)
    if self.case and self.case.bindings:
      unknown = 0
      for s in self.syntax:
        binder, bound = self.calcBindings(s)

        if binder: #the element is a binder
          trip = False
          for b in binder:
            if b.repr is s.repr:
              result.syntax.append(s)
              trip = True
          if not trip:
            #take account of known binders in the env (complicated in lists, I think)
            newEnvr = env.Env(envr)
            bindings = dict()
            for b in binder:
              bindings[b] = binder
            newEnvr.addBindings(bindings, binder)
            result.syntax.append(s.subst(new, old, newEnvr, symbols))
        elif s in bound: #the element is bound over
          if envr.provesEqOrIn(old, bound[s]):   #the subst is overridden by the binding
            result.syntax.append(s)
          elif envr.provesNEqOrIn(old, bound[s]):  #we can prove that the subst is not overridden by any of the bindings
            result.syntax.append(s.subst(new, old, envr, symbols))
          else:   #unknown one way or the other
            result.syntax.append(s)
            unknown += 1
        else: #no top level binding issues
          #check for unknowness
          for b in bound:
            if not (envr.provesEqOrIn(old, bound[b]) or envr.provesNEqOrIn(old, bound[b])):
              unknown += 1
            
          if unknown:
            result.syntax.append(s)
          else:  
            newEnvr = env.Env(envr)
            bindings = dict()
            for b in binder:
              bindings[s] = binder
            bindings.update(bound)
            newEnvr.addBindings(bindings, binder)
            result.syntax.append(s.subst(new, old, newEnvr, symbols))
        
      #If we can't do any better, then just leave a syntactic subsititution
      if unknown:
        result = Subst(None)
        result.lhs = new
        result.rhs = old
        result.body = self
    else:
      #no bindings so go through the elements of the sequence substing each one
      #print self.shortString()
      result.syntax = map(lambda x: x.subst(new, old, envr, symbols), self.syntax)
      
    return result
    
  def substMatch(self, ms):
    for m in ms:
      if hasattr(m, "id") and self == m.id:
        return m.other
  
    result = Seq(None)
    result.syntax = map(lambda x: x.substMatch(ms), self.syntax)
    return result

    
  def fv(self, kind, envr):
    result = Union(None)
    if self.case and self.case.bindings:
      
      for s in self.syntax:
        binder, bound = self.calcBindings(s)

        if binder: #the element is a binder
          trip = False
          for b in binder:
            if b.repr is s.repr:
              #do nothing the whole element is a binding variable
              trip = True
          if not trip:
            #take account of known binders in the env 
            newEnvr = env.Env(envr)
            bindings = dict()
            for b in binder:
              bindings[b] = binder
            newEnvr.addBindings(bindings, binder)
            result.addElementNorm(s.fv(kind, newEnvr))
        else: #not a binder (might have bound vars, but deal with them lower down)
          newEnvr = env.Env(envr)
          bindings = dict()
          for b in binder:
            bindings[s] = binder
          bindings.update(bound)
          newEnvr.addBindings(bindings, binder)
          result.addElementNorm(s.fv(kind, newEnvr))
        
    else:
      #no bindings so go through the elements of the sequence
      map(lambda x: result.addElementNorm(x.fv(kind, envr)), self.syntax)

    return result

  def dom(self, envr, symbols):
    promo = List(None)
    promo.arg = self
    promo.repr = self
    result = promo.dom(envr, symbols)
    if isinstance(result, List):
      return result.arg
    else:
      return expSemantics.Dom(self, result.type(symbols))

    
#one case of a symbol/production
class Case(Seq):
  def __init__(self, parent, ast):
    Seq.__init__(self, ast)
    self.parent = parent
    self.bindings = []
    self.dvCache = -1
    
  def addElement(self, sym):
    self.syntax.append(sym)
    
  def deepVars(self, binders = -1):
    if binders == -1:
      binders = []
    binders.extend(map(lambda x: x[0], self.bindings))

    if self.dvCache == -1:
      self.dvCache = self.dvHelper(self, binders)
    return self.dvCache
    
  def dvHelper(self, s, binders):  
    if isinstance(s, Id):
      if s in binders:
        return []
      else:
        return s.symbol.deepVars(binders)
    if isinstance(s, List):
      nb = []
      for b in binders:
        if isinstance(b, List):
          nb.append(b.arg)
      return self.dvHelper(s.arg, nb)
    if isinstance(s, Seq):
      return sum(map(lambda ss: self.dvHelper(ss, binders), s.syntax), [])

    return []

    
  
class List(Type):
  def __init__(self, ast):
    self.ast = ast
    self.typeCache = None
    self.repr = self
    self.promo = False

  def replace(self, old, new):
    result = List(self.ast)
    result.repr = self.repr
    result.arg = self.arg.replace(old, new)
    return result
    
  def subsumes(self, other, symbols):
    if not isinstance(other, List):
      return False
    return self.arg.subsumes(other.arg, symbols)

  
  def evalSubst(self, env, symbols):
    result = List(None)
    result.arg = self.arg.evalSubst(env, symbols)
    return result
    
  def names(self):
    return map(lambda y: "[" + y + "]", self.arg.names())
    
  def ids(self):
    return map(lambda y: "[" + y + "]", self.arg.ids())
    
  def type(self, symbols):
    if not self.typeCache:
      self.typeCache = List(None)
      self.typeCache.arg = self.arg.type(symbols)
    return self.typeCache
    
  
  def isSuperType(self, other, symbols=[], infer = False):
    if isinstance(other, Elipses):
      return IdMatch(other, self)

    if isinstance(other, List):
      if isinstance(self.arg, Empty):
        im = IdMatch(other.arg, self.arg)
        return im.makeListMatch()
      else:
        m = self.arg.isSuperType(other.arg, symbols, infer) 
        if m:
          return m.makeListMatch()
        else:
          return None

    if isinstance(other, Seq) and len(other.syntax) == 1:
      m = self.isSuperType(other.syntax[0], symbols, infer)
      if m:
        return m
        
    if isinstance(other, Symbol) and other in symbols and other.matches(self):
      return IdMatch(other, self)
    for s in symbols:
      m1 = s.matches(self)
      if m1:
        m2 = s.isSuperType(other, symbols, infer)
        if m2:
          result = IdMatch(other, self)
          result.trans = m1.trans + m2.trans
          return result
      
    if isinstance(other, Id):
      m = self.isSuperType(other.symbol, symbols, infer)
      if m:
        m.switchIn(other.symbol, other)
        return m
  
    if not self.promo:
      promo = List(None)
      promo.arg = other
      promo.repr = other
      promo.promo = True
      m = self.isSuperType(promo, symbols, infer)
      if m:
        m.switchIn(promo, other)
        return m
  
    return None 
 
  def shortString(self):
    return "[" + self.arg.shortString() + "]"

  def longString(self):
    return "List [" + self.arg.longString() + "]"
    
  def names(self):
    return map(lambda x: "[" + str(x) + "]", self.arg.names())
    
  def ids(self):
    return map(lambda x: "[" + str(x) + "]", self.arg.ids())

  def vars(self):
    return map(lambda x: listFromExp(x, None, x), self.arg.vars())
    
  def eval(self, env, symbols):
    result = List(None)
    result.arg = self.arg.eval(env, symbols)
    return result
    
  def substMatch(self, ms):
    for m in ms:
      mm = m.match(self)
      if mm:
        return mm
        
    newM = []
    for m in sum(map(lambda m: m.flatMatches(), ms), []):
      if isinstance(m.id, List) and isinstance(m.other, List):
        newM.append(IdMatch(m.id.arg, m.other.arg))
    
    if newM:
      result = List(None)
      result.arg = self.arg.substMatch(newM)
      return result
    else:
      return self
    
  def subst(self, new, old, envr, symbols):
    if isinstance(old, List):
      result = List(None)
      result.arg = self.arg.subst(new.arg, old.arg, envr, symbols)
      return result
    else:
      #check for not in constraints
      cnstr = judge.InTest(None)
      cnstr.nt = True
      cnstr.lhs = old
      cnstr.rhs = self
      if envr.proves(cnstr):
        return self

      def dvHelper(x):
        #take into account bound vars
        xeq = [x]
        envr.envClosure(xeq)
        if reduce(lambda x,y: x or y, map(lambda x: envr.isBoundVar(x), xeq), False):
          return []
        if isinstance(x, Id):
          return x.symbol.deepVars()
        elif isinstance(x, List):
          return dvHelper(x.arg)
        return []
        
      dv = sum(map(dvHelper, self.vars()), [])
      sym = old if isinstance(old, Symbol) else old.symbol
      if not envr.provesIn(sym, dv):
        return self
      result = Subst(None)
      result.body = self
      result.lhs = new
      result.rhs = old
      return result
    
  def fv(self, kind, env):
    fva = self.arg.fv(kind, env.deListifyBindings())
          
    return listify(fva)

  def dom(self, envr, symbols):
    for s in symbols:
      if s.maps:
        for c in s.cases:
          m = self.isSuperType(c, symbols)
          if m:
            l = List(None)
            l.arg = s.maps[0]
            return m.match(l)
          
    return None

    
def listFromExp(exp, ast, repr):
  result = List(ast)
  result.arg = exp
  result.repr = repr
  return result
  
def listify(x):
  if isinstance(x, FV):
    x.arg = listify(x.arg)
    return x
  if isinstance(x, Id) or isinstance(x, List):
    return listFromExp(x, None, x.repr)
  if isinstance(x, Union) or isinstance(x, Concat):
    x.elements = map(listify, x.elements)
    return x
  if isinstance(x, SetSub):
    x.lhs = listify(x.lhs)
    return x
  
  
  print "Internal error, cannot handle: " + x.longString() + " in listify"
  
"""
class Cons:
  def __init__(self, arg):
    self.arg = arg
    self.typeCache = None
    self.ast = arg.ast
    
  def type(self, symbols):
    if not self.typeCache:
      self.typeCache = List(None)
      self.typeCache.arg = self.arg.type(symbols)
    return self.typeCache
    
  def shortString(self):
    return "_List(" + self.arg.shortString() + ")"
    
  def longString(self):
    return "Cons (" + self.arg.longString() + ")"
    
  def names(self):
    return map(lambda x: "[" + str(x) + "]", self.arg.names())
    
  def ids(self):
    return map(lambda x: "[" + str(x) + "]", self.arg.ids())

  def vars(self):
    return map(lambda x: listFromExp(x), self.arg.vars())
    
  def eval(self, env, symbols):
    result = List(None)
    result.arg = self.arg.eval(env, symbols)
    return result
"""

    


    

class Id(Base):
  def __init__(self, ast, symbol):
    self.symbol = symbol
    if ast:
      self.ast = ast
      self.name = ast.val
      self.mod = ast.mod
    else:
      self.ast = None
      self.name = symbol.name
      self.mod = ""
    self.repr = self
    
  
  def evalSubst(self, env, symbols):
    return self
    
  def subsumes(self, other, symbols):
    if not isinstance(other, Id):
      return False
    return self == other
    
    
  def type(self, symbols):
    return self.symbol   
    
  def substMatch(self, ms):
    for m in ms:
      mm = m.match(self)
      if mm:
        return mm
      
    return self
    
  def names(self):
    return [self.name]
    
  def ids(self):
    return [self.name + self.mod]
    
  def shortString(self):
    return self.name + self.mod
    
  def vars(self):
    return [self]
    
  def longString(self):
    return "Id: " + self.name + self.mod
    
  def eval(self, env, symbols):
    return self
    
  def isSuperType(self, other, symbols, infer = False):
    m = self.symbol.isSuperType(other, symbols, infer)
    if m:
      m.update(other, self)
    return m
    
  def subst(self, new, old, env, symbols):
    if env.isBoundVar(self):
      return self
      
    if env.provesIn(old, env.boundVars(self)):
      return self

    if env.provesEq(self, old):
      return new
      
    sym = old
    if isinstance(old, Id):
      sym = old.symbol

    if self.symbol == sym and env.provesNE(self, old):
      return self
      
    if not env.provesIn(sym, self.symbol.deepVars()):
      return self
      
    result = Subst(None)
    result.body = self
    result.lhs = new
    result.rhs = old
    return result
    
  def fv(self, kind, env):
    if env.isBoundVar(self):
      return Concat(None)
      
    def simpleType(x):
      if isinstance(x, Id):
        return x.symbol
      if isinstance(x, List):
        return simpleType(x.arg)
      return None
      
    if kind in map(lambda x: simpleType(x), env.boundVars(self)):
      result = SetSub(None)
      result.lhs = FV(kind, self, None)
      result.rhs = Concat(None)
      result.rhs.elements = set(env.boundVars(self))
      return result
      
    if kind not in self.symbol.deepVars():
      return Concat(None)

    if self.symbol == kind:
      return self    

    return FV(kind, self, None)
    
  def dom(self, envr, symbols):
    pos = [self]
    envr.envClosure(pos)
    backup = None
    for p in pos:
      result = None
      if isinstance(p, Id):
        result = p.symbol.dom(envr, symbols)
        if result:
          result.arg = self
      else:
        result = p.dom(envr, symbols)
      if result:
        if isinstance(result, Dom):
          backup = result
        else:
          return result
          
    return backup
    
    
class FreshId(Id):
  def __init__(self, sym, num):
    self.symbol = sym
    self.mod = num
    self.ast = None
    self.name = sym.shortString()
    self.repr = self
    
  def shortString(self):
    return "_" + self.name + str(self.mod)

  def longString(self):
    return "Fresh Id: " + self.shortString()
  
  
class ErrSym(Base):
  def __init__(self):
    self.lhs = self
    self.rhs = self
    self.name = "Err"
    self.names = ["Err"]
    self.mod = ""
    self.val = "Err"
    self.ast = None
    self.repr = self
    self.globe = False
    
  def type(self, symbols):
    return ErrType()
    
  def shortString(self):
    return "_Err"
    
    
  def eval(self, env, symbols):
    return self
    
  def vars(self):
    return []
    
  def isSuperType(self, other, symbols=[], infer = False):
    return IdMatch(other, self)
    
  def subst(self, new, old, env, symbols):
    return self
  
  def evalSubst(self, env, symbols):
    return self
    
  def fv(self, kind, env):
    return Concat(None)
    
  def dom(self, envr, symbols):
    return None
    
  def isInteresting(self):
    return False
    
class FunType(Type):
  def __init__(self, lhs, rhs, vars = []):
    self.lhs = lhs
    self.rhs = rhs
    self.vars = vars
    

  def replace(self, old, new):
    if old in self.vars:
      return self  
    return FunType(map(lambda x: x.replace(old, new), self.lhs), self.rhs.replace(old, new), self.vars)
    
  def isSuperType(self, other, symbols=[], infer = False):
    if self == other:
      return IdMatch(other, self)
      
    if not isinstance(other, FunType):
      return False
      
    #don't need to handle type vars, because only built in functions have type variables (I think)

    result = SeqMatch(other)
    rm = other.rhs.isSuperType(self.rhs, symbols, infer)
    if rm:
      result.addMatch(rm.reverse())
    else:
      return None
    for (x,y) in zip(self.lhs, other.lhs):
      rm = x.isSuperType(y, symbols, infer)
      if rm:
        result.addMatch(rm)
      else:
        return None
    return result
  
  def shortString(self):
    return ",".join(map(lambda x: x.shortString(), self.vars)) + "." + "; ".join(map(lambda x: x.shortString(), self.lhs)) + "-->" + self.rhs.shortString()
  
  
  def longString(self):
    return "Fun: " + ",".join(map(lambda x: x.longString(), self.vars)) + "." + "; ".join(map(lambda x: x.longString(), self.lhs)) + "-->" + self.rhs.longString()
  
    
    
class TypeVar(Type):
  def __init__(self, label):
    self.label = label
    
  def isSuperType(self, other, symbols=[], infer = False):
    if self == other:
      return IdMatch(other, self)
    
    if infer:
      return IdMatch(other, self)
    
    return None
    
    
  def shortString(self):
    return self.label
    
  def longString(self):
    return "TypeVar " + self.label
    

  def replace(self, old, new):
    if self == old:
      return new
    return self
    
    
    
class IndexType(Type):    
  def isSuperType(self, other, symbols=[], infer = False):
    if isinstance(other, IndexType):
      return IdMatch(other, self)
      
    return False
    
    
  def shortString(self):
    return "_Index"
    
    
    
    
class SetType(Type):
  def __init__(self, type):
    self.arg = type
    
  def isSuperType(self, other, symbols=[], infer = False):
    if self == other:
      return IdMatch(other, self)
      
    if not hasattr(other, "arg"):
      return False
      
    m = self.arg.isSuperType(other.arg, symbols, infer)
    if m:
      return m.makeListMatch(SetType)
    else:
      return None

    
  def shortString(self):
    return "set(" + self.arg.shortString() + ")"  
  

  def replace(self, old, new):
    return SetType(self.arg.replace(old, new))
  

    
  
  


    
class ErrType(BottomType):
  def __init__(self):
    self.lhs = self
    self.rhs = self
    self.repr = self

  def type(self, symbols):
    return self
       
  def shortString(self):
    return "_Error"
  
  
  def superClasses(self, symbols = [], acc = []):
    return Type.superClasses(self, symbols, acc)
    
    
    
    
class Match(Base):
  def match(self, x):
    return None
    
  def backMatch(self, x):
    return []
    
  def repMatch(self, x):
    return None
    
  def repBackMatch(self, x):
    return []
    
  def shortString(self):
    return "Some match"
    
  def flatMatches(self):
    return []
  
class IdMatch(Match):
  def __init__(self, id, other):
    self.id = id
    self.other = other
    self.trans = [self]
    
  def remove(self, ids):
    if id in ids:
      return IdMatch(None, None)
    else:
      return self
    
  def reverse(self):
    result = IdMatch(self.other, self.id)
    if self.trans != [self]:
      result.trans = map(lambda x: x.reverse(), self.trans)
      result.trans.reverse()
    return result
    
  def flatMatches(self):
    return [self]

  def match(self, x):
    if self.id == x:
      return self.other
      
    return None
    
  def backMatch(self, x):
    if self.other == x:
      return [self.id]
      
    return []
    
  def repMatch(self, x):
    if self.id.repr is x.repr:
      return self.other
      
    return None
    
  def repBackMatch(self, x):
    if self.other.repr is x.repr:
      return [self.id]
      
    return []
    
  def shortString(self):
    return self.id.shortString() + " --> " + self.other.shortString()
    
  def longString(self):
    return "IdMatch: " + self.id.shortString() + " --> " + self.other.shortString()
    
  def makeListMatch(self, cls = List):
    li = cls(None)
    li.arg = self.id
    li.repr = self.id.repr
    lo = cls(None)
    lo.arg = self.other
    lo.repr = self.other.repr
    return IdMatch(li, lo)

  def deList(self):
    return IdMatch(self.id.arg, self.other.arg)
    
  def update(self, id, other):
    if self.id == id:
      self.other = other
    
  def switchIn(self, id, new):
    if self.id == id:
      self.id = new
      
  def substMatch(self, m):
    self.other = self.other.substMatch(m)
      
  def dom(self):
    return [self.id]
      
  def range(self):
    return [self.other]


"""    
class PromoMatch(IdMatch):
  def __init__(self, m):
    self.arg = m.deList()

  def shortString(self):
    return self.id.shortString() + " --> " + "p[" + self.other.shortString() + "]"
    
  def match(self, x):
    if isinstance(x, List):
      return self.arg.match(x.arg)
    return None

  def makeListMatch(self):
    li = List(None)
    li.arg = self.id
    lo = List(None)
    lo.arg = self.other
    return PromoMatch(li, lo)
    
  def deList(self):
    if isinstance(self.other, List):
      return PromoMatch(self.id.arg, self.other.arg)
    else:
      return IdMatch(self.id.arg, self.other)

  def update(self, id, other):
    return self
    
    
   
class DemoMatch(Match):
  def __init__(self, m):
    self.arg = m.deList()

  def shortString(self):
    return "d[" + self.arg.shortString() + "]"

  def makeListMatch(self):
    return PromoMatch(self.arg.makeListMatch())
    
  def deList(self):
    return self.arg

  def update(self, id, other):
    return self
"""
  
class SeqMatch(Match):
  def __init__(self, seq):
    self.matches = []
    self.seq = seq
    self.trans = [self]
    
  def remove(self, ids):
    if self.seq in ids:
      return SeqMatch(None)
    result = SeqMatch(seq)
    result.matches = map(lambda x: x.remove(ids), self.matches)
    return result
      
    
  def match(self, x):
    return reduce(lambda x,y: x or y, map(lambda y: y.match(x), self.matches), None)
    
  def reverse(self):
    result = SeqMatch(None)
    result.matches = map(lambda x: x.reverse(), self.matches)
    if self.trans != [self]:
      result.trans = map(lambda x: x.reverse(), self.trans)
      result.trans.reverse()
    return result
    
  def backMatch(self, x):
    return sum(map(lambda y: y.backMatch(x), self.matches), [])
    
  def repMatch(self, x):
    return reduce(lambda x,y: x or y, map(lambda y: y.repMatch(x), self.matches), None)
    
  def repBackMatch(self, x):
    return sum(map(lambda y: y.repBackMatch(x), self.matches), [])
      
  def addMatch(self, m):
    if not isinstance(m, Match):
      print m
      raise Exception
    self.matches.append(m)
    
  def addIdMatch(self, id, other):
    self.matches.append(IdMatch(id, other))
    
  def shortString(self):
    return "(" + ", ".join(map(lambda x: x.shortString(), self.matches)) + ")"
    
  def longString(self):
    return "SeqMatch(" + ", ".join(map(lambda x: x.longString(), self.matches)) + ")"
  
  def makeListMatch(self, cls = List):
    lSeq = cls(None)
    lSeq.arg = self.seq
    result = SeqMatch(lSeq)
    result.matches = map(lambda x: x.makeListMatch(cls), self.matches)
    return result

  def deList(self):
    result = SeqMatch()
    result.matches = map(lambda x: x.deList(), self.matches)
    return result
    
  def update(self, id, other):
    if self.seq == id:
      self.matches = [IdMatch(id, other)]
    for m in self.matches:
      m.update(id, other)   
    
  def switchIn(self, id, new):
    for m in self.matches:
      m.switchIn(id, new)    
      
  def substMatch(self, m):
    for mm in self.matches:
      mm.substMatch(m)    
      
  def flatMatches(self):
    return sum(map(lambda x: x.flatMatches(), self.matches), [])
    
  def dom(self):
    return sum(map(lambda x: x.dom(), self.matches), [])
    
  def range(self):
    return sum(map(lambda x: x.range(), self.matches), [])
    
"""  
class ListMatch(Match):
  def __init__(self, m):
    self.arg = m
    
  def match(self, x):
    if isinstance(x, List):
      return List(self.arg.match(x.arg))
    return None
  
  def shortString(self):
    return "[" + self.arg.shortString() + "]"
"""    
    

 