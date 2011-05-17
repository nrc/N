import symbol
import expSemantics



class JudgeDef:
  def __init__(self, ast):
    self.asts = [ast]
    self.cases = []
    
    
class FunDef:
  def __init__(self, ast):
    self.ast = ast
    
  def substMatch(self, ms):
    return self
    
  def type(self, symbols):
    return None
  
  def eval(self, envr, symbols, args):
    return None
    
  def isSuperType(self, other, symbols, infer=False):
    if other.__class__.__name__ == self.__class__.__name__:
      return symbol.IdMatch(other, self)
    else:
      return None

class FvFun(FunDef):
  def __init__(self):
    FunDef.__init__(self, None)
    self.name = "fv"
    
  #assumes args have already been evaluated
  def eval(self, envr, symbols, args):
    kind = args[0].symbol
    return args[1].fv(kind, envr)
    
  def type(self, symbols):
    x = symbol.TypeVar("ExpType")
    y = symbol.TypeVar("VarType")
    return symbol.FunType([y, x], symbol.SetType(y), [x, y])
    
  def shortString(self):
    return "fv"
    
  def vars(self):
    return []
    
    
class DomFun(FunDef):
  def __init__(self):
    FunDef.__init__(self, None)
    self.name = "dom"
    
  def type(self, symbols):
    l = symbol.TypeVar("L")
    r = symbol.TypeVar("R")
    return symbol.FunType([symbol.FunType([l], r, [])], symbol.SetType(l), [l, r])
    
  def eval(self, envr, symbols, args):
    return args[0].dom(envr, symbols)
    
  def shortString(self):
    return "dom"
    
  def vars(self):
    return []
    
    
class JCase:
  def __init__(self, ast):
    self.ast = ast
    self.premises = []
    
    
  def shortString(self):
    result = ""
    result += self.parent.name + " "
    result += "; ".join(map(lambda x: x.shortString(), self.envs))
    result += " |- "
    result += "; ".join(map(lambda x: x.shortString(), self.args))
    return result
    
  def getConclusions(self):
    conc = Judge(None)
    conc.args = self.args
    conc.envs = self.envs
    conc.nt = False
    conc.defn = self.parent
    return [conc]
    
class Equality(symbol.Base):
  def __init__(self, ast):
    self.ast = ast
    
  def isSuperType(self, other, symbols):
    if not isinstance(other, Equality):
      return None
    if self.nt != other.nt:
      return None
      
    m = self.istHelper(other, symbols)
    if m:
      return m
    self.lhs, self.rhs = self.rhs, self.lhs
    m = self.istHelper(other, symbols)
    self.lhs, self.rhs = self.rhs, self.lhs
    return m
    
  def istHelper(self, other, symbols):
    m1 = self.lhs.isSuperType(other.lhs, symbols)
    m2 = self.rhs.isSuperType(other.rhs, symbols)
    if m1 and m2:
      result = symbol.SeqMatch(None)
      result.addMatch(m1)
      result.addMatch(m2)
      return result
    return None
       
  def uHelper(self, other, symbols):
    m1 = self.lhs.isSuperType(other.lhs, symbols)
    m2 = self.rhs.isSuperType(other.rhs, symbols)
    if not m1: 
      m1 = other.lhs.isSuperType(self.lhs, symbols)
      if m1:
        m1 = m1.reverse()
    if not m2:
      m2 = other.rhs.isSuperType(self.rhs, symbols)
      if m2:
        m2 = m2.reverse()
    if m1 and m2:
      result = symbol.SeqMatch(None)
      result.addMatch(m1)
      result.addMatch(m2)
      return result
    return None
    
  def unify(self, other, symbols):
    if not isinstance(other, Equality):
      return None
    if self.nt != other.nt:
      return None
      
    m = uHelper(other, symbols)
    if m:
      return m
    self.lhs, self.rhs = self.rhs, self.lhs
    m = uHelper(other, symbols)
    self.lhs, self.rhs = self.rhs, self.lhs
    return m

  def subsumes(self, other, symbols):
    if not isinstance(other, Equality):
      return False
    if self.nt != other.nt:
      return False
    if self.lhs.subsumes(other.lhs, symbols) and self.rhs.subsumes(other.rhs, symbols):
      return True
    if self.lhs.subsumes(other.rhs, symbols) and self.rhs.subsumes(other.lhs, symbols):
      return True
    return False
    
    
  def vars(self):
    return self.lhs.vars() + self.rhs.vars()

  def eval(self, env, symbols, assume = False):
    le = self.lhs.eval(env, symbols)
    re = self.rhs.eval(env, symbols)
    #check that the sides are compatible - same number of entries in a concat
    if isinstance(le, expSemantics.Concat) and isinstance(re, expSemantics.Concat) and len(le.elements) != len(re.elements):
      return False

    result = False   
    if env.provesEq(le, re, self.nt):
      result = True
      
    if not result and assume:
      #put the constraint into the environment
      if self.nt:
        cnstr = Equality(None)
        cnstr.nt = self.nt
        cnstr.lhs = le
        cnstr.rhs = re
        env[le] = cnstr
        env[re] = cnstr
      else:
        for (l, r) in self.flattenConstraint(le, re, symbols):
          cnstr = Equality(None)
          cnstr.nt = False
          cnstr.lhs = l
          cnstr.rhs = r
          env[l] = cnstr
          env[r] = cnstr
        
    return result
    
    
  def flattenConstraint(self, l, r, symbols):
    if l == r:
      return []
    if isinstance(l, symbol.Id) or isinstance(r, symbol.Id):
      return [(l,r)]
    if isinstance(l, symbol.Concat) and isinstance(r, symbol.Concat):
      return sum(map(lambda (x,y): self.flattenConstraint(x, y, symbols), zip(l.elements, r.elements)), [])
    if isinstance(l, symbol.Seq) and isinstance(r, symbol.Seq):
      if l.type(symbols) == r.type(symbols):
        return sum(map(lambda (x,y): self.flattenConstraint(x, y, symbols), zip(l.syntax, r.syntax)), [])
      else:
        return [(l,r)]
    if isinstance(l, symbol.Concat) and isinstance(r, symbol.Seq) and len(l.elements) == 1:
      return self.flattenConstraint(l.elements[0], r, symbols)
    if isinstance(l, symbol.Seq) and isinstance(r, symbol.Concat) and len(r.elements) == 1:
      return self.flattenConstraint(l, r.elements[0], symbols)
    
    return []
    
 
  def type(self, symbols):
    return symbol.TopType()
    
  def __eq__(self, other):
    if not isinstance(other, Equality):
      return False
      
    if other.nt != self.nt:
      return False
    
    return self.lhs == other.lhs and self.rhs == other.rhs    

  def __ne__(self, other):
    return not self.__eq__(other)

  def __hash__(self):    
    hash((self.lhs, self.rhs, self.nt))

  def shortString(self):
    result = ""
    if self.nt:
      result += "not "
    result += self.lhs.shortString()
    result += " = "
    result += self.rhs.shortString()
    return result

  def substMatch(self, ms):
    result = Equality(None)
    result.nt = self.nt
    result.lhs = self.lhs.substMatch(ms)
    result.rhs = self.rhs.substMatch(ms)
    return result
    
        
class Judge(symbol.Base):
  def __init__(self, ast):
    self.asts = [ast]
    
  def isSuperType(self, other, symbols):
    if not isinstance(other, Judge):
      return None
    if self.defn.name != other.defn.name:
      return None
    if self.nt != other.nt:
      return None
    result = symbol.SeqMatch(None)
    for (s, o) in zip(self.envs, other.envs) + zip(self.args, other.args):
      m = s.isSuperType(o, symbols)
      if m:
        result.addMatch(m)
      else:
        return None
    return result
  
    
  def unify(self, other, symbols):
    if not isinstance(other, Judge):
      return None
    if self.defn.name != other.defn.name:
      return None
    if self.nt != other.nt:
      return None
    result = symbol.SeqMatch(None)
    for (s, o) in zip(self.envs, other.envs) + zip(self.args, other.args):
      m = s.isSuperType(o, symbols)
      if m:
        result.addMatch(m)
      else:
        m = o.isSuperType(s, symbols)
        if m:
          result.addMatch(m.reverse())
        else:
          return None
    return result
  
  def subsumes(self, other, symbols):
    if not isinstance(other, Judge):
      return False
    if self.defn.name != other.defn.name:
      return False
    if self.nt != other.nt:
      return False
    if not reduce(lambda x,y: x and y, map(lambda (s,o): s.subsumes(o, symbols), zip(self.envs, other.envs)), True):
      return False
    if not reduce(lambda x,y: x and y, map(lambda (s,o): s.subsumes(o, symbols), zip(self.args, other.args)), True):
      return False
    return True

  def vars(self):
    return sum(map(lambda x: x.vars(), self.args), []) + sum(map(lambda x: x.vars(), self.envs), [])
    
  def type(self, symbols):
    return symbol.TopType()
    
  def eval(self, env, symbols, wth = 0, depth = 8, assume = False):
    if not depth:
      return False
    if wth == 0:
      wth = dict()
      
    envs = map(lambda x: x.eval(env, symbols), self.envs)
    args = map(lambda x: x.eval(env, symbols), self.args)
    
    #is the judgement already in the env?
    if env.canJudge(self.defn, self.nt, envs, args):
      return True
      
    for case in self.defn.cases:
      #check the envs and args match syntactically
      envMatch = []
      argMatch = []
      for (a,b) in zip(envs, case.envs):
        m = a.isSuperType(b, symbols)
        envMatch.append(m)
      for (a,b) in zip(args, case.args):
        m = a.isSuperType(b, symbols)
        argMatch.append(m)
      if reduce(lambda x, y: x and y, envMatch + argMatch, True):
        #match free variables with the with clause
        free = []
        freeMatch = []
        for x in case.free:
          if x in wth and wth[x]:
            freeMatch.append(symbol.IdMatch(x, wth[x].pop()))
          else:
            free.append(x)
        
        if not free:
          #check each premise after substing in the match
          sPrems = map(lambda p: p.substMatch(envMatch + argMatch + freeMatch), case.premises)
          if reduce(lambda x, y: x and y, map(lambda p: p.eval(env, symbols, wth, depth - 1) if isinstance(p, Judge) else p.eval(env, symbols), sPrems), True):
            return True
    
    if assume:
      cnstr = Judge(None)
      cnstr.nt = self.nt
      cnstr.args = args
      cnstr.envs = envs
      cnstr.defn = self.defn
      key = symbol.Seq(None)
      key.syntax = envs + args
      env[key] = cnstr
      
    return False
    
  def shortString(self):
    result = ""
    if self.nt:
      result += "not "
    result += self.defn.name + " "
    result += "; ".join(map(lambda x: x.shortString(), self.envs))
    result += " |- "
    result += "; ".join(map(lambda x: x.shortString(), self.args))
    return result
    
  def longString(self):
    result = ""
    if self.nt:
      result += "not "
    result += self.defn.name + " "
    result += "; ".join(map(lambda x: x.longString(), self.envs))
    result += " |- "
    result += "; ".join(map(lambda x: x.longString(), self.args))
    return result
    
  def substMatch(self, ms):
    result = Judge(None)
    result.defn = self.defn
    result.nt = self.nt
    result.envs = map(lambda x: x.substMatch(ms), self.envs)
    result.args = map(lambda x: x.substMatch(ms), self.args)
    return result
      
    
class InTest(symbol.Base):
  def __init__(self, ast):
    self.ast = ast

  def isSuperType(self, other, symbols):
    if not isinstance(other, InTest):
      return None
    if self.nt != other.nt:
      return None
    m1 = self.lhs.isSuperType(other.lhs, symbols)
    m2 = self.rhs.isSuperType(other.rhs, symbols)
    if m1 and m2:
      result = symbol.SeqMatch(None)
      result.addMatch(m1)
      result.addMatch(m2)
      return result
    return None

  def unify(self, other, symbols):
    if not isinstance(other, InTest):
      return None
    if self.nt != other.nt:
      return None
    m1 = self.lhs.isSuperType(other.lhs, symbols)
    m2 = self.rhs.isSuperType(other.rhs, symbols)
    if not m1: 
      m1 = other.lhs.isSuperType(self.lhs, symbols)
      if m1:
        m1 = m1.reverse()
    if not m2:
      m2 = other.rhs.isSuperType(self.rhs, symbols)
      if m2:
        m2 = m2.reverse()
    if m1 and m2:
      result = symbol.SeqMatch(None)
      result.addMatch(m1)
      result.addMatch(m2)
      return result
    return None
    
  def subsumes(self, other, symbols):
    if not isinstance(other, InTest):
      return False
    if self.nt != other.nt:
      return False
    if self.lhs.subsumes(other.lhs, symbols) and self.rhs.subsumes(other.rhs, symbols):
      return True
    return False
    
    
  def vars(self):
    return self.lhs.vars() + self.rhs.vars()
    
    
  def eval(self, env, symbols, assume = False):
    le = self.lhs.eval(env, symbols)
    re = self.rhs.eval(env, symbols)
    leq = [le]
    req = [re]
    env.envClosure(leq)
    env.envClosure(req)
    
    rr = False
    for l in leq:
      for r in req:  
        result = self.evalHelper(env, symbols, l, r)
        if result:
          rr = not self.nt

    cnstr = InTest(None)
    cnstr.nt = self.nt
    cnstr.lhs = le
    cnstr.rhs = re
    
    if env.constraint(cnstr):
      rr = True
      
        
    #put the constraint into the enviornment
    if not rr and assume:
      env[le] = cnstr
      env[re] = cnstr

    return rr

  def evalHelper(self, env, symbols, le, re):
    cnstr = InTest(None)
    cnstr.lhs = le
    cnstr.rhs = re
    cnstr.nt = self.nt
    if env.constraint(cnstr):
      return True
  
  
    if isinstance(le, expSemantics.Subscript):
      l = symbol.List(None)
      l.arg = le.lhs
      if l.shortString() == re.shortString():
        return True
      
    if isinstance(re, expSemantics.Concat) and hasattr(le, "shortString"):
      return reduce(lambda x, y: x or y, map(lambda x: le.shortString() == x.shortString(), re.elements), False)
      
    return False
    
    
    
  def type(self, symbols):
    return symbol.TopType()
    
  def __eq__(self, other):
    if not isinstance(other, InTest):
      return False
      
    if other.nt != self.nt:
      return False
    
    return self.lhs == other.lhs and self.rhs == other.rhs    

  def __ne__(self, other):
    return not self.__eq__(other)

  def __hash__(self):    
    hash((self.lhs, self.rhs, self.nt))

  def shortString(self):
    result = ""
    if self.nt:
      result += "not "
    result += self.lhs.shortString()
    result += " in "
    result += self.rhs.shortString()
    return result
    
  def substMatch(self, ms):
    result = InTest(None)
    result.nt = self.nt
    result.lhs = self.lhs.substMatch(ms)
    result.rhs = self.rhs.substMatch(ms)
    return result
    
    