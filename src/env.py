import judge
import symbol
import util

    
class Env:
  def __init__(self, parent = None):
    self.vars = dict()
    self.frsh = dict()
    self.bound = []
    self.bindings = dict()
    self.parent = parent
    self.regVars = set()
    if parent:
      self.globals = parent.globals
    else:
      self.globals = dict()
      
  def registerVars(self, obj):
    if hasattr(obj, "__iter__"):
      self.regVars |= set(sum(map(lambda x: x.vars(), obj), []))
    else:
      self.regVars |= set(obj.vars())
      
  def getVars(self):
    result = set()
    if self.parent != None:
      result = self.parent.getVars()
    result |= self.regVars
    return result
    
  def freshOld(self, clone):
    if not util.interestingRoot(clone):
      return clone
    if isinstance(clone, symbol.Id):
      result = symbol.FreshId(clone.symbol, self.getFreshNum(clone.name))
      result.name = clone.name
      return result
    elif isinstance(clone, symbol.List):
      result = symbol.List(None)
      result.arg = self.freshOld(clone.arg)
      return result
    elif isinstance(clone, symbol.Symbol):
      return symbol.FreshId(clone, self.getFreshNum(clone.shortString()))
    elif isinstance(clone, symbol.Seq):
      result = symbol.Seq(None)
      result.syntax = map(lambda x: self.freshOld(x), clone.syntax)
      return result
    else:
      print "Error: can't clone " + str(clone)
      return symbol.ErrSym()
    
  def makeFresh(self, result, listDepth):  
    nextTry = 0
    test = result
    vars = self.getVars()
    for i in range(listDepth):
      t = symbol.List(None)
      t.arg = test
      test = t
    while test in vars:
      nextTry += 1
      result.mod = str(nextTry)
    return result
    
  def fresh(self, clone, listDepth = 0):
    if not util.interestingRoot(clone):
      return clone
    if isinstance(clone, symbol.Id):
      result = symbol.Id(None, clone.symbol)
      result.name = clone.name
      result = self.makeFresh(result, listDepth)
    elif isinstance(clone, symbol.Symbol):
      result = self.makeFresh(symbol.Id(None, clone), listDepth)
    elif isinstance(clone, symbol.List):
      result = symbol.List(None)
      result.arg = self.fresh(clone.arg, listDepth + 1)
    elif isinstance(clone, symbol.Seq):
      result = symbol.Seq(None)
      result.syntax = map(lambda x: self.fresh(x, listDepth), clone.syntax)
    else:
      print "Error: can't clone " + str(clone)
      return symbol.ErrSym()
      
    if listDepth == 0:
      self.regVars.add(result)
    return result
      
  def getFreshNum(self, name):
    if name in self.frsh:
      self.frsh[name] += 1
      return self.frsh[name]
    else:
      self.frsh[name] = 0
      return 1
      
  #return a new environment with de-listed versions of the bindings in
  def deListifyBindings(self):
    dlP = None
    if self.parent:
      dlP = self.parent.deListifyBindings()
    result = Env(dlP)
    for b in self.bound:
      if isinstance(b, symbol.List):
        result.bound.append(b.arg)
    result.frsh = self.frsh
    result.vars = self.vars
    for b in self.bindings:
      if isinstance(b, symbol.List):
        result.bindings[b.arg] = self.bindings[b]
    return result
      
  def addBindings(self, bindings, bounds):
    self.bindings.update(bindings)
    self.bound.extend(bounds)
      
  def shortString(self):
    result = "\n".join(map(lambda x: x.shortString() + " --> " + ", ".join(map(lambda y: y.shortString(), self.vars[x])), self.vars))
    if self.parent:
      result += "\n" + self.parent.shortString()
    return result
    
  def longString(self):
    result = "Constraints:\n" + self.shortString()
    result += "\nBindings:\n" + self.bindString()
    result += "\nBound variables:\n" + self.boundString()
    return result
    
  def bindString(self):
    result = "\n".join(map(lambda i: i[0].shortString() + " --> " + ",".join(map(lambda j: j.shortString(), i[1])), self.bindings.items()))
    if self.parent:
      result += "\n" + self.parent.bindString()
    return result
    
  def boundString(self):
    result = "\n".join(map(lambda i: i.shortString(), self.bound))
    if self.parent:
      result += "\n" + self.parent.boundString()
    return result

  
  #returns true if x is a binder
  def isBoundVar(self, x):
    if x in self.bound:
      return True
    if self.parent:
      return self.parent.isBoundVar(x)
    return False
    
  #return a list of variables bound in e
  def boundVars(self, e):
    s = []
    if self.parent:
      s = self.parent.boundVars(e)
      
    r = []
    if e in self.bindings:
      r = self.bindings[e]
    
    return s + r
    
  def __len__(self):
    if self.parent:
      return len(self.vars) + self.parent.__len__()
    else:  
      return len(self.vars)
    
  #True if the constraint is lexically in the env
  def constraint(self, cnstr):
    if cnstr.lhs not in self:
      return False
    poss = self[cnstr.lhs]
    return cnstr in poss
    
  #see if the env can be used to prove the given constraint
  def proves(self, cnstr):
    if isinstance(cnstr, judge.Equality) or isinstance(cnstr, judge.InTest):
      return self.provesHelper(cnstr.lhs, cnstr.rhs, cnstr.nt, cnstr.__class__)
      
      #c = None
      #if isinstance(cnstr, judge.Equality):
      #  c = judge.Equality(None)
      #elif isinstance(cnstr, judge.InTest):
      #  c = judge.InTest(None)
      #leq = [cnstr.lhs]
      #req = [cnstr.rhs]
      #self.envClosure(leq)
      #self.envClosure(req)
      #c.nt = cnstr.nt
      #for l in leq:
      #  for r in req:
      #    c.lhs = l
      #    c.rhs = r
      #    if self.constraint(c):
      #      return True
            
    return False
  
  def provesEq(self, le, re, nt = False):
    return self.provesHelper(le, re, nt, judge.Equality)

  def provesNE(self, le, re):
    return self.provesEq(le, re, True)      
  
  #the le is equal to one of re (re is a python list), equiv to Python in, not N in  
  def provesIn(self, le, re):
    for r in re:
      if self.provesEq(le, r, False):
        return True
            
    return False

  def provesNIn(self, le, re):
    for r in re:
      if not self.provesEq(le, r, True):
        return False
            
    return True
    
  #prove the constraint that le is in re (re is expected to be a Concat or Seq, etc)
  def provesInN(self, le, re, nt = False):
    return self.provesHelper(le, re, nt, judge.InTest)
    
  def provesNInN(self, le, re):
    return self.provesInN(le, re, True)
    
  #true if we can prove that for any r in re, le == re or le in re
  def provesEqOrIn(self, le, re):
    for r in re:
      if self.provesEq(le, r, False) or self.provesInN(le, r, False):
        return True
            
    return False
    
  def provesNEqOrIn(self, le, re):
    for r in re:
      if not (self.provesEq(le, r, True) or self.provesInN(le, r, True)):
        return False
            
    return True
   
  def equiv(self, l, r):
    if l == r:
      return True
    if l.__class__.__name__ == "Elipses" or r.__class__.__name__ == "Elipses":
      return True
    if l.__class__.__name__ == r.__class__.__name__ == "List":
      return self.equiv(l.arg, r.arg)
    if l.__class__.__name__ == r.__class__.__name__ == "Concat" and len(l.elements) == len(r.elements):
      return reduce(lambda x,y: x and y, map(lambda (l,r): self.equiv(l, r), zip(l.elements, r.elements)), True)
    if l.__class__.__name__ == r.__class__.__name__ == "Seq":
      i = j = 0
      while i < len(l.syntax):
        if j >= len(r.syntax):
          return False
        le = l.syntax[i]
        re = r.syntax[j]
        if le.__class__.__name__ == "Elipses":
          j += 1
          if j >= len(r.syntax):
            return i >= len(l.syntax)-1
          if i+1 < len(l.syntax) and self.equiv(l.syntax[i+1], r.syntax[j]):
            i += 1
        elif re.__class__.__name__ == "Elipses":
          i += 1
          if i >= len(r.syntax):
            return j >= len(l.syntax)-1
          if j+1 < len(r.syntax) and self.equiv(l.syntax[i], r.syntax[j+1]):
            j += 1
        elif self.equiv(le, re):
          i += 1
          j += 1
        else:
          return False
      while j < len(r.syntax) and r.syntax[j].__class__.__name__ == "Elipses":
        j += 1
      return j >= len(r.syntax)
    return False
  
  #generic version of provesEq/provesInN
  def provesHelper(self, le, re, nt, cnstrCls):
    leq = [le]
    req = [re]
    self.envClosure(leq)
    self.envClosure(req)
    for l in leq:
      poss = []
      if l in self:
        poss = self[l]
        
      for r in req:
        if cnstrCls == judge.Equality and self.equiv(l, r):
          return not nt
        if cnstrCls == judge.InTest and r.__class__.__name__ == "Concat" and l in r.elements:
          return not nt
        for p in poss:
          if isinstance(p, cnstrCls) and p.nt == nt:
            if (self.equiv(l, p.lhs) and self.equiv(r, p.rhs)) or (cnstrCls == judge.Equality and self.equiv(r, p.lhs) and self.equiv(l, p.rhs)):
              return True
          #bit of a special case, if we know that x is not in [x], then for all x' in [x] we can prove that x not= x'
          #the last clause assumes that the rhs of an InTest is always a Concat - not sure if this is right
          if cnstrCls == judge.Equality and nt and p.nt and isinstance(p, judge.InTest):
            if p.rhs.__class__.__name__ == "Concat" and r in p.rhs.elements:
              return True
            if hasattr(p.rhs, "__iter__") and r in p.rhs:
              return True
        #take account of elements in a compound object
        if nt and cnstrCls == judge.Equality and self.existsElementEq(l, r, nt):
          return True
        if nt and cnstrCls == judge.Equality and self.existsElementEq(l, r, not nt):
          return False
        if not nt and cnstrCls == judge.Equality and self.allElementEq(l, r, nt):
          return True
        if not nt and cnstrCls == judge.Equality and self.allElementEq(l, r, not nt):
          return False
            
            
    return False
    
  def allElementEq(self, l, r, nt):
    if l.__class__.__name__ == r.__class__.__name__ == "Concat":
      if len(l.elements) != len(r.elements):
        return False
      for (le, re) in zip(l.elements, r.elements):
        if not self.allElementEq(le, re, nt):
          return False
      return True
    if l.__class__.__name__ == r.__class__.__name__ == "Seq":
      if len(l.syntax) != len(r.syntax):
        return False
      for (le, re) in zip(l.syntax, r.syntax):
        if not self.allElementEq(le, re, nt):
          return False
      return True
      
    return self.elementEq(l, r, nt)
  
  
  def existsElementEq(self, l, r, nt):
    if l.__class__.__name__ == r.__class__.__name__ == "Concat":
      if len(l.elements) != len(r.elements):
        return False
      for (le, re) in zip(l.elements, r.elements):
        if self.existsElementEq(le, re, nt):
          return True
    if l.__class__.__name__ == r.__class__.__name__ == "Seq":
      if len(l.syntax) != len(r.syntax):
        return False
      for (le, re) in zip(l.syntax, r.syntax):
        if self.existsElementEq(le, re, nt):
          return True
      
    return self.elementEq(l, r, nt)
      
  def elementEq(self, l, r, nt):
    if l == r:
      return not nt
    if l.__class__.__name__ == "Id" or r.__class__.__name__ == "Id":
      cnstr = judge.Equality(None)
      cnstr.lhs = l
      cnstr.rhs = r
      cnstr.nt = nt
      if self.constraint(cnstr):
        return True
      
    return False
    
  def envClosure(self, st):
    flag = False
    for s in st:
      f = False
      if s.__class__.__name__ == "Id":
        f = self.closeId(s, st)       
      if s.__class__.__name__ == "Seq":
        f = self.closeSeq(s, st)       
      if s.__class__.__name__ == "Concat":
        f = self.closeConcat(s, st)       
      if s.__class__.__name__ == "Judge":
        f = self.closeJudge(s, st)       
      if s.__class__.__name__ == "Equality":
        f = self.closeEquality(s, st)       
      if s.__class__.__name__ == "InTest":
        f = self.closeEquality(s, st)       
      if f:
        flag = True
      
    if flag:
      self.envClosure(st)
      
  def closeJudge(self, s, st):
    ee = map(lambda x: [x], s.envs)
    ae = map(lambda x: [x], s.args)
    map(lambda x: self.envClosure(x), ee)
    map(lambda x: self.envClosure(x), ae)
    
    es = [[]]
    for e in ee:
      es2 = []
      for ss in es:
        for ei in e:
          es2.append(ss + [ei])
      es = es2
    
    aas = [[]]
    for e in ae:
      as2 = []
      for ss in aas:
        for ei in e:
          as2.append(ss + [ei])
      aas = as2
    
    flag = False
    for e in es:
      for a in aas:
        r = judge.Judge(None)
        r.nt = s.nt
        r.envs = e
        r.args = a
        r.defn = s.defn
        if r not in st:
          st.append(r)
          flag = True
    return flag
    
    
      
  def closeEquality(self, s, st):
    le = [s.lhs]
    re = [s.rhs]
    self.envClosure(le)
    self.envClosure(re)
    flag = False
    for l in le:
      for r in re:
        e = s.__class__(None)
        e.nt = s.nt
        e.lhs = l
        e.rhs = r
        if e not in st:
          st.append(e)
          flag = True
    return flag
      
      
  def closeSeq(self, s, st):
    syns = [[]]
    for e in s.syntax:
      ee = [e]
      self.envClosure(ee)
      s2 = []
      for ss in syns:
        for eee in ee:
          s2.append(ss + [eee])
      syns = s2
      
    def makeSeq(x):
      result = symbol.Seq(None)
      result.syntax = x
      return result
    result = map(makeSeq, syns)
      
    flag = False
    for r in result:
      if r not in st:
        st.append(r)
        flag = True
        
    flag |= self.closeId(s, st)    
    
    return flag
    
  def closeConcat(self, s, st):
    syns = [[]]
    for e in s.elements:
      ee = [e]
      self.envClosure(ee)
      s2 = []
      for ss in syns:
        for eee in ee:
          s2.append(ss + [eee])
      syns = s2
      
    def makeCc(x):
      result = symbol.Concat(None)
      result.elements = x
      result.typeF = s.typeF
      return result
    result = map(makeCc, syns)
      
    flag = False
    for r in result:
      if r not in st:
        st.append(r)
        flag = True
    
    return flag
      
  def closeId(self, s, st):
    flag = False
    if s in self:
      for eq in self[s]:
        if isinstance(eq, judge.Equality) and not eq.nt:
          r = None
          if eq.lhs == s:
            r = eq.rhs
          elif eq.rhs == s:
            r = eq.lhs
          if r and not r in st:
            st.append(r)
            flag = True
            
    return flag
    
  def canJudge(self, defn, nt, envs, args):
    #make the key and close it
    key = symbol.Seq(None)
    key.syntax = envs + args
    ke = [key]
    self.envClosure(ke)
    #check if we have the key and for the right defn and nt
    for k in ke:
      if k in self and self[k]:
        for c in self[k]:
          if c.nt == nt and c.defn == defn:
            return True
        
    return False
            
  
  def __getitem__(self, key):
    if hasattr(key, "symbol") and key.symbol.globe:
      if key in self.globals:
        return [self.globals[key]]
      raise KeyError(key)
      
    result = None
    if key in self.vars:
      result = self.vars[key]
    if not result and self.parent:
      result = self.parent[key]
      
    if result == None:
      raise KeyError(key)
    return result
  
  def __setitem__(self, key, value):
    if hasattr(key, "symbol") and key.symbol.globe:
      self.globals[key] = value
      return
  
    keySet = [key]
    keySet.extend(key.vars())
    keySet = set(keySet)
    for k in keySet:
      if k not in self.vars:
        self.vars[k] = []
      self.vars[k].append(value)
    
  def __contains__(self, key):
    if hasattr(key, "symbol") and key.symbol.globe:
      if key in self.globals:
        return key in self.globals
      return False
    
    result = key in self.vars
    if not result and self.parent:
      result = key in self.parent
    return result
    
  def __iter__(self):
    return self.iter()
    
  def iter(self):
    for k in self.vars.keys():
      yield k
    if self.parent:
      self.parent.iter()
    raise StopIteration()


    

  
    
    
    