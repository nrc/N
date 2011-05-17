import util
import expSemantics
import judge
import symbol


#TODO state is broken

class ProofState:
  def stateTuple(self):
    return [], []
    
  def stateString(self, deep = True):
    unlabList,labList = self.stateTuple(deep)
            
    result = "\n".join(unlabList)
    if result:
      result += "\n\n"
    result += "\n".join(labList)
    while result and result[-1] == "\n":
      result = result[:-1]
    return result
    
  def lookup(self, ref):
    return None
    
    
  def localStateTuple(self, deep = True):
    result = []
    if len(self.results) == 1:
      result.append(self.results[0].shortString())
      return result, []
    else:
      for i in range(len(self.results)):
        result.append(self.results[i].shortString())
      return [], result   
    
    
class ProofBase(ProofState):
  def __init__(self, parent):
    self.parent = parent
    self.unlabelled = []
    self.labelled = dict()
    self.transparentUp = False
    self.topProof = False
    self.concrete = False
    self.assumptions = []
    
  def lookupLemma(self, name):
    if self.parent:
      return self.parent.lookupLemma(name)
    else:
      return None

   
  def pop(self, ref):
    if ref.world == True or ref.up or len(ref.ids) != 1:
      return None
     
    label = ref.ids[0]
    if label in self.labelled:
      result = self.labelled[label]
      del self.labelled[label]
      return result
    else:
      return None
    
  def clear(self):
    self.unlabelled = []
    self.labelled = dict()
    
  def stateTuple(self, deep = True):
    unlabList = []
    labList = []
    if deep and self.parent:
      pul,pll = self.parent.stateTuple()
      if not self.transparentUp:
        pul = map(lambda x: "up." + x, pul)
        pll = map(lambda x: "up." + x, pll)
      unlabList = pul
      labList = pll
    
    for x in self.unlabelled:
      if x != self:
        unlabList.extend(x.stateTuple()[0])
        unlabList.extend(x.stateTuple()[1])
      else:
        unlabList.extend(x.localStateTuple()[0])
        unlabList.extend(x.localStateTuple()[1])
        
    for l in self.labelled:
      if self.labelled[l] != self:
        ull,ll = self.labelled[l].stateTuple()
      else:
        ull,ll = self.localStateTuple()
        
      for i in range(len(ull)):
        labList.append(l + ".  " + ull[i])
      for i in range(len(ll)):
        labList.append(l + "." + str(i+1) + ".  " + ll[i])
            
    return unlabList,labList
            
    
  def longString(self):
    result = ""
    result += "\n".join(map(lambda x: x.longString(), self.unlabelled))
    if result:
      result += "\n"
    result += "\n".join(map(lambda x: x + ".   " + self.labelled[x].longString(), self.labelled))
    return result
    
  def lookup(self, ref):
    if ref.world:
      if self.topProof:
        return self.lookupHere(ref)
      else:
        if self.parent:
          return self.parent.lookup(ref)
        else:
          return None
          
    if ref.case:
        if self.parent:
          return self.parent.lookup(ref)
        else:
          return None      
        
    if ref.up == 0:
      return self.lookupHere(ref)
    
    if ref.up > 0 and self.parent:
      if self.transparentUp:
        result = self.parent.lookup(ref)
        if result:
          return result
      else:
        ref.up -= 1
        result = self.parent.lookup(ref)
        ref.up += 1
        if result:
          return result

    return None
    
  def lookupHere(self, ref):
    if not ref.ids or (len(ref.ids) == 1 and not ref.ids[0]):
      return self
    if ref.ids[0] in self.labelled:
      return self.labelled[ref.ids[0]].lookup(self.truncateRef(ref))
    elif self.transparentUp:
      return self.parent.lookupHere(ref)
    else:
      return None
      
  def truncateRef(self, ref):
    class Ref:
      pass
    result = Ref()
    result.world = False
    result.up = 0
    result.ids = ref.ids[1:]
    result.str = ".".join(result.ids)
    return result
    
  def execute(self, envr, pm):
    return None

    
    
class Proof(ProofBase):
  def __init__(self, world, parent = None):
    ProofBase.__init__(self, parent)
    self.world = world
    self.lemmas = dict()
    self.checkedDone = False
    
    
  def lookupLemma(self, name):
    if name in self.lemmas:
      return self.lemmas[name]
    elif self.parent:
      return self.parent.lookupLemma(name)
    else:
      return None

    
  def shortString(self):
    if not self.parent:
      return "top"
    else:
      return self.parent.shortString() + ".proof"
    
  def execute(self, envr, pm):
    result = pm.getIndent() + "proof:"
    pm.open(self)
    return ProofResult(result)
    


class Lemma(ProofBase):
  def __init__(self, name, ast, parent):
    ProofBase.__init__(self, parent)
    self.name = name
    self.ast = ast
    self.conclusion = []
    self.proof = None
    self.freeConc = [] #variables in the conclusion not bound in the premises
    self.free = [] #variables in the premises not bound in the conclusion
    
  def getConclusions(self):
    return self.conclusion

  def lookupLemma(self, name):
    if self.name == name:
      return self
    elif self.parent:
      return self.parent.lookupLemma(name)
    else:
      return None

  def shortString(self):
    if not self.parent:
      return self.name
    else:
      return self.parent.shortString() + "." + self.name

  def calcFreeVars(self):
    premVars = sum(map(lambda p: p.vars(), self.premises), [])
    concVars = sum(map(lambda c: c.vars(), self.conclusion), [])
    self.free = []
    for v in premVars:
      if util.interestingRoot(v) and v not in concVars and v not in self.free:
        self.free.append(v)
    self.freeConc = []
    for v in concVars:
      if util.interestingRoot(v) and v not in premVars and v not in self.freeConc:
        self.freeConc.append(v)
      
  def execute(self, envr, pm):
    self.calcFreeVars()
    result = pm.getIndent() + "lemma " + self.name + ":"
    pm.open(self)
    pm.curEnv.registerVars(self.premises)
    for r in self.premises:      
      if isinstance(r, judge.Equality) and not r.nt:
        pm.curEnv[r.lhs] = r
        pm.curEnv[r.rhs] = r
    #pm.curEnv.registerVars(self.conclusion)
    return ProofResult(result)

 
class Cases(ProofState):
  def __init__(self, parent):
    self.parent = parent
    self.cases = dict()
    self.remaining = []
    self.transparentUp = True
    self.results = []

   
  def shortString(self):
    return self.parent.shortString() + ".cases"
    
  def lookup(self, ref):
    return self.parent.parent.lookup(ref)
    
  def execute(self, envr, pm):
    try:
      self.cases = self.parent.cases
    except:
      raise ProofError(self.parent.shortString() + " does not support cases")
    self.remaining = self.cases.keys()
    result = pm.getIndent() + str(len(self.cases)) + " cases (" + ", ".join(self.remaining) + "):"
    pm.open(self)
    return ProofResult(result)
    
  def nextCase(self):
    if not self.remaining:
      raise ProofError("No more cases to prove in " + self.shortString())
    label = self.remaining.pop()
    return label, self.cases[label]
    
  def getCase(self, label):
    if label not in self.remaining:
      raise ProofError("Case " + label + " does not remain to be proved in " + self.shortString())
    self.remaining.remove(label)
    return self.cases[label]
    
    
class LineBase:    
  def __init__(self, parent):
    self.parent = parent
    self.results = []
      
  def stateTuple(self, deep = True):
    return self.localStateTuple(deep)
      
  def stateString(self, deep = True, prefix = ""):
    unlabList,labList = self.stateTuple(deep)
            
    result = "\n".join(unlabList)
    if result:
      result += "\n\n"
    
    for i in range(len(labList)):
      result += prefix + str(i+1) + ".  " + labList[i] + "\n"
      
    while result.endswith("\n"):
      result = result[:-1]
    return result
    
  def resolve(self):
    if len(self.results) == 1:
      return self.results[0]
    else:
      return None
      

    
class Case(Proof, LineBase):
  def __init__(self, ast, parent):
    Proof.__init__(self, ast, parent)
    LineBase.__init__(self, parent)    
    self.concrete = True
    
  def stateTuple(self, deep = True):
    u, l = LineBase.stateTuple(self, deep)
    u2, l2 = Proof.stateTuple(self, deep)
    return u+u2,l+l2
      
  def stateString(self, deep = True):
    return LineBase.stateString(self, deep, "case.")
    
  def lookupLemma(self, name):
    if name in self.lemmas:
      return self.lemmas[name]
    return self.parent.parent.lookupLemma(name)
      
  def lookup(self, ref):
    if ref.case:
      if not ref.ids or (len(ref.ids) == 1 and not ref.ids[0]):
        return self
      if len(ref.ids) == 1:
        try:
          return DeferredLookup(self, int(ref.ids[0]))
        except:
          return None
      return None
    else:
      return Proof.lookup(self, ref)
      
  def shortString(self):
    return self.parent.shortString() + ".case" + "(" + self.label + ")"
      
  def execute(self, envr, pm):
    indent = pm.getIndent()
    pm.open(self)
    if self.label:
      self.results = self.parent.getCase(self.label)
    else:
      self.label, self.results = self.parent.nextCase()
    pm.curEnv.registerVars(self.results)
    if hasattr(self.parent.parent, "caseVars"):
      pm.curEnv.registerVars(self.parent.parent.caseVars)
    for r in self.results:      
      if isinstance(r, judge.Equality) and not r.nt:
        pm.curEnv[r.lhs] = r
        pm.curEnv[r.rhs] = r
    return ProofResult(indent + "case " + self.label + ":")


class ProofLine(ProofState, LineBase):
  def __init__(self, ast, proof):
    LineBase.__init__(self, proof)
    self.ast = ast
    self.concrete = True
    
  def stateTuple(self):
    return LineBase.stateTuple(self)
    
  def lookupLemma(self, name):
    if name == "indhyp'" and self.command == "sind":
      return self.lemma
    elif name == "indhyp" and self.command == "sind":
      return [self.lemma, True]
    return self.parent.lookupLemma(name)
   
  def longString(self):
    return self.shortString() + ". " + self.command + " " + "; ".join(map(lambda x: x.shortString(), self.args))
    
  def shortString(self):
    label = self.parent.shortString()
    if self.label:
      label += "." + self.label
    return label
    
  def lookup(self, ref):
    if ref.ids:
      if len(ref.ids) == 1:
        try:
          return DeferredLookup(self, int(ref.ids[0]))
        except ValueError:
          return None
      else:
        return None
    else:
      return self
   
  def execute(self, envr, pm):
    if self.command in ["assume", "state", "clear", "done", "and", "-and", "or", "-or", "implies", "-implies", "apply", "invert", "vars", "forall", "-forall", "exists", "-exists", "replace", "sind", "weakf", "sym", "fun", "-fun", "weakin", "let", "substeq", "inconcat", "-inconcat"]:
      result = getattr(self, "exec_" + self.command.replace("-", "m"))(pm.curEnv, pm)
      pm.curEnv.registerVars(self.results)

      for r in self.results:      
        if isinstance(r, judge.Equality) and not r.nt:
          pm.curEnv[r.lhs] = r
          pm.curEnv[r.rhs] = r
      
      return result
    else:
      raise ProofError("Unknown command: " + self.command)

  def exec_vars(self, envr, pm):    
    result = ProofResult(pm.getIndent() + "In-scope variables: " + ", ".join(map(str, envr.getVars())))
    result.source = self
    return result
      
  def exec_assume(self, envr, pm):
    result = ProofResult("")
    result.source = self
    for a in self.args:
      r = None
      if hasattr(a, "resolve"):
        r = a.resolve()
      else:
        r = a
        self.parent.assumptions.append(r)
      if not r:
        raise ProofError("Could not resolve " + a.shortString())
      self.results.append(r)
    result.verbose = "\n".join(map(lambda r: pm.getIndent() + r.shortString(), self.results))
    return result
    
  def exec_let(self, envr, pm):
    result = ProofResult("")
    result.source = self
    
    if len(self.args) != 1:
      raise ProofError("let takes one argument, found: " + str(len(self.args)))
    arg = self.args[0]
    
    if isinstance(arg, judge.Equality) or isinstance(arg, judge.InTest):
      if not (not arg.nt and arg.lhs == arg.rhs):
        vars = envr.getVars()
        if (arg.lhs in vars or not util.isAtomic(arg.lhs)) and (arg.rhs in vars or not util.isAtomic(arg.rhs)):
          raise ProofError("let command requires at least one variable to be free, found: " + arg.lhs.shortString() + "; " + arg.rhs.shortString())
    else:
      raise ProofError("let command expects equality or contains assertion, found: " + arg.shortString())
      
    self.results = [arg]
    result.verbose = pm.getIndent() + "let " + self.results[0].shortString()
    return result
    
  def exec_substeq(self, envr, pm):
    result = ProofResult("")
    result.source = self
    
    if len(self.args) != 1:
      raise ProofError("substeq takes one argument, found: " + str(len(self.args)))
    arg = self.args[0]
    
    if isinstance(arg, judge.Equality) and not arg.nt:
      l = arg.lhs.evalSubst(envr, pm.world.symList)
      r = arg.rhs.evalSubst(envr, pm.world.symList)
      if l == r:
        self.results = [arg]
      else:  
        raise ProofError("substeq could not prove equality, found: " + arg.lhs.shortString() + "(" + l.shortString() + "); " + arg.rhs.shortString() + "(" + r.shortString() + ")")
    else:
      raise ProofError("substeq command expects a postive equality, found: " + arg.shortString())
      
    result.verbose = pm.getIndent() + self.results[0].shortString()
    return result
    
  def exec_fun(self, envr, pm):
    result = ProofResult("")
    result.source = self

    if len(self.args) != 2:
      raise ProofError("fun takes two arguments, found: " + str(len(self.args)))
    inMap, funok = map(lambda x: self.resolveOrDont(x), self.args)
    
    if not isinstance(inMap, judge.InTest) or inMap.nt:
      raise ProofError("fun expects a positive contains assertion, found: " + inMap.shortString())
    if not isinstance(funok, expSemantics.FunOK):
      raise ProofError("fun expects a function predicate, found: " + funok.shortString())
    if funok.rhs != inMap.rhs:
      raise ProofError("mismatch of arguments to fun, found: " + inMap.rhs.shortString() + "; " + funok.rhs.shortString())
    
    #extract the parts of the mapping
    sym = util.atomicType(inMap.lhs, pm.world.symList)
    fType = util.isFunType(sym, pm.world.symList)
    l = r = None
    if not fType:
      raise ProofError("Can not construct function: " + sym.shortString())
    for c in sym.cases:
      if len(c.syntax) == 1 and isinstance(c.syntax[0], symbol.List):
        m = inMap.lhs.isSuperType(c.syntax[0].arg, pm.world.symList)
        l = m.match(fType.lhs[0])
        r = m.match(fType.rhs)

    if not l:
      raise ProofError("Can not construct function: " + sym.shortString())
        
    apply = expSemantics.FunApp(None)
    apply.fun = funok.rhs
    apply.args = [l]
    
    eq = judge.Equality(None)
    eq.nt = False
    eq.lhs = apply
    eq.rhs = r
      
    self.results = [eq]
    
    result.verbose = pm.getIndent() + "function introduction: " + eq.shortString()
    return result
    
  def exec_mfun(self, envr, pm):
    result = ProofResult("")
    result.source = self

    if len(self.args) != 1:
      raise ProofError("-fun takes one argument, found: " + str(len(self.args)))
    eq = self.resolveOrDont(self.args[0])
    
    if not isinstance(eq, judge.Equality):
      raise ProofError("-fun expects an equality, found: " + str(eq))    
    funapp = eq.lhs
    r = eq.rhs
    if not isinstance(funapp, expSemantics.FunApp):
      raise ProofError("-fun expects a function application on the lhs, found: " + funapp.shortString())
    fun = funapp.fun
    fType = util.isFunType(fun.type(pm.world.symList), pm.world.symList)
    if not fType or not hasattr(funapp, "funInfo") or not funapp.funInfo:
      raise ProofError("-fun can only operate on mappings, found: " + fun.shortString())
    l = funapp.args[0]

    mapping = None
    for c in funapp.funInfo.cases:
      if isinstance(c.syntax[0], symbol.List):
        mapPattern = c.syntax[0].arg
        ms = [symbol.IdMatch(fType.lhs[0], l), symbol.IdMatch(fType.rhs, r)]
        mapping = mapPattern.substMatch(ms)
    if not mapping:
      raise ProofError("Could not deconstruct function: " + fun.shortString())
    
    funok = expSemantics.FunOK(None)
    funok.rhs = fun
    inMap = judge.InTest(None)
    inMap.rhs = fun
    inMap.lhs = mapping
    inMap.nt = False
    
    self.results = [inMap, funok]
    
    result.verbose = pm.getIndent() + "function elimination: " + "; ".join(map(lambda x: x.shortString(), self.results))
    return result
    
  def exec_minconcat(self, envr, pm):
    result = ProofResult("")
    result.source = self
    
    if len(self.args) != 1:
      raise ProofError("-inconcat takes one argument, found: " + str(len(self.args)))
    intest = self.resolveOrDont(self.args[0])
    
    if not isinstance(intest, judge.InTest):
      raise ProofError("-inconcat expects a contains assertion, found: " + intext.shortString())
    cc = intest.rhs
    if not isinstance(cc, expSemantics.Concat):
      raise ProofError("-inconcat expects a concatenation, found: " + cc.shortString())
        
    els = []
    for c in cc.elements:    
      i2 = judge.InTest(None)
      i2.nt = intest.nt
      i2.lhs = intest.lhs
      i2.rhs = c
      els.append(i2)
      
    if intest.nt:
      r = expSemantics.And(None)
    else:
      r = expSemantics.Or(None)
    r.elements = els

    
    self.results = [r]
    result.verbose = pm.getIndent() + self.results[0].shortString()
    return result
    
  def exec_inconcat(self, envr, pm):
    result = ProofResult("")
    result.source = self
    
    if len(self.args) != 1:
      raise ProofError("inconcat takes one argument, found: " + str(len(self.args)))
    arg = self.resolveOrDont(self.args[0])

    if isinstance(arg, expSemantics.Or) and arg.elements:
      nt = False
    elif isinstance(arg, expSemantics.And) and arg.elements:
      nt = True
    else:
      raise ProofError("inconcat expects a non-empty conjuntion or disjuntion, found: " + arg.shortString())
    fail = []
    lhs = arg.elements[0].lhs
    for e in arg.elements:
      if not isinstance(e, judge.InTest) or e.nt != nt or e.lhs != lhs:
        fail.append(e)
    if fail:
      raise ProofError("inconcat expects homogenous contains assertions, found: " + "; ".join(map(lambda e: e.shortString(), fail)))
      
    r = judge.InTest(None)
    r.nt = nt
    r.lhs = lhs
    r.rhs = expSemantics.Concat(None)
    r.rhs.elements = map(lambda e: e.rhs, arg.elements)
    r.rhs.typeF = util.maxListType(map(lambda x: x.rhs.type(pm.world.symList), arg.elements), pm.world.symList)

    self.results = [r]
    result.verbose = pm.getIndent() + self.results[0].shortString()
    return result

    
  def exec_weakf(self, envr, pm):
    result = ProofResult("")
    result.source = self
    
    if len(self.args) != 2:
      raise ProofError("weakf takes two arguments, found: " + str(len(self.args)))
    fun, notDom = map(lambda x: self.resolveOrDont(x), self.args)
    
    if not isinstance(fun, expSemantics.FunOK):
      raise ProofError("weakf expects a fun predicate, found: " + fun.shortString())
    if not isinstance(notDom, judge.InTest) or notDom.nt == False:
      raise ProofError("weakf expects a negative contains assertion, found: " + notDom.shortString())
    if not (isinstance(notDom.rhs, expSemantics.Dom) or (isinstance(notDom.rhs, expSemantics.FunApp) and isinstance(notDom.rhs.fun, judge.DomFun))):
      raise ProofError("weakf expects a domain assertion, found: " + notDom.rhs.shortString())
    if isinstance(notDom.rhs, expSemantics.Dom):
      domFun = notDom.rhs.arg
    else:    
      domFun = notDom.rhs.args[0]

    if domFun != fun.rhs:
      raise ProofError("non-matching arguments to weakf, found: " + fun.rhs.shortString() + "; " + domFun.shortString())
      
    if not isinstance(domFun, expSemantics.Concat) or len(domFun.elements) != 2:
      raise ProofError("weakf operates on a concatenation of length two, found: " + domFun)

    fType = util.isFunType(domFun.type(pm.world.symList), pm.world.symList)
    if not fType:
      raise ProofError("weakf expects a function, found: " + domFun.shortString())
      
    mapping = None
    qVar = envr.fresh(fType.rhs)
    for c in util.atomicType(domFun.elements[0], pm.world.symList).cases:
      if isinstance(c.syntax[0], symbol.List):
        mapPattern = c.syntax[0].arg
        ms = [symbol.IdMatch(fType.lhs[0], notDom.lhs), symbol.IdMatch(fType.rhs, qVar)]
        mapping = mapPattern.substMatch(ms)
    if not mapping:
      raise ProofError("Could not deconstruct function: " + domFun.shortString())

      
    df2 = expSemantics.Concat(None)
    df2.elements.append(domFun.elements[0])
    df2.elements.append(mapping)
    df2.elements.append(domFun.elements[1])
    df2.typeF = domFun.typeF
      
    fun2 = expSemantics.FunOK(None)
    fun2.rhs = df2
    
    forall = expSemantics.Forall(None)
    forall.qVars = [qVar]
    forall.rhs = fun2
      
    self.results = [forall]
    result.verbose = pm.getIndent() + "weakening: " + self.results[0].shortString()
    return result

    
  def exec_weakin(self, envr, pm):
    result = ProofResult("")
    result.source = self

    if len(self.args) != 1:
      raise ProofError("weakin takes one argument, found: " + str(len(self.args)))
    intest = self.resolveOrDont(self.args[0])
    
    if not isinstance(intest, judge.InTest) or intest.nt:
      raise ProofError("weakin expects a positive contains assertion, found: " + intext.shortString())
    cc = intest.rhs
    if not isinstance(cc, expSemantics.Concat) or len(cc.elements) != 2:
      raise ProofError("weakin expects a concatenation of length 2, found: " + cc.shortString())
        
    cc2 = expSemantics.Concat(None)
    cc2.elements.append(cc.elements[0])
    cc2.elements.append(envr.fresh(cc.elements[0]))
    cc2.elements.append(cc.elements[1])
    cc2.typeF = cc.typeF
    
    in2 = judge.InTest(None)
    in2.rhs = cc2
    in2.nt = False
    in2.lhs = intest.lhs
    
    forall = expSemantics.Forall(None)
    forall.qVars = [cc2.elements[1]]
    forall.rhs = in2
    
    self.results = [forall]
    
    result.verbose = pm.getIndent() + "weakening: " + self.results[0].shortString()
    return result
    
    
    
  def exec_sym(self, envr, pm):
    result = ProofResult("")
    result.source = self
    
    if not self.args[0]:
      raise ProofError("No argument to sym")
    arg = self.resolveOrDont(self.args[0])
    
    if not isinstance(arg, judge.Equality):
      raise ProofError("sym expects an equality, found: " + eq.shortString())
    ne = judge.Equality(None)  
    ne.nt = arg.nt
    ne.lhs = arg.rhs
    ne.rhs = arg.lhs
    self.results = [ne]
    result.verbose = pm.getIndent() + ne.shortString()
    
    return result


    
  def exec_sind(self, envr, pm):
    result = ProofResult("")
    result.source = self
    
    pc = self.invertArg(self.args[0], envr, pm)         
    if not pc:
      self.results = [expSemantics.FALSE]
      result.verbose = pm.getIndent() + expSemantics.FALSE.shortString()
      return result
    prems,cases = pc

    if len(prems) == 1:
      self.results = prems[0]
      result.verbose = pm.getIndent() + "; ".join(map(lambda x: x.shortString(), self.results))
    else:
      self.cases = dict(zip(map(lambda c: c.name, cases), prems))
      result.verbose = pm.getIndent() + str(len(prems)) + " cases: " + "; ".join(map(lambda c: c.name, cases))
      pm.registerCallBack(self, "mor_callback")

    return result
    
  def invertArg(self, arg, envr, pm):
    arg = self.resolveOrDont(arg)
    if not isinstance(arg, judge.Judge) or arg.nt:
      raise ProofError("Argument to " + self.command + " must be a positive judgement, found: " + arg.shortString())

      
    #if any of the parts of arg are not atomic, we will need to use proxy variables
    proxy = judge.Judge(None)
    pMatches = []
    proxy.defn = arg.defn
    proxy.nt = False
    trackFresh = set()
    
    def proxify(x):
      if util.isAtomic(x):
        return x
      else:
        fresh = envr.fresh(x.type(pm.world.symList))
        trackFresh.add(fresh)
        pMatches.append(x.isSuperType(fresh, pm.world.symList))
        return fresh
        
    proxy.envs = map(proxify, arg.envs)
    proxy.args = map(proxify, arg.args)

    #find the cases that match syntactically
    cases = []
    matches2 = [] #matches formals to fresh variables
    matches = [] #matches fresh variables to actuals
    for c in proxy.defn.cases:
      m2 = symbol.SeqMatch(None)
      for source in set(c.getConclusions()[0].vars()):
        for v in source.vars():
          if util.interestingRoot(v):
            m2.addIdMatch(v, envr.fresh(v))
      m = proxy.unify(c.getConclusions()[0].substMatch([m2]), pm.world.symList)
      if m:        
        cases.append(c)
        m.substMatch(pMatches)
        matches.append(m)
        matches2.append(m2)

    
    #if no cases, then we have a contradiction and the result is false
    if not cases:
      return None
      
      
    #use fresh variables for fv
    for c,m in zip(cases, matches2):
      for f in c.free:
        m.addIdMatch(f, envr.fresh(f))
        
    
    #find the premises of those cases, subst variables deduced from conc
    prems = map(lambda (c,m,m2): map(lambda p: p.substMatch([m2]).substMatch([m]), c.premises), zip(cases, matches, matches2))
    
    for (p, m, m2) in zip(prems, matches, matches2):
      for source in set(m.dom()):
        #account for equalities between actuals and formals of the conclusion/arg
        if not util.isAtomic(source):
          pe = judge.Equality(None)
          pe.lhs = m.match(source)
          pe.rhs = source.substMatch([m2]).substMatch([m])
          pe.nt = False
          p.insert(0, pe)
        #account for where refinements of actuals would otherwise be lost
        elif not source.substMatch([m]).isSuperType(source, pm.world.symList):
          #revert the premises to using the more refined variable
          for i in range(len(p)):
            p[i] = p[i].substMatch([symbol.IdMatch(m.match(source), source.substMatch([m2]))])
          #add an equality which captures the refinement
          pe = judge.Equality(None)
          pe.lhs = m.match(source)
          pe.rhs = source.substMatch([m2])
          pe.nt = False
          p.insert(0, pe)
          
    return prems,cases

      
  def exec_invert(self, envr, pm):
    result = ProofResult("")
    result.source = self
    
    pc = self.invertArg(self.args[0], envr, pm)         
    if not pc:
      self.results = [expSemantics.FALSE]
      result.verbose = pm.getIndent() + expSemantics.FALSE.shortString()
      return result
    prems,cases = pc

    #package up results or open cases
    if self.star:
      r = expSemantics.Or(None)
      for p in prems:
        if len(p) == 0:
          cr = expSemantics.TRUE
        elif len(p) == 1:
          cr = p[0]
        else:
          cr = expSemantics.And(None)
          cr.elements = p
        r.elements.append(cr)
      if r.elements == 1:
        r = r.elements[0]
      self.results = [r]
      result.verbose = pm.getIndent() + r.shortString()
    else:
      if len(prems) == 1:
        self.results = prems[0]
        result.verbose = pm.getIndent() + "; ".join(map(lambda x: x.shortString(), self.results))
      else:
        self.cases = dict(zip(map(lambda c: c.name, cases), prems))
        result.verbose = pm.getIndent() + str(len(prems)) + " cases: " + "; ".join(map(lambda c: c.name, cases))
        pm.registerCallBack(self, "mor_callback")
      
    return result
    
  def exec_apply(self, envr, pm):
    result = ProofResult("")
    rule = self.args[0]
    guessFV = False
    if hasattr(rule, "__iter__"):
      guessFV = rule[1]
      rule = rule[0]
    
    args = map(lambda x: [x], filter(lambda x: x != None, map(self.resolveOrDont, self.args[1:])))
    if self.equals:
      map(lambda x: envr.envClosure(x), args)

    fail = []
    matches = []
    for p in rule.premises:
      mm = []
      for a in args:
        for aa in a:
          m = aa.isSuperType(p, pm.world.symList)
          if m:
            mm.append(m)
      if not mm:
        fail.append(p)
      matches.append(mm)      
    if fail:
      raise ProofError("Premises of " + rule.name + " could not be satisfied: " + "; ".join(map(lambda x: x.shortString(), fail)))
    #try to unify the matches
    poss = [[]]
    for mm in matches:
      newPoss = []
      for m in mm:
        for p in poss:
          #if m agrees with p, then add p + m to newPoss
          if self.matchAgrees(p, m):
            newPoss.append(p + m.flatMatches())
      poss = newPoss
    if not poss:
      raise ProofError("Premises of " + rule.name + " could not be satisfied.")

    #find the conclusion and apply the possible unifications to it
    conc = sum(map(lambda c: map(lambda p: c.substMatch(p), poss), rule.getConclusions()), [])
    #fv in conc => forall quant
    #if the indhyp is being applied and was not primed (guessFV), then guess the FVs
    if not guessFV and conc and rule.freeConc:
      r = expSemantics.Forall(None)
      r.qVars = rule.freeConc
      if len(conc) == 1:
        r.rhs = conc[0]
      else:
        r.rhs = expSemantics.And(None)
        r.rhs.elements = conc
      conc = [r]   
    
    self.results = conc
    result.source = self
    result.verbose = pm.getIndent() + "Applied " + rule.name + ": " + "; ".join(map(lambda x: x.shortString(), self.results))
    return result
    
  #ms is  alist of matches
  #m is a match
  #returns true if m does not contradict any of the matches in ms
  def matchAgrees(self, ms, m):
    for mp in ms:
      for d in mp.dom():
        if d in m.dom() and mp.match(d) != m.match(d):
          return False
    return True
    
  def exec_clear(self, envr, pm):
    result = ProofResult("")
    if self.args:
      result.verbose = pm.getIndent() + "Cleared from(" + self.parent.shortString() + "):\n"
      for a in self.args:
        p = self.parent.pop(a)
        if p:
          result.verbose += pm.getIndent() + "  " + a.str + ". " + ";   ".join(p.stateString().split("\n")) + "\n"
      while result.verbose.endswith("\n"):
        result.verbose = result.verbose[:-1]
    else:
      result.verbose = pm.getIndent() + "Cleared(" + self.parent.shortString() + "):\n" + "\n".join(map(lambda x: pm.getIndent() + "  " + x, self.parent.stateString(False).split("\n")))
      self.parent.clear()
    
    return result
    
  def exec_state(self, envr, pm):
    target = self.parent
    
    if self.args:
      target = self.args[0]
      
    indent = pm.getIndent()
    msg = indent + "proof state(" + target.shortString() + "):\n"
    indent += "  "
    msg += "\n".join(map(lambda x: indent + x, target.stateString().split("\n")))
    
    result = ProofResult(msg)
    result.source = self
    return result
    
  def exec_done(self, envr, pm):
    args = map(lambda x: [x], filter(lambda x: x != None, map(self.resolveOrDont, self.args)))
    if self.equals:
      map(lambda x: envr.envClosure(x), args)
    fail = []
    for p in self.lemma.conclusion:
      trip = False
      for a in args:
        for aa in a:
          if aa.subsumes(p, pm.world.symList):
            trip = True
            break
        if trip:
          break
      if not trip:
        fail.append(p)
    if fail:
      raise ProofError("Some conclusions could not be satisfied: " + "; ".join(map(lambda x: x.shortString(), fail)))
            
    result = ProofResult("")
    result.source = self
    if self.star:
      self.parent.parent.results.append(self)
      result.msg = pm.getIndent() + "Case closed"
      result.verbose = result.msg + " with " + "; ".join(map(lambda x: x.label, self.args))
    else:
      if self.parent and self.parent.parent and isinstance(self.parent.parent, Cases):
        self.results = [expSemantics.FALSE]
        self.parent.parent.results.append(self)
      result.msg = pm.getIndent() + "Case proved for " + self.lemma.shortString()
      result.verbose = result.msg + " by " + "; ".join(map(lambda x: x.label, self.args))
    return result
    
  def exec_and(self, envr, pm):
    result = ProofResult("")
    result.source = self
    if self.args:
      conc = expSemantics.And(self.ast)
      conc.elements = map(lambda x: x.resolve(), self.args)
      self.results = [conc]
      result.verbose = pm.getIndent() + conc.shortString()
    
    return result
    
  def exec_mand(self, envr, pm):
    result = ProofResult("")
    result.source = self
    if self.args:
      a = self.args[0].resolve()
      if isinstance(a, expSemantics.And):
        self.results = a.elements
        result.verbose = pm.getIndent() + "; ".join(map(lambda x: x.shortString(), self.results))
      else:
        raise ProofError(a.shortString() + " is not an 'and' object")        
    
    return result
 
  def resolveOrDont(self, a):
    r = None
    if hasattr(a, "resolve"):
      r = a.resolve()
    else:
      r = a
    return r
 
  def exec_or(self, envr, pm):
    result = ProofResult("")
    result.source = self
    if self.args:
      conc = expSemantics.Or(self.ast)
      conc.elements = map(lambda x: self.resolveOrDont(x), self.args)
      self.results = [conc]
      result.verbose = pm.getIndent() + conc.shortString()
    
    return result
    
  def exec_mor(self, envr, pm):
    result = ProofResult("")
    result.source = self
    if self.args:
      a = self.args[0].resolve()
      if isinstance(a, expSemantics.Or):
        result.verbose = pm.getIndent() + str(len(a.elements)) + " cases: " + "; ".join(map(lambda x: x.shortString(), a.elements))
        self.cases = dict(zip(map(lambda x: str(x + 1), range(len(a.elements))), map(lambda x: [x], a.elements)))
      else:
        raise ProofError(a.shortString() + " is not an 'or' object")        
    else:
      raise ProofError("No arguments to '-or'")        
    
    pm.registerCallBack(self, "mor_callback")
    return result
  
  def mor_callback(self, cases):
    comps = []
    falseTrip = True
    if len(cases.results) < len(cases.cases):
      falseTrip = False
    for r in cases.results:
      if not r.results:
        falseTrip = False
      elif len(r.results) == 1:
        rr = r.results[0]
        if rr != expSemantics.FALSE:
          falseTrip = False
        comps.append(rr)
      elif len(r.results) > 1:
        result = expSemantics.And(None)
        result.elements = r.results
        comps.append(result)
        
    if falseTrip:
      self.results = [expSemantics.FALSE]
    else:
      comps = list(set(comps))
      if expSemantics.FALSE in comps:
        comps.remove(expSemantics.FALSE)
      if not comps:
        self.results = [expSemantics.TRUE]
      elif len(comps) == 1:
        self.results = [comps[0]]
      else:
        result = expSemantics.Or(None)
        result.elements = comps
        self.results = [result]
        
      
  def exec_replace(self, envr, pm):  
    result = ProofResult("")
    result.source = self
    
    exp = self.args[0].resolve()
    if not exp:
      raise ProofError("reference " + self.args[0].shortString() + " cannot be resolved")
      
    args = self.args[1:]
    
    def checkAndMakeMatch(x):
      x = self.resolveOrDont(x)
      if not isinstance(x, judge.Equality) or x.nt:
        raise ProofError("replace command requires arguments to be positive equalities; found: " + x.shortString())
      if self.star:
        return symbol.IdMatch(x.rhs, x.lhs)
      else:
        return symbol.IdMatch(x.lhs, x.rhs)
    
    self.results = [exp.substMatch(map(checkAndMakeMatch, args))]      
    result.verbose = pm.getIndent() + self.results[0].shortString()
    
    return result
      
  def exec_forall(self, envr, pm):
    result = ProofResult("")
    result.source = self
    if self.args:
      def checkVar(x):
        if isinstance(x, symbol.Id):
          return None
        if isinstance(x, symbol.List):
          return checkVar(x.arg)
        return x
    
      checks = reduce(lambda x,y: x + [y] if y else x, map(checkVar, self.args), [])
      if checks:
        raise ProofError("Non-formal variable as argument to forall: " + ", ".join(map(lambda x: x.shortString(), checks)))
      vars = envr.getVars()
      checks = reduce(lambda x,y: x + [y] if y else x, map(lambda x: x if x in vars else None, self.args), [])
      if checks:
        raise ProofError("Argument to forall not fresh: " + ", ".join(map(lambda x: x.shortString(), checks)))
      result.verbose = pm.getIndent() + "forall scope, variables " + "; ".join(map(lambda x: x.shortString(), self.args))
      self.cases = dict([("1", [])])
      #make variables in scope in the case
      self.caseVars = self.args
    else:
      raise ProofError("No arguments to 'forall'")        
    
    pm.registerCallBack(self, "forall_callback")
    return result
  
  def exec_exists(self, envr, pm):
    result = ProofResult("")
    result.source = self
    
    exists = expSemantics.Exists(None)
    exists.rhs = self.args[0].resolve()
    if not exists.rhs:
      raise ProofError("reference " + self.args[0].shortString() + " cannot be resolved")
    exists.qVars = self.args[1:]
    
    def checkVar(x):
      if isinstance(x, symbol.Id):
        return None
      if isinstance(x, symbol.List):
        return checkVar(x.arg)
      return x
      
    checks = reduce(lambda x,y: x + [y] if y else x, map(checkVar, exists.qVars), [])
    if checks:
      raise ProofError("Non-variable as argument to exists: " + ", ".join(map(lambda x: x.shortString(), checks)))

    self.results = [exists]      
    result.verbose = pm.getIndent() + self.results[0].shortString()
    
    return result
    
  def exec_mexists(self, envr, pm):
    result = ProofResult("")
    result.source = self
    
    exists = self.args[0].resolve()
    if not exists:
      raise ProofError("reference " + self.args[0].shortString() + " cannot be resolved")
    args = self.args[1:]
    if not isinstance(exists, expSemantics.Exists):
      raise ProofError("-exists requires an exists quantified expression as its argument; found: " + str(forall))
      
    self.results = [exists.rhs.substMatch(map(lambda x: symbol.IdMatch(x, envr.fresh(x)), exists.qVars))]    
    result.verbose = pm.getIndent() + self.results[0].shortString()
    
    return result
  
  def forall_callback(self, cases):
    result = expSemantics.Forall(None)
    #quantifying variables
    result.qVars = self.args
    
    #rhs
    if len(cases.results[0].results) == 0:
      result.rhs = expSemantics.TRUE
    elif len(cases.results[0].results) == 1:
      result.rhs = cases.results[0].results[0]
    else:
      result.rhs = expSemantics.And(None)
      result.rhs.elements = cases.results[0].results
     
    self.results = [result]
    
  def exec_mforall(self, envr, pm):
    result = ProofResult("")
    result.source = self
    forall = self.args[0].resolve()
    if not forall:
      raise ProofError("reference " + self.args[0].shortString() + " cannot be resolved")
    if not isinstance(forall, expSemantics.Forall):
      raise ProofError("-forall requires a forall quantified expression as its first argument; found: " + str(forall))
    args = self.args[1:]
    if len(args) != len(forall.qVars):
      raise ProofError("Mismatch in number of arguments to -forall; found: " + str(len(args)) + ", expected: " + str(len(forall.qVars)))
    for (f,a) in zip(forall.qVars, args):
      if not a.isSuperType(f, pm.world.symList):
        raise ProofError("Type mismatch in argument to -forall; found: " + str(a) + ", expected: " + str(f))
    self.results = [forall.rhs.substMatch(map(lambda (f,t): symbol.IdMatch(f,t), zip(forall.qVars, args)))]
    result.verbose = pm.getIndent() + self.results[0].shortString()  
    return result
    
  def exec_implies(self, envr, pm):
    result = ProofResult("")
    result.source = self
    if self.args:
      result.verbose = pm.getIndent() + "implication scope, assumptions " + "; ".join(map(lambda x: x.shortString(), self.args))
      self.cases = dict([("1", self.args)])
    else:
      raise ProofError("No arguments to 'implies'")        
    
    pm.registerCallBack(self, "implies_callback")
    return result
    
  def exec_mimplies(self, envr, pm):
    result = ProofResult("")
    result.source = self
    if self.args:
      implies = self.args[0].resolve()
      if not implies:
        raise ProofError("reference " + self.args[0].shortString() + " cannot be resolved")

      if isinstance(implies.lhs, expSemantics.And):
        lhs = implies.lhs.elements
      else:
        lhs = [implies.lhs]
        
      if len(lhs) == len(self.args)-1:
        for a,f in zip(self.args[1:], lhs):
          aa = a.resolve()
          if not aa:
            raise ProofError("reference " + a.shortString() + " cannot be resolved")
          if not aa.subsumes(f, pm.world.symList):
            raise ProofError(aa.shortString() + " does not give " + f.shortString())
      else:
        raise ProofError("Number of arguments to -implies (" + str(len(self.args)-1)+ ") does not match number of implicands (" + str(len(lhs)) + ")")
      

      if isinstance(implies.rhs, expSemantics.And):
        self.results = implies.rhs.elements
      else:
        self.results = [implies.rhs]
      result.verbose = pm.getIndent() + "; ".join(map(lambda x: x.shortString(), self.results))
    
    return result
  
  def implies_callback(self, cases):
    result = expSemantics.Implies(None)
    #lhs
    if len(self.args) == 1:
      result.lhs = self.args[0]
    else:
      result.lhs = expSemantics.And(None)
      result.lhs.elements = self.args
    
    #rhs
    if len(cases.results[0].results) == 0:
      result.rhs = expSemantics.TRUE
    elif len(cases.results[0].results) == 1:
      result.rhs = cases.results[0].results[0]
    else:
      result.rhs = expSemantics.And(None)
      result.rhs.elements = cases.results[0].results

     
    self.results = [result]
 
 
class DeferredLookup:
  def __init__(self, proofLine, index):
    self.proofLine = proofLine
    self.index = index
    self.concrete = True
    
  def shortString(self):
    return "Deferred (" + self.proofLine.shortString() + ")." + str(self.index)
    
  def resolve(self):
    if len(self.proofLine.results) > self.index-1:
      self.label = self.proofLine.label + "." + str(self.index)
      return self.proofLine.results[self.index-1]
    else:
      return None

    
class ProofError():
  def __init__(self, msg):
    self.msg = msg
    
  def __str__(self):
    return self.msg
    
VERBOSE_RESULTS = True
    
class ProofResult():
  def __init__(self, msg):
    self.msg = msg
    self.verbose = ""
    self.source = None
    
  def __str__(self):
    if VERBOSE_RESULTS and self.verbose:
      return self.verbose
    else:
      return self.msg
    
    