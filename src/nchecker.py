#TODO - 

#make all strings in asts Ids - make sure errors always point at the right token
#type var inference in fun apps
#type vars in subtyping


from ast import *
from nparser import Err
from pretty import ppSynExp
from judge import *
from expSemantics import *
from symbol import *
from env import Env
import util
import proof
import nparser



class Checker:
  def __init__(self, world):
    self.world = world
    self.errs = []
    self.log = ""
    
  def check(self):
    self.checkSyntax()
    
    self.world.judges = dict()
    self.world.jCases = dict()
    for k in self.world.judgeNames:
      self.checkJudge(k)
      
    self.checkProofs()
      
  def makeDefFuns(self):
    result = dict()
    result["fv"] = FvFun()
    result["dom"] = DomFun()
    
    return result
      
  def checkProofs(self):
    if not self.world.proofAsts:
      return
  
    if not self.world.topProof:
      self.world.topProof = proof.Proof(self.world)
      self.world.proofs = []
  
    for p in self.world.proofAsts:
      self.world.proofs.append(self.checkProof(p, self.world.topProof, True, True))
        
  def checkProof(self, p, parent, tUp = False, top = False):
    result = proof.Proof(self.world, parent)
    result.transparentUp = tUp
    result.topProof = top
    self.execProof(result, p)
    self.checkProofBlock(p, result)
    
    self.world.proofMode.close()    
    return result
    
  def checkProofBlock(self, ast, parent):
    for c in ast.children:
      cResult = None
      if parent.checkedDone:
        self.addErr("Command after 'done' in proof mode", c)
        break
      if c.type == LEMMA:
        cResult = self.checkLemma(c, parent)
      elif c.type == PROOF_LINE:
        cResult = self.checkProofLine(c, parent)
      elif c.type == PROOF:
        cResult = self.checkProof(c, parent)
      else:
        self.addErr("Unexpected component in proof AST: found: " + BACK_LOOKUP[c.type], c)

  def execProof(self, cResult, ast):
    if cResult:
      try:
        pr = cResult.execute(None, self.world.proofMode)
        if pr and str(pr):
          self.log += "\n" + str(pr)
      except proof.ProofError as pe:
        self.addErr("Error in proof: " + str(pe), ast)

    
  def checkLemma(self, ast, parent):
    name = ast.name.val
    result = proof.Lemma(name, ast, parent)
    
    #conclusions
    for c in ast.conclusion:
      result.conclusion.append(self.checkPremise(c))
    #premises
    result.premises = []
    for l,p in ast.premises:
      prem = self.checkPremise(p)
      pl = proof.ProofLine(p, result)
      pl.label = l
      pl.args = [prem]
      pl.command = "premise"
      pl.results = pl.args
      if l:
        if l in result.labelled:
          self.addErr("Premise " + l + " already defined", ast)
        else:
          result.labelled[l] = pl
      else:
        result.unlabelled.append(pl)
      result.premises.append(prem)
    self.execProof(result, ast)
    #proof
    if ast.proof:
      result.proof = self.checkProof(ast.proof, result, True)
    
    if name in parent.lemmas:
      self.addErr("Lemma " + name + " already defined", ast)
    else:
      parent.lemmas[name] = result
      
    self.world.proofMode.close()    
    return result
   
  def checkCases(self, asts, parent):
    result = proof.Cases(parent)
    self.execProof(result, parent.ast)
    for c in asts:
      cResult = None
      if c.type == PROOF_CASE:
        cResult = self.checkCase(c, result)
      else:
        self.addErr("Unexpected component in proof AST: found: " + BACK_LOOKUP[c.type], c)
        
    self.world.proofMode.close()        
    return result
    
  def checkCase(self, ast, parent):
    result = proof.Case(ast, parent)
    result.label = ast.label
    self.execProof(result, ast)
    self.checkProofBlock(ast, result)
    
    self.world.proofMode.close()    
    return result
    
  def registerLabel(self, result, parent):
    if result.label:
      if result.label in parent.labelled:
        self.addErr("Line label " + result.label + " already defined", result.ast)
      else:
        parent.labelled[result.label] = result
    else:
      parent.unlabelled.append(result)
    
  def checkProofLine(self, ast, parent):
    result = proof.ProofLine(ast, parent)
    result.label = ast.label
    self.registerLabel(result, parent)
    
    #store the command
    result.command = ast.command
    result.star = False
    result.equals = False
    if result.command[-1] == "=":
      result.equals = True
      result.command = result.command[:-1]
    if result.command[-1] == "'":
      result.star = True
      result.command = result.command[:-1]
    result.args = []
    #check the arguments are correct for the command and store the args
    def appendArg(arg):
      if arg:
        result.args.append(arg)
    if result.command == "assume":
      #one or more labels or embeds
      map(lambda x: appendArg(self.checkRefOrEmbedArg(x, parent)), ast.args)
      if not result.args:
        self.addErr("Command 'assume' requires at least one argument", ast)
        return None
    elif result.command == "done":
      result.lemma = self.findLemma(result)
      if not result.lemma:
        self.addErr("Command 'done' must appear in the scope of a lemma or theorem", ast)
      #one or more labels
      map(lambda x: appendArg(self.checkRefArg(x, parent)), ast.args)
      if not result.args:
        self.addErr("Command 'done' requires at least one argument", ast)
      #elif len(result.args) != len(result.lemma.conclusion):
      #  self.addErr("Number of arguments to 'done' must match number of conclusions of " + result.lemma.name + ". Expected: " + len(result.lemma.conclusion) + ", found: " + len(result.args), ast)
      parent.checkedDone = True
    elif result.command == "state":
      #one or zero paths
      if ast.args:
        appendArg(self.checkRefArg(ast.args[0], parent, False))
        if len(ast.args) > 1:
          self.addErr("Command 'state' takes at most one argument", ast)
    elif result.command == "substeq":
      #one embed
      if len(ast.args) != 1:
        self.addErr("Command '" + ast.command + "' requires exactly one argument", ast)
      if ast.args:
        appendArg(self.checkEmbedArg(ast.args[0], parent))
    elif result.command == "clear":
      #zero or more labels (but keep the raw label)
      for x in ast.args:
        r = self.checkRefArg(x, parent)
        if r:
          result.args.append(x)
    elif result.command == "vars":
      #no args
      if ast.args:
        self.addErr("Command 'vars' takes no arguments", ast)      
    elif result.command in {"inconcat", "-inconcat", "-and", "-or", "-exists", "sym", "-fun", "weakin", "invert"}:
      #one label
      if len(ast.args) != 1:
        self.addErr("Command '" + ast.command + "' requires exactly one argument", ast)
      if ast.args:
        appendArg(self.checkRefArg(ast.args[0], parent))
    elif result.command in {"or"}:
      #one or more labels and zero or more embeds
      map(lambda x: appendArg(self.checkRefOrEmbedArg(x, parent)), ast.args)
      if not result.args:
        self.addErr("Command '" + ast.command + "' requires at least one argument", ast)
      elif not reduce(lambda x,y: x or y, map(lambda x: x.subtype == "ref", ast.args), False):
        self.addErr("Command '" + ast.command + "' requires at least one reference argument", ast)
    elif result.command in {"and"}:
      #one or more labels
      map(lambda x: appendArg(self.checkRefArg(x, parent)), ast.args)
      if not result.args:
        self.addErr("Command '" + ast.command + "' requires at least one argument", ast)
    elif result.command == "let":
      #one embed
      if len(ast.args) != 1:
        self.addErr("Command '" + ast.command + "' requires exactly one argument", ast)
      if ast.args:
        appendArg(self.checkEmbedArg(ast.args[0], parent))
    elif result.command in {"forall"}:
      #at least one variable literal
      map(lambda x: appendArg(self.checkVarArg(x, parent)), ast.args)
      if not result.args:
        self.addErr("Command '" + ast.command + "' requires at least one argument", ast)
    elif result.command in {"-forall"}:
      #one label and one or more variable literal
      if len(ast.args) < 2:
        self.addErr("Command '" + ast.command + "' requires at least two arguments", ast)
      appendArg(self.checkRefArg(ast.args[0], parent))
      map(lambda x: appendArg(self.checkVarArg(x, parent)), ast.args[1:])
      if len(result.args) < 2:
        self.addErr("Command '" + ast.command + "' requires at least two arguments", ast)
    elif result.command in {"exists"}:
      #one label and one or more variable literal
      if len(ast.args) < 2:
        self.addErr("Command '" + ast.command + "' requires at least two arguments", ast)
      appendArg(self.checkRefArg(ast.args[0], parent))
      map(lambda x: appendArg(self.checkVarArg(x, parent)), ast.args[1:])
      if len(result.args) < 2:
        self.addErr("Command '" + ast.command + "' requires at least two arguments", ast)
    elif result.command in {"implies"}:
      #at least one embed
      map(lambda x: appendArg(self.checkEmbedArg(x, parent)), ast.args)
      if not result.args:
        self.addErr("Command '" + ast.command + "' requires at least one argument", ast)
    elif result.command == "-implies":
      #at least one label
      map(lambda x: appendArg(self.checkRefArg(x, parent)), ast.args)
      if not result.args:
        self.addErr("Command '" + ast.command + "' requires at least one argument", ast)
    elif result.command in {"replace"}:
      #at least one label
      map(lambda x: appendArg(self.checkRefArg(x, parent)), ast.args)
      if not result.args:
        self.addErr("Command '" + ast.command + "' requires at least one argument", ast)
    elif result.command == "apply":
      if not ast.args:
        self.addErr("Command '" + ast.command + "' requires at least one argument", ast)
      #one name and zero or more labels
      appendArg(self.checkNameArg(ast.args[0], parent))
      map(lambda x: appendArg(self.checkRefArg(x, parent)), ast.args[1:])
    elif result.command == "fun":
      #two labels
      map(lambda x: appendArg(self.checkRefArg(x, parent)), ast.args)
      if len(result.args) != 2:
        self.addErr("Command 'fun' requires exactly two arguments", ast)
    elif result.command == "weakf":
      #two labels
      map(lambda x: appendArg(self.checkRefArg(x, parent)), ast.args)
      if len(result.args) != 2:
        self.addErr("Command 'weakf' requires exactly two arguments", ast)
    elif result.command == "sind":
      #one label
      if len(ast.args) != 1:
        self.addErr("Command 'sind' requires exactly one argument", ast)
      else:
        if ast.args:
          appendArg(self.checkRefArg(ast.args[0], parent))
        if not result.args:
          self.addErr("Command 'sind' requires exactly one argument", ast)
      result.lemma = self.findLemma(result)
      if not result.lemma:
        self.addErr("Command 'sind' must appear in the scope of a lemma or theorem", ast)
    else:
      self.addErr("Unknown command in proof mode: " + result.command, ast)
      return None
      
    self.execProof(result, ast)
    if ast.children:
      #cases
      self.checkCases(ast.children, result)

    return result

  def findLemma(self, x):
    if isinstance(x, proof.Lemma):
      return x
    elif x.parent:
      return self.findLemma(x.parent)
    else:
      return None

    
  def checkVarArg(self, arg, parent):
    if arg.subtype != "ref":
      self.addErr("Expected variable literal, found: " + arg.subtype, arg)
      return None
      
    parse = nparser.Parser(util.StringFileAdapter(arg.str))
    parse.recurLimit = 50
    try:
      result = parse.parseSyExp()
      if parse.errs:
        self.errs.extend(parse.errs)
      return self.handleExp(result)
    except Exception as e:
      self.addError("Error parsing embedded code: " + str(e), tok)
      return None

    
        
  def checkNameArg(self, arg, parent):
    if arg.subtype != "ref":
      self.addErr("Expected reference, found: " + arg.subtype, arg)
      return None
    if parent.lookupLemma(arg.str):
      return parent.lookupLemma(arg.str)
    elif arg.str in self.world.jCases:
      return self.world.jCases[arg.str]
    else:
      self.addErr("Unknown reference: " + arg.str, arg)
    
  def checkRefOrEmbedArg(self, arg, proof):      
    if arg.subtype == "ref":
      return self.checkRefArg(arg, proof)
    elif arg.subtype == "embed":
      return self.checkEmbedArg(arg, proof)
    else:
      self.addErr("Expected reference or embedded code, found: " + arg.subtype, arg)
      return None
      
    
  def checkRefArg(self, arg, proof, concrete = True):
    if arg.subtype != "ref":
      self.addErr("Expected reference, found: " + arg.subtype, arg)
      return None
    #lookup the referred proof line and return it
    result = proof.lookup(arg)
    if result:
      if concrete and not result.concrete:
        self.addErr("Expected concrete reference, found reference to proof or lemma", arg)
        return None
      return result
    else:
      self.addErr("Unknown reference: " + arg.str, arg)
      return None
  
  def checkEmbedArg(self, arg, proof):
    if arg.subtype != "embed":
      self.addErr("Expected embedded code, found: " + arg.subtype, arg)
      return None
    #check the embedded code
    return self.checkPremise(arg.ast)

      
  def checkSyntax(self):
    self.world.symbols = dict()
    self.world.terminals = []
    self.world.vars = []
    self.world.cases = []
    self.world.funs = self.makeDefFuns()
    self.world.mappings = dict()
    
    #put all the productions in the symbol table
    for ast in self.world.syntaxTrees:
      for c in ast.children:
        if c.type == PRODUCTION:
          s = Symbol(c)
          s.addNames(c.lhs)
          for n in c.lhs:
            self.world.symbols[n.val] = s
    
    
    #store each production in the symbol table
    for s in set(self.world.symbols.values()):
      #store each case including semantics
      for c in s.ast.children:
        cs = Case(s, c)
        for e in c.children:
          cs.addElement(self.makeSynElement(e))

        #check for a semantic binding in the case and fill it out from the symbol table
        cs.bindings = []
        for sem in c.semantic:
          if sem.subtype == "binds":
            t = self.makeIdTuple(sem)
            if t:
              cs.bindings.append(t)
              #check that the symbols mentioned in the binding occur in the production, if they do, then use the id in the production rule in the binding
              for i in range(len(t)):
                matched = False
                for c in cs.vars():
                  if t[i] == c:
                    t[i] = c
                    matched = True
                if not matched:
                  self.addErr("Variable in binding (" + t[i] + ") not found in case: " + ppSynExp(cs.ast), sem.children[i])
        
        cs.case = cs
        cs.caseMatch = cs.isSuperType(cs, [])

        s.addCase(cs)
        self.world.cases.append(cs)
      #add new terminals to the symbol table
      if s.ast.subtype in ("terminal", "variable"):
        self.world.terminals.append(s)
      if s.ast.subtype == "variable":
        self.world.vars.append(s)
        
      #handle semantic information (variables, mappings in environments)
      for sem in s.ast.semantic:
        if s.ast.subtype == "variable" and sem.subtype == "id":
          if sem.children[0] in self.world.symbols:
            s.variable = self.world.symbols[sem.children[0]]
          else:
            self.addErr("Semantic variable (" + sem.children[0] + ") not found", sem)
        if sem.subtype == "maps":
          t = self.makeIdTuple(sem)
          if t:
            s.maps = t
          ft = FunType([t[0].type([])], t[1].type([]))
          ft.symbol = s
          s.supertypes.append(ft)
          self.world.mappings[s.name] = (ft, s)
        elif sem.subtype == "global":
          s.globe = True
    
    self.world.symList = set(self.world.symbols.values())
    
    self.computeSubtypes()
    
    self.checkVars()
    
    
    #print symbols and subtypes
    #for s in set(self.world.symbols.values()):
    #  print s.name + " {" + ", ".join(map(lambda x: x.name, s.supertypes)) + "}"
    #print any actual subtypes
    #for s1 in set(self.world.symbols.values()):
    #  for s2 in set(self.world.symbols.values()):
    #    if s2.isSuperType(s1):
    #      print s2.name + " <: " + s1.name


  #check that wherever a variable is used, it's replacement can be used
  def checkVars(self):
    for v in self.world.vars:
      for c in self.world.cases:
        cvars = c.fv(v, env.Env()).vars()
        if v in cvars:
          if not c.subst(v.variable, v, env.Env(), self.world.symList).isSuperType(c.parent, self.world.symList):
            self.addErr("Unsound possible substitution of " + v.shortString() + " in " + c.shortString(), c.ast)
        lv = List(None)
        lv.arg = v
        if lv in cvars:
          lvv = List(None)
          lvv.arg = v.variable
          if not c.subst(lvv, lv, env.Env(), self.world.symList).isSuperType(c.parent, self.world.symList):
            self.addErr("Unsound possible substitution of " + v.shortString() + " in " + c.shortString(), c.ast)
      
    
  #actually computes supertypes, looks for s <: s2
  def computeSubtypes(self):
    for s in self.world.symList:
      #simple subtypes - symbol occurs as a case of the supertype
      for c in self.world.cases:
        if s != c.parent and self.matches(c, s):
          s.supertypes.append(c.parent)
      #compund subtypes - all cases of subtype occur as cases of the supertype, taking into account subtypes (including the current tentative one)
      #TODO seems to be broken for v <: e
      if len(s.cases) > 0:
        for s2 in set(self.world.symbols.values()):
          if s != s2 and len(s2.cases) > 0:
            oFlag = True
            s.supertypes.append(s2)
            oFlag = reduce(lambda x,c: x and reduce(lambda x, y: x or y, map(lambda x: self.matches(c, x), s2.cases), False), s.cases, True)
            if not oFlag:
              s.supertypes.remove(s2)
      #backward subtypes - if s has only one case and it is one symbol then it should be a supertype
      if len(s.cases) == 1 and len(s.cases[0].syntax) == 1 and isinstance(s.cases[0].syntax[0], Id):
        s.supertypes.append(s.cases[0].syntax[0].symbol)

    
    
  def checkJudge(self, name):
    pTree = self.world.judgeTrees[name][0]
    judge = JudgeDef(pTree)
    judge.name = pTree.val
    judge.envs = map(lambda x: self.strToSym(x, pTree.syntax), pTree.syntax.envs)
    judge.args = map(lambda x: self.strToSym(x, pTree.syntax), pTree.syntax.children)
    freshGen = Env()
    judge.envLabels = map(lambda x: freshGen.freshOld(x), judge.envs)
    judge.argLabels = map(lambda x: freshGen.freshOld(x), judge.args)
    
    
    self.world.judges[pTree.val] = judge
    
    for i in range(len(pTree.children)):
      self.checkJCase(pTree.children[i], judge, i)
      
    curIndex = len(pTree.children)
    
    #add any other asts which hold parts of the judgement
    for oTree in self.world.judgeTrees[name][1:]:
      #check the shapes match (ignore any latex or label)
      envs = map(lambda x: self.strToSym(x, oTree.syntax), oTree.syntax.envs)
      args = map(lambda x: self.strToSym(x, oTree.syntax), oTree.syntax.children)
      check = reduce(lambda x,y: x and y, map(lambda (x,y): x == y, zip(args, judge.args)), True)
      check = check and reduce(lambda x,y: x and y, map(lambda (x,y): x == y, zip(envs, judge.envs)), True)
      if not check:
        expectStr = "; ".join(map(lambda x: x.name, judge.envs)) + " |- " + "; ".join(map(lambda x: x.name, judge.args))
        foundStr = "; ".join(map(lambda x: x.name, envs)) + " |- " + "; ".join(map(lambda x: x.name, args))
        self.addErr("Shape of repeated judgment does not match original judgement: found: " + foundStr + ", expected: " + expectStr, oTree)

      #add any cases
      for i in range(len(oTree.children)):
        self.checkJCase(oTree.children[i], judge, curIndex + i)
      curIndex += len(oTree.children)
      
      
      
  def checkJCase(self, ast, parent, index):
    result = JCase(ast)
    result.parent = parent
    if ast.label:
      result.label = ast.label
    else:
      result.label = parent.name + str(index)
    result.name = result.label
         

    #store the shape as a mapping from the parent envs/args to the case ones
    #check the shape matches the parent shape
    if len(ast.val.envs) != len(parent.envs):
      self.addErr("Incorrect number of environments in case " + result.label + " of " + parent.name, ast.val)
      result.envs = []
    else:
      m = map(lambda (x, p): self.checkShapeElement(x, p), zip(ast.val.envs, parent.envLabels))
      result.envs, result.envMatches = ([ a for a,b in m ], [ b for a,b in m ])

    if len(ast.val.children) != len(parent.args):
      self.addErr("Incorrect number of arguments in case " + result.label + " of " + parent.name, ast.val)
      result.args = []
    else:
      m = map(lambda (x, p): self.checkShapeElement(x, p), zip(ast.val.children, parent.argLabels))
      result.args, result.argMatches = ([ a for a,b in m ], [ b for a,b in m ])
      
    vars = [] #collect all vars in the premises

    #rename non-unique variables and add corresponding equality constraints
    names = dict()
    curEnv = env.Env()
    for i in range(len(result.envs)):
      e = result.envs[i]
      if e in names and e.vars():
        result.envs[i] = curEnv.freshOld(e)
        result.envMatches[i] = result.envs[i].isSuperType(parent.envLabels[i], self.world.symList)
        p = judge.Equality(None)
        p.nt = False
        p.lhs = e
        p.rhs = result.envs[i]
        vars.append(p.lhs)
        vars.append(p.rhs)
        result.premises.append(p)
      else:
        names[e] = e
    for i in range(len(result.args)):
      a = result.args[i]
      if a in names and a.vars():
        result.args[i] = curEnv.freshOld(a)
        result.argMatches[i] = result.args[i].isSuperType(parent.argLabels[i], self.world.symList)
        p = judge.Equality(None)
        p.nt = False
        p.lhs = a
        p.rhs = result.args[i]
        vars.append(p.lhs)
        vars.append(p.rhs)
        result.premises.append(p)
      else:
        names[a] = a
    
    #store and check the premises
    for p in ast.children:
      sp = self.checkPremise(p)
      if sp:
        result.premises.append(sp)
        vars.extend(sp.vars())
      
    #collect together vars bound in the conclusion
    bound = []
    bound.extend(filter(lambda x: util.interestingRoot(x), sum(map(lambda x: x.vars(), result.envs), [])))
    bound.extend(filter(lambda x: util.interestingRoot(x), sum(map(lambda x: x.vars(), result.args), [])))
    result.bound = []
    result.globals = []
    result.freeConc = []
    for b in bound:
      if b not in result.bound:
        result.bound.append(b)
        #check if they are bound in the premises
        if util.interestingRoot(b) and b not in vars and b not in result.freeConc:
          result.freeConc.append(b)
      elif self.globalRoot(b) and b not in result.globals:
        result.globals.append(b)
        
    

    #compute the free vars (variables that are used in the premises, but not the conc)
    result.free = []
    for b in vars:
      if util.interestingRoot(b) and b not in result.free and b not in result.bound:
        result.free.append(b)
      elif self.globalRoot(b) and b not in result.globals:
        result.globals.append(b)
            
    
    parent.cases.append(result)
    if result.label in self.world.jCases:
      self.addErr("Case " + result.label + " already defined", ast)
    else:
      self.world.jCases[result.label] = result
    
    
    
    
  
  def globalRoot(self, var):
    if isinstance(var, Id):
      return var.symbol.globe
    if isinstance(var, List):
      return self.globalRoot(var.arg)
    if isinstance(var, IndexVar):
      return False

      
      
  def checkPremise(self, ast):
    result = None
    if ast.subtype == "eq":
      result = Equality(ast)
      result.lhs = self.handleExp(ast.lhs)
      result.rhs = self.handleExp(ast.rhs)
      if result.rhs.type(self.world.symList).isSuperType(result.lhs.type(self.world.symList), self.world.symList):
        result.super = result.lhs
        result.sub = result.rhs
      elif result.lhs.type(self.world.symList).isSuperType(result.rhs.type(self.world.symList), self.world.symList):
        result.super = result.rhs
        result.sub = result.lhs
      else:
        self.addErr("Type mismatch in equality, found: " + result.lhs.type(self.world.symList).shortString() + " and " + result.rhs.type(self.world.symList).shortString(), ast)
    elif ast.subtype == "judge":
      result = Judge(ast)
      if ast.val not in self.world.judges:
        result.defn = None
        self.addErr("Judgement defintion not found: '" + ast.val + "'", ast)
      else:
        result.defn = self.world.judges[ast.val]
        
      result.envs = map(lambda x: self.handleExp(x), ast.envs)
      result.args = map(lambda x: self.handleExp(x), ast.children)
      
      if result.defn:
        #check the envs and args have the right type
        if len(result.defn.envs) != len(result.envs):
          self.addErr("Mismatch in number of environments for judgement " + result.defn.name + ": expected: " + str(len(result.defn.envs)) + ", found: " + str(len(result.envs)), ast)
        else:
          result.envMatches = []
          for (a,b) in zip(result.envs, result.defn.envLabels):
            m = a.isSuperType(b, self.world.symList)
            result.envMatches.append(m)
            a.judgePromo = False
            if not m:
              if isinstance(a.type(self.world.symList), List) and self.matches(a.type(self.world.symList).arg, b, self.world.symList):
                a.judgePromo = True
              else:
                a.judgePromo = False
                self.addErr("Type mismatch in environment of judgement, expected: " + b.shortString() + ", found: " + a.shortString(), a.ast)
        if len(result.defn.args) != len(result.args):
          self.addErr("Mismatch in number of arguments for judgement " + result.defn.name + ": expected: " + str(len(result.defn.args)) + ", found: " + str(len(result.args)), ast)
        else:
          result.argMatches = []
          for (a,b) in zip(result.args, result.defn.argLabels):
            m = a.isSuperType(b, self.world.symList)
            result.argMatches.append(m)
            a.judgePromo = False
            if not m:
              if isinstance(a.type(self.world.symList), List) and self.matches(a.type(self.world.symList).arg, b, self.world.symList):
                a.judgePromo = True
              else:
                self.addErr("Type mismatch in argument of judgement, expected: " + b.shortString() + ", found: " + a.shortString(), a.ast)
    elif ast.subtype == "in":
      result = InTest(ast)
      result.lhs = self.handleExp(ast.lhs)
      result.rhs = self.handleExp(ast.rhs)
      rType = result.rhs.type(self.world.symList)
      st = self.isListType(rType)
      if st:
        if isinstance(st, Symbol):
          flag = reduce(lambda x,y: x or y, map(lambda c: result.lhs.type(self.world.symList).isSuperType(c.type(self.world.symList), self.world.symList), st.cases), False)
          if not flag:
            self.addErr("Type mismatch in inclusion test, found: " + result.lhs.type(self.world.symList).shortString() + " and " + rType.shortString(), ast)
        else:
          rat = st.arg
          if not result.lhs.type(self.world.symList).isSuperType(rat, self.world.symList):
            self.addErr("Type mismatch in inclusion test, found: " + result.lhs.type(self.world.symList).shortString() + " and " + rType.shortString(), ast)
      else:
        self.addErr("Right-hand side of inclusion test must have list or set type, found: " + rType.shortString(), ast)

    #premise might be negated negation
    result.nt = ast.nt
    return result
    
  
  #check that an id matches a symbol and return the match
  def checkShapeElement(self, el, sym):
    result = self.handleExp(el)
    m = result.isSuperType(sym, self.world.symList)
    if not m:
      self.addErr("Argument in case does not match shape, expected: " + sym.type(self.world.symList).shortString() + ", found: " + result.shortString(), el)
    return result, m
    
  
  #convert an expression ast into a semantic equivalent  
  def handleExp(self, e):
    if e.type == ID:
      if e.val in self.world.symbols.keys():
        return Id(e, self.world.symbols[e.val])
      else:
        self.addErr("Symbol not found: " + e.val, e)
        return Id(e, ErrSym())
    elif e.type == ELIPSES:
      return Elipses(e)
    elif e.type == LIST:
      result = List(e)
      if e.val:
        result.arg = self.handleExp(e.val)
      else:
        result.arg = Empty(e)
      return result
    elif e.type != EXP:
      self.addErr("Expected expression, found: " + BACK_LOOKUP[e.type], e)
      return ErrSym()
    elif e.subtype == "fun app":
      result = FunApp(e)
      result.args = map(lambda x: self.handleExp(x), e.rhs)

      if e.lhs.type == ID and e.lhs.val in self.world.funs:
        #a user-defined or built-in function
        result.fun = self.world.funs[e.lhs.val]
        ft = result.fun.type(self.world.symList)
        #check we have the right number of args wrt the def
        if len(result.args) != len(ft.lhs):
          self.addErr("Incorrect number of arguments to " + result.fun.name + "; found: " + str(len(result.args)) + ", expected: " + str(len(ft.lhs)), e)
        else:
          #infer type variables
          
          matches = map(lambda (s,o): s.type(self.world.symList).isSuperType(o, self.world.symList, True), zip(result.args, ft.lhs))
          def flatten(x):
            if x:
              return sum(map(lambda y: y.flatMatches(), x.trans), [])
            else:
              return []
          matches = sum(map(flatten, matches), [])
          varMatches = dict()
          for m in matches:
            if m.id in ft.vars:
              if m.id not in varMatches:
                varMatches[m.id] = []
              varMatches[m.id].append(m)
          
          varResults = dict()
          for v in ft.vars:
            if v not in varMatches:
              self.addErr("Type variable " + v.shortString() + " could not be inferred", e)
              continue
            ms = varMatches[v]
            vr = ms[0].other
            for o in ms[1:]:
              if o.other != vr:
                self.addErr("Multiple inferences for type variable " + v.shortString(), e)
            varResults[v] = vr
          result.typeVarRes = varResults
          ft = result.fun.type(self.world.symList)
          ftl = ft.lhs
          for v in varResults:
            ftl = map(lambda x: x.replace(v, varResults[v]), ftl)
          #check arg types
          if not reduce(lambda x,y: x and y, map(lambda (s,o): s.type(self.world.symList).isSuperType(o, self.world.symList, False), zip(result.args, ftl)), True):
            self.addErr("Type mismatch in function argument; expected: " + ft.shortString(), e)
      else:
        #a mapping      
        result.fun = self.handleExp(e.lhs)     
      
        ft = self.isFunType(result.fun.type(self.world.symList))
        if not ft:
          self.addErr("Expression in function position of function application does not have function type (" + result.fun.type(self.world.symList).shortString() + ")", e.lhs)
          result.fun = ErrSym()
        else:
          #check we have only one arg
          if not len(result.args) == 1:
            self.addErr("Mappings may take only one argument, found " + str(len(result.args)) + " arguments", e)
          #check arg types
          if result.args and not result.args[0].type(self.world.symList).isSuperType(ft.lhs[0], self.world.symList):
            self.addErr("Type mismatch in function argument; expected: " + ft.shortString() + ", found: " + result.args[0].type(self.world.symList).shortString(), e)
          if hasattr(ft, "symbol"):
            result.funInfo = ft.symbol
      
      return result
    elif e.subtype == "sequence":
      if len(e.children) == 0:
        return Empty(e)
      if len(e.children) == 1:
        return self.handleExp(e.children[0])

      result = Seq(e)
      result.syntax = map(self.handleExp, e.children)
      #check if the sequence matches a case
      result.case = None
      for c in self.world.cases:
        m = result.isSuperType(c, self.world.symList)
        #if c.parent.name == "M":
          #print m
          #print result.longString(), "      ",  c.longString()
          #print self.world.symList
        if m:
          result.case = c
          result.caseMatch = m
        
      
      return result
    elif e.subtype == "concat":
      if len(e.children) == 1:
        return self.handleExp(e.children[0])
      
      result = Concat(e)
      result.elements = map(self.handleExp, e.children)
      type = BottomType()
      for i in range(len(result.elements)):
        el = result.elements[i]
        #don't insert cons cells, better to promote in typing
        #if not self.isListType(el.type(self.world.symList)):
        #  #insert a list constructor
        #  result.elements[i] = Cons(el)
        #  el = result.elements[i]
        if el.type(self.world.symList).isSuperType(type, self.world.symList):
          continue
        elif type.isSuperType(el.type(self.world.symList), self.world.symList):
          type = el.type(self.world.symList)
          if not util.isListType(type, self.world.symList):
            temp = type
            type = List(None)
            type.arg = temp
        else:
          self.addErr("Incompatible type in concatenation: " + ppExp(e) + ", found: " + el.type(self.world.symList).shortString(), el.ast)
      result.typeF = type
      return result
    elif e.subtype == "subst":
      result = Subst(e)
      result.lhs = self.handleExp(e.lhs)
      result.rhs = self.handleExp(e.rhs)
      result.body = self.handleExp(e.val)
      lhsType = result.lhs.type(self.world.symList)
      if isinstance(result.rhs, List):
        if not isinstance(result.lhs, List):
          self.addErr("Cannot substitute non-list (" + result.lhs.shortString() + ") for list (" + result.rhs.shortString() + ")", e)
        else:
          lhsType = result.lhs.arg.type(self.world.symList)
        rhsSemantic = result.rhs.arg.symbol.variable
      else:
        rhsSemantic = result.rhs.symbol.variable
      if not lhsType.isSuperType(rhsSemantic, self.world.symList):
        self.addErr("Substituting value is not a subtype of substituted variable", e)
      return result
    elif e.subtype == "subscript":
      result = Subscript(e)
      result.lhs = self.handleExp(e.lhs)
      result.rhs = self.handleSubscript(e.rhs)
      #check rhs has index type
      if not self.isIndexType(result.rhs.type(self.world.symList)):
        self.addErr("Subscript is not an index: " + result.rhs.shortString(), e.rhs)
      return result
    else:
      self.addErr("Unexpected expression: " + e.subtype, e)
      return ErrSym()
  
  #handle an expression in index position
  def handleSubscript(self, e):  
    #either a variable or a constant int
    if e.type == ID:
      result = IndexVar(e)
      result.name = e.val
      return result
    elif e.type == INT:
      result = Num(e)
      result.val = e.val
      return result
    else:
      self.addErr("Unexpected expression in index position: " + e.subtype, e)
      return ErrSym()
  
  def strToSym(self, st, ast):
    if isinstance(st, Ast) and st.type == LIST:
      #a list of names
      result = List(st)
      if not isinstance(st.val, Seq):
        result.arg = self.strToSym(st.val, st)
      elif len(st.val.children) == 1:
        result.arg = self.strToSym(st.val.children[0], st)
      elif len(st.val.children) == 0:
        result.arg = Empty(str)
      else:
        result.arg = Seq(st)
        for c in st.val.children:
          result.arg.syntax.append(self.strToSym(c, st))

      return result      
      
    if st in self.world.symbols.keys():
      return self.world.symbols[st]
    else:
      self.addErr("Symbol not found: " + st, ast)
      return ErrSym()
    
  def isFunType(self, t):
    return util.isFunType(t, self.world.symList)
   
    
    
  def isListType(self, t):
    return util.isListType(t, self.world.symList)
    
    
    
  def isIndexType(self, t):
    return t if isinstance(t, IndexType) else None
   
   
   
  def makeIdTuple(self, sem):
    result = []
    for c in sem.children:
      m = self.matchSynId(c)
      if m:
        result.append(m)
      else:
        self.addErr("Semantic variable (" + ppExp(c.val) + ") not found", c)
        result.append(ErrSym())
         
    return result
    
    
  def matchSynId(self, ast):  
    if ast.type == ID and ast.val in self.world.symbols:
      return Id(ast, self.world.symbols[ast.val])
      
    if ast.type == LIST:
      nest = self.matchSynId(ast.val)
      if nest:
        result = List(ast)
        result.arg = nest
        return result
      
    return None
    
    
    
    
  def makeSynList(self, ast):
    result = List(ast)
    result.arg = Case(result, ast)
    for e in ast.children:
      sym = self.makeSynElement(e)
      if sym:
        result.arg.addElement(sym)
    return result


        
  def makeSynElement(self, e):
    if e.type == ID:
      if e.val in self.world.symbols:
        return Id(e, self.world.symbols[e.val])
      else:
        #add all terminals to list of terminals
        self.addTerminal(e.val)
        return Id(e, self.world.symbols[e.val])
    elif e.type == SYN_SEQ:
      return self.makeSynList(e)
    else:
      self.addErr("Unknown ast in production", e)
      return Id(e, ErrSym)


  #effectively the subsumption rule
  def matches(self, e, type, symbols = []):
    return e.type(self.world.symList).isSuperType(type, self.world.symList)
    
    
    
    
  def addErr(self, msg, ast):
    if ast:
      tok = ast.tok
      self.errs.append(Err(msg, tok, tok.line, tok.col))
    else:
      self.errs.append(Err(msg, None, 0, 0))
    
  #add an 'anonynmous' terminal
  def addTerminal(self, s):
    sym = Symbol(None)
    sym.setName(s)
    self.world.symbols[s] = sym
    self.world.terminals.append(sym)
    