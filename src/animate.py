#TODO - see help (eval, assignment, using variables in commands, utils)

#TODO 
  #eval with
#TODO eval - env:
  #bounds into env after subscripting
  #globals in env, and globals in general

  
    
from nparser import Parser
from nchecker import Checker
from env import Env
import util


class Animate:
  def __init__(self, world):
    self.world = world
    self.oldWorld = world
    self.passes = 0
    self.fails = 0
    self.curEnv = Env()
    
  def dispatch(self, input):
    words = input.split(" ")
    if len(words) == 0:
      return ""
    cmd = words[0]
    args = []
    if len(words) > 1:
      input = input.replace("\;", "__colon")
      args = map(lambda x: x.strip().replace("__colon", "\;"), input[len(cmd)+1:].split(";"))
      

    if cmd == "exit":
      tests = ""
      if self.passes+self.fails > 0:
        tests = "Assertions failed: " + str(self.fails) + ", passed: " + str(self.passes) + ", total: " + str(self.passes+self.fails)
      return "_exit" + tests
    if cmd in ("help", "symbols", "judges"):
      return getattr(self, cmd)()
    if cmd in ("ids", "names", "sup", "cases"):
      if len(args) == 1:
        return getattr(self, cmd)(args[0])
      else:
        return "Error, " + cmd + " takes one argument"
    if cmd == "assert":
      if len(args) >= 2:
        return self.assertS(args[0], args[1:])
      else:
        return "Error, assert requires at least two arguments"
    if cmd in ("eval", "assume", "type", "env", "subst", "fv"):
      return getattr(self, cmd)(args)
    if cmd in ("match", "subtype"):
      if len(args) == 2:
        return getattr(self, cmd)(args[0], args[1])
      else:
        return "Error, " + cmd + " takes two arguments"
        
    
    if cmd:
      return "Unknown command, for help, use 'help', to leave animation mode, use 'exit'"
    
    return ""
    
  def match(self, sym, exp):
    try:
      sym = self.parseSynExp(sym)
      exp = self.parseSemExp(exp)
    except AnimError as e:
      return str(e)
      
    m = exp.isSuperType(sym,set(self.world.symbols.values()))
    if m:
      return "Yes(" + sym.longString() + "; " + exp.longString() + "; " + m.shortString() + ")"
    else:
      return "No(" + sym.longString() + "; " + exp.longString() + ")"
    
  def subtype(self, e1, e2):
    try:
      e1 = self.parseSynExp(e1)
      e2 = self.parseSynExp(e2)
    except AnimError as e:
      return str(e)
      
    if e1.isSuperType(e2, self.world.symList):
      return "Yes"
    else:
      return "No"
      
  def assertS(self, result, rest):
    test = self.dispatch("; ".join(rest))
    if test.startswith(result):
      self.passes += 1
      return ""
    else:
      self.fails += 1
      return "Failed assertion: '" + "; ".join(rest) + "'\n expected: '" + result + "'\n found: '" + test + "'"
    
  def assign(self, cmd):
    pass
       
  def help(self):
    return """Animation mode commands:
  help               print this message
  exit               leave animation mode

  eval p [with cs]   evaluate the meta-expression p
                       using the given free variable bindings
                       c ::= x '=' e
                       cs ::= cs ';' c | []
  assume p           add p to the environment if not p cannot be proved
  env [clear]        display the current environment 
                       clear = clear environment
  type e             the type of e
  ids e              the ids in e
  names e            the names in e
  match sym; s       try to match the expression s to the symbol sym
  subtype t1; t2     tries t1 <: t2
  sup sym            prints all super-symbols of sym
  symbols            prints the symbol table
  judges             prints the table of judgements
  subst [s]          print the definition information for the variable s (no s = all variables)

  x = s              assign the syntactic expression s to x TODO
  x = eval e         assign the result of eval e to x TODO
  x = type e         assign the result of type e to x TODO
  .x                 use the value stored in x TODO
  
  assert r; m        assert that m evaluates to the given result
"""

  def parseSemExp(self, s):
    parse = Parser(util.StringFileAdapter(s))
    parse.recurLimit = 50
    ast = parse.parseSemExp()
    if parse.errs:
      result = "Parsing errors:\n"
      for e in parse.errs:
        result +=  e.longMsg() + "\n"
      result +=  "\nTotal: " + str(len(parse.errs)) + " errors\n" 
      raise AnimError(result)

    check = Checker(self.world)
    sem = check.handleExp(ast)
    if check.errs:
      result = "Checking errors:\n"
      for e in check.errs:
        result +=  e.longMsg() + "\n"
      result +=  "\nTotal: " + str(len(check.errs)) + " errors\n" 
      raise AnimError(result)

    return sem    

  def parseSynExp(self, s):    
    parse = Parser(util.StringFileAdapter(s))
    parse.recurLimit = 50
    ast = parse.parseSubSeq()
    if parse.errs:
      result = "Parsing errors:\n"
      for e in parse.errs:
        result +=  e.longMsg() + "\n"
      result +=  "\nTotal: " + str(len(parse.errs)) + " errors\n" 
      raise AnimError(result)

    check = Checker(self.world)
    sem = check.handleExp(ast)
    if check.errs:
      result = "Checking errors:\n"
      for e in check.errs:
        result +=  e.longMsg() + "\n"
      result +=  "\nTotal: " + str(len(check.errs)) + " errors\n" 
      raise AnimError(result)

    return sem    
    
  def parsePremise(self, s):
    parse = Parser(util.StringFileAdapter(s))
    parse.recurLimit = 50
    try:
      ast = parse.parsePremise()
      if parse.errs:
        result = "Parsing errors:\n"
        for e in parse.errs:
          result +=  e.longMsg() + "\n"
        result +=  "\nTotal: " + str(len(parse.errs)) + " errors\n" 
        raise AnimError(result)

      check = Checker(self.world)
      sem = check.checkPremise(ast)
      if check.errs:
        result = "Checking errors:\n"
        for e in check.errs:
          result +=  e.longMsg() + "\n"
        result +=  "\nTotal: " + str(len(check.errs)) + " errors\n" 
        raise AnimError(result)

      return sem    
    except Exception as e:
      raise AnimError(str(e))
    
  

    
  def parseSym(self, s):
    if s in self.world.symbols:
      return self.world.symbols[s]
      
    raise AnimError(s + " not a symbol")
       
  def type(self, s):
    cmd = "; ".join(s)
    try:
      if reduce(lambda x, y: x or y, map(lambda x: x in cmd, ('=', 'in', '|-')), False):
        cmd = self.parsePremise(cmd)
      else:
        cmd = self.parseSemExp(cmd)
      return cmd.type(self.world.symList).shortString()
    except AnimError as e:
      return str(e)
    
  def ids(self, s):
    try:
      return self.parseSemExp(s).ids()
    except AnimError as e:
      return str(e)
    
  def names(self, s):
    try:
      return self.parseSemExp(s).names()
    except AnimError as e:
      return str(e)

      
  def eval(self, cmd):
    try:
      cmd = "; ".join(cmd)
      wth = None
      if "with" in cmd:
        wIndex = cmd.find("with")
        wStr = cmd[wIndex+5:]
        cmd = cmd[:wIndex-1]
        ws = wStr.split(";")
        ws = map(lambda x: x.strip(), ws)
        wes = map(lambda x: self.parsePremise(x), ws)
        wth = dict()
        for w in wes:
          if w.__class__.__name__ == "Equality":
            if w.lhs not in wth:
              wth[w.lhs] = []
            wth[w.lhs].append(w.rhs)

      if reduce(lambda x, y: x or y, map(lambda x: x in cmd, ('=', 'in', '|-')), False):
        cmd = self.parsePremise(cmd)
      else:
        cmd = self.parseSemExp(cmd)
      if wth:
        result = cmd.eval(self.curEnv, self.world.symList, wth)
      else:
        result = cmd.eval(self.curEnv, self.world.symList)
      try:
        return result.shortString()
      except:
        return str(result)
    except AnimError as e:
      return str(e)
      
  def assume(self, cmd):
    try:
      cmd = "; ".join(cmd)
      if reduce(lambda x, y: x or y, map(lambda x: x in cmd, ('=', 'in', '|-')), False):
        cmd = self.parsePremise(cmd)
      else:
        return "False"
      cmd.nt = not cmd.nt
      result = cmd.eval(self.curEnv, self.world.symList)
      if result:
        return "False"
      else:
        cmd.nt = not cmd.nt
        cmd.eval(self.curEnv, self.world.symList, assume = True)
        return "True"
    except AnimError as e:
      return str(e)
   
  def env(self, cmd):
    if cmd and cmd[0] == "clear":
      self.curEnv = Env()
      return "Cleared environment"

    return self.curEnv.shortString()
    
  def subst(self, arg):
    if arg:
      for v in self.world.vars:
        if arg[0] in map(lambda x: x[0], v.names):
          return util.subst(v, self.world.symList).shortString()
      return "Variable not found: " + arg[0]
      
    result = ""
    for v in self.world.vars:
      result += util.subst(v, self.world.symList).shortString()
      
    return result
    
  def fv(self, arg):
    if arg:
      for v in self.world.vars:
        if arg[0] in map(lambda x: x[0], v.names):
          return util.fv(v, self.world.symList).shortString()
      return "Variable not found: " + arg[0]
      
    result = ""
    for v in self.world.vars:
      result += util.fv(v, self.world.symList).shortString()
      
    return result

    
  def sup(self, sym):
    try:
      sym = self.parseSym(sym)
      return "Immediate: " + str(map(lambda x: x.shortString(), sym.supertypes)) + "\nTransitive: " + str(map(lambda x: x.shortString(), sym.superClasses([],[])))
    except AnimError as e:
      return str(e)


  def symbols(self):
    result = ""
    for k in self.world.symbols:
      result += str(k) + " "
      sym = self.world.symbols[k]
      result += "(" + "; ".join(map(lambda x: x[0], sym.names)) + ")  ::=  " 
      result += " | ".join(map(lambda x: x.shortString(), sym.cases)) + "  {" 
      result += ", ".join(map(lambda x: x.shortString(), sym.supertypes)) + "}\n"
      
    return result
    
  def judges(self):
    result = ""
    for k in self.world.judgeNames:
      result += str(k) + " -> "
      sym = self.world.judges[k]
      result += "'" + sym.name + "' "
      result += "; ".join(map(lambda x: x.shortString(), sym.envs)) + " |- " 
      result += "; ".join(map(lambda x: x.shortString(), sym.args)) + "\n"
      
    return result
    
  def cases(self, name):
    if name not in self.world.judgeNames:
      return "Judgement not defined: " + name
    j = self.world.judges[name]
    result = ""
    for c in j.cases:
      result += c.label + ": "
      result += "; ".join(map(lambda x: x.shortString(), c.envs)) + " |- " 
      result += "; ".join(map(lambda x: x.shortString(), c.args)) + "\n"
      result += "  free: {" + ", ".join(map(lambda x: x.shortString(), c.free)) + "}\n"
      result += "  bound: {" + ", ".join(map(lambda x: x.shortString(), c.bound)) + "}\n"
      result += "  global: {" + ", ".join(map(lambda x: x.shortString(), c.globals)) + "}\n"
    return result

  
    
  def dom(self, cmd):
    pass
    
    
    

    
class AnimError(Exception):
  def __init__(self, msg):
    Exception.__init__(self, msg)



    
    