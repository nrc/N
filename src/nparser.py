#parse a n file


from ast import *
import util

COMMENT = "//"
RESERVED = ("|-", "->", "::=", "=>", "...", "((", ";", "[", "]", ",", "|", "=", "~", "(", ")", "_", "/")
SPECIAL = ("\"", "[[", "]]", "{", "}")
SYMBOLS = ("!", "$", "%", "^", "&", "*", "-", "+", "\\", ":", "@", "~", "?", "<", ">", ".", "#")
SYM_TEXT = ("EXCLAME", "DOLLAR", "PERCENT", "CARET", "AMPERSAND", "ASTERISK", "MINUS", "PLUS", "BACKSLASH", "COLON", "SNAIL", "TILDA", "QUESTION", "LANGLE", "RANGLE", "DOT", "HASH")
SYM_MAP = dict(zip(SYMBOLS, SYM_TEXT))
KEYWORDS = ("syntax", "var", "judge", "case", "env", "apply", "not", "in", "proof")
SEM_KEYWORDS = ("binds", "in", "ints", "global")
PROOF_KEYWORDS = ("lemma", "where", "assume", "done'", "done", "proof", "case", "by", "sind", "state", "clear", "invert'", "invert", "and", "or", "implies", "-and", "-or", "-implies", "apply", "vars", "exists", "-exists", "forall", "-forall", "replace", "replace'", "weakf", "sym", "fun", "-fun", "weakin", "let", "apply=", "done=", "done'=", "substeq", "inconcat", "-inconcat")
PROOF_RESERVED = (".", "{", "}", ";", "*", "\"")
MODS = ("'", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9")
PREFIXES = set([x[0] for x in SYMBOLS + RESERVED + SPECIAL + MODS])
PROOF_PREFIXES = set([x[0] for x in PROOF_RESERVED[1:]])


class Parser:
  def __init__(self, src):
    self.lex = Lexer(src, self)
    self.errs = []
    self.tokStack = []
    self.newLine = False
    
  def parseTop(self, world):
    #self.printTokenStream()
    #return
    self.world = world
    result = Ast(PROGRAM, self.peek())
    
    #try:
    while True:
      tok = self.nextToken()
      
      try:
        if tok.type == TokType.EOF:
          break
        elif tok.type == TokType.NEW_LINE:
          continue
        elif tok.type == TokType.LATEX_STRING:
          result.addChild(self.parseLatex(tok))
          self.matchOptNL()
        elif self.isKW(tok, "syntax"):
          result.addChild(self.parseSyntax())
        elif self.isKW(tok, "judge"):
          result.addChild(self.parseJudge())
        elif self.isKW(tok, "proof"):
          self.pushBack(tok)
          proof = self.parseProof()
          result.addChild(proof)
          self.world.proofAsts.append(proof)
        else:
          self.unexpect(tok)
      except PanicMode:
        self.recover()
    #except Exception as e:
    #  raise Exception("Unexpected error: " + str(e))
        
    return result
    
  def printTokenStream(self):
    tok = self.nextToken()
    while tok.type != TokType.EOF:
      print tok.shortString()
      tok = self.nextToken()
      
    
  #get the next token without looking at the stack
  def nextTokenPop(self):  
    tok = self.lex.nextToken()
    while tok.type == TokType.COMMENT:
      tok = self.lex.nextToken()
    return tok      
    
  def nextToken(self):
    if self.tokStack:
      return self.tokStack.pop()
      
    return self.checkNewLine(self.nextTokenPop())
    
  def checkNewLine(self, tok):
    if tok.type == TokType.NEW_LINE:
      if self.newLine:
        return self.checkNewLine(self.nextTokenPop())
      else:
        self.newLine = True
    else:
      self.newLine = False
      
    return tok
    
  def peek(self):
    result = self.nextToken()
    self.pushBack(result)
    return result
    
  def pushBack(self, tok):
    self.tokStack.append(tok)
  
  
  
  
  def searchLine(self, kw):
    seen = []
    tok = self.nextToken()
    seen.insert(0, tok)
    while tok.type != TokType.NEW_LINE and tok.type != TokType.EOF and tok.type != TokType.END_BLOCK:
      if self.isKW(tok, kw):
        self.tokStack.extend(seen)
        return True
      tok = self.nextToken()
      seen.insert(0, tok)
      
    self.tokStack.extend(seen)
    return False
  
  def parseProof(self):
    result = Ast(PROOF, self.peek())
    self.matchKW("proof")
    self.matchOptNL()
    self.matchType(TokType.START_BLOCK)
    while self.peek().type not in (TokType.END_BLOCK,TokType.EOF):
      try:
        result.addChild(self.parseProofLine())
      except PanicMode as e:
        self.recover()
    self.matchType(TokType.END_BLOCK)
    self.matchOptNL()
    
    return result
  
  def parseProofCase(self):
    result = Ast(PROOF_CASE, self.peek())
    self.matchKW("case")
    #opt match a label
    result.label = ""
    if self.isId(self.peek()):
      tok = self.nextToken()
      result.label = tok.str
    self.matchOptNL()
    self.matchType(TokType.START_BLOCK)
    while self.peek().type not in (TokType.END_BLOCK,TokType.EOF):
      try:
        result.addChild(self.parseProofLine())
      except PanicMode as e:
        self.recover()
    self.matchType(TokType.END_BLOCK)
    self.matchOptNL()
    
    return result
  
  
  def parseProofLine(self):
    if self.isKW(self.peek(), "proof"):
      return self.parseProof()
    elif self.isKW(self.peek(), "lemma"):
      return self.parseLemma()
    elif self.isKW(self.peek(), "case"):
      return self.parseProofCase()
    else:
      tok = self.nextToken()
      #opt match a label
      label = ""
      if self.isId(tok) and tok.str[-1] == ".":
        label = tok.str[:-1]
        tok = self.nextToken()
      result = Ast(PROOF_LINE, tok)
      result.label = label
      #opt match a command
      if tok.type == TokType.KEYWORD:
        result.command = tok.str
        tok = self.nextToken()
      else:
        result.command = "assume"
      #match params separated by semi-colons
      self.pushBack(tok)
      result.args = self.matchProofArgList()

      self.matchOptNL()
      if self.peek().type == TokType.START_BLOCK:
        self.matchType(TokType.START_BLOCK)
        while self.peek().type not in (TokType.END_BLOCK,TokType.EOF):
          try:
            result.addChild(self.parseProofLine())
          except PanicMode as e:
            self.recover()
        self.matchType(TokType.END_BLOCK)            
        self.matchOptNL()
        
      return result
  
  def matchEmbed(self):
    tok = self.nextToken()
    #parse the embedded N syntax and store
    parse = Parser(util.StringFileAdapter(tok.str))
    parse.recurLimit = 50
    try:
      result = parse.parsePremise()
      if parse.errs:
        self.errs.extend(parse.errs)
      return result
    except Exception as e:
      self.addError("Error parsing embedded code: " + str(e), tok)
      return None
  
  def matchProofArgList(self):
    result = []
    peek = self.peek()
    first = True
    while peek.type in (TokType.ID, TokType.KEYWORD, TokType.PROOF_EMBED):
      if not first:
        self.matchKW(";")
        peek = self.peek()
        
      arg = Ast(PROOF_ARG, peek)
      if peek.type == TokType.PROOF_EMBED:
        arg.subtype = "embed"
        arg.ast = self.matchEmbed()
        
      elif peek.type == TokType.ID:
        tok = self.nextToken()
        str = tok.str
        strp = 0
        arg.subtype = "ref"
        arg.str = str
        #parse the ref path
        #p ::= ('.' | ('up' '.')+ | 'case' '.')? id ('.' id)*
        arg.world = False
        arg.case = False
        arg.up = 0
        if str[strp] == ".":
          arg.world = True
          strp += 1
        elif str[strp:strp+5] == "case.":
          arg.case = True
          strp += 5
        else:
          while str[strp:strp+3] == "up.":
            arg.up += 1
            strp += 3

        nextDot = str[strp:].find(".")
        if nextDot == 0:
          arg.ids = []
          self.addErr("Expected: label literal", tok)
        elif nextDot < 0:
          arg.ids = [str[strp:]]
        else:
          arg.ids = [str[strp:nextDot]]
          strp = nextDot
          while str[strp] == ".":
            nextDot = str[strp+1:].find(".")
            nextDot = nextDot if nextDot > 0 else len(str)
            arg.ids.append(str[strp+1:nextDot])
            strp = nextDot
            if strp >= len(str):
              break
        if len(arg.ids) == 1 and arg.ids[0] == "up":
          arg.ids[0] = ""
          arg.up += 1
      else:
        self.unexpect(peek)
      result.append(arg)
      peek = self.peek()
      first = False

      
    return result    
      
  def parseLemma(self):
    result = Ast(LEMMA, self.peek())
    self.matchKW("lemma")
    #name
    result.name = self.matchId()
    #opt label
    if self.peek().type == TokType.STRING:
      result.label = self.nextToken().str
    self.matchOptNL()
    self.matchType(TokType.START_BLOCK)
    #conclusion
    result.conclusion = [self.matchEmbed()]
    self.matchOptNL()
    while self.peek().type == TokType.PROOF_EMBED:
      result.conclusion.append(self.matchEmbed())
      self.matchOptNL()
    #opt where clause
    result.premises = []
    if self.isKW(self.peek(), "where"):
      self.matchKW("where")
      self.matchOptNL()
      self.matchType(TokType.START_BLOCK)
      while self.peek().type == TokType.PROOF_EMBED or self.peek().type == TokType.ID:
        label = ""
        peek = self.peek()
        if peek.type == TokType.ID and peek.str[-1] == ".":
          label = self.matchId().val[:-1]
        prem = self.matchEmbed()
        result.premises.append((label, prem))
        self.matchOptNL()
      self.matchType(TokType.END_BLOCK)
  #opt proof
    result.proof = None
    if self.isKW(self.peek(), "proof"):
      result.proof = self.parseProof()
    self.matchType(TokType.END_BLOCK)
    return result


    
  def parseSyntax(self):
    self.matchOptNL()
    result = Ast(SYNTAX, self.peek())
    self.matchType(TokType.START_BLOCK)
    while self.peek().type != TokType.END_BLOCK:
      try:
        if self.peek().type == TokType.LATEX_STRING:
          result.addChild(self.parseLatex(self.nextToken()))
          self.matchOptNL()
        else:
          result.addChild(self.parseProduction())
      except PanicMode:
        self.recover()
    self.matchType(TokType.END_BLOCK)
    self.matchOptNL()
    
    self.world.syntaxTrees.append(result)
    
    return result
    
    
    
  def parseProduction(self):
    result = Ast(PRODUCTION, self.peek())
    result.subtype = "terminal"
    peek = self.peek()
    if self.isKW(peek, "var"):
      result.subtype = "variable"
      self.nextToken()
    elif self.isKW(peek, "env"):
      result.subtype = "environment"
      self.nextToken()

    #optional semantic
    result.semantic = []
    while self.isKW(self.peek(), "{"):
      result.semantic.append(self.parseSemantic())
    peek = self.peek()

    if peek.type != TokType.ID:
      self.expect(self.nextToken(), "id")
      self.panic()
      result.err = "Missing category name"
      return result
      
    names = [self.matchName()]
    peek = self.peek()
    while self.isKW(peek, ";"):
      self.nextToken()
      names.append(self.matchName())
      peek = self.peek()
    result.lhs = names
    
    if self.isKW(peek, "::="):
      if result.subtype != "environment":
        result.subtype = "non-terminal"
      self.nextToken()
      #parse the rhs
      result.children = self.parseSynExps()
      peek = self.peek()
      
    if peek.type == TokType.STRING:
      result.label = self.nextToken().str
    else:
      result.label = ""
    
    self.matchType(TokType.NEW_LINE)
    return result
    
    
  def parseSemantic(self):
    self.matchKW('{')
    tok = self.nextToken()
    result = Ast(SEMANTIC, tok)
    if tok.type == TokType.KEYWORD:
      if tok.str == 'binds':
        result.subtype = 'binds'
        result.addChild(self.matchIdLists())
        if self.isKW(self.peek(), "in"):
          self.matchKW('in')
          result.addChild(self.matchIdLists())
          while not self.isKW(self.peek(), "}"):
            self.matchKW(";")
            result.addChild(self.matchIdLists())
      elif tok.str == 'ints':
        result.subtype = 'ints'
      elif tok.str == 'global':
        result.subtype = 'global'
      else:
        self.unexpect(tok)
    elif self.isKW(self.peek(), "->"):
      result.subtype = 'maps'
      self.pushBack(tok)
      result.addChild(self.matchIdLists())
      self.nextToken()
      result.addChild(self.matchIdLists())
    elif tok.type == TokType.ID:
      result.subtype = "id"
      result.addChild(tok.str)
    
    self.matchKW('}')
    return result
    
    
  def parseSynExps(self):
    result = [self.parseSynExp()]
    while self.isKW(self.peek(), "|"):
      self.matchKW('|')
      result.append(self.parseSynExp())
      
    return result

  def parseSynExp(self):
    exp = self.parseSynSubExp()
    
    exp.semantic = []
    while self.isKW(self.peek(), "{"):
      exp.semantic.append(self.parseSemantic())
    return exp  
    

  def parseSynSubExp(self):
    result = Ast(SYN_EXP, self.peek())
    while True:
      if self.peek().type == TokType.ID:
        result.addChild(self.matchId())
      elif self.isKW(self.peek(), "["):
        self.matchKW('[')
        sub = self.parseSynSubExp()
        sub.type = SYN_SEQ
        result.addChild(sub)
        self.matchKW(']')
      else:
        break
    return result
  
  
  def parseJudge(self):
    result = Ast(JUDGE, self.peek())

    result.val = self.matchRawId()
    result.syntax = self.parseJudgeSyntax()
    result.syntax.val = result.val

    if self.peek().type == TokType.LATEX_STRING:
      result.latex = self.nextToken().str

    if self.peek().type == TokType.STRING:
      result.label = self.nextToken().str
    else:
      result.label = ""
    
    self.checkEOS()

    self.matchOptNL()
    self.matchType(TokType.START_BLOCK)
    while self.peek().type != TokType.END_BLOCK:
      try:
        if self.peek().type == TokType.LATEX_STRING:
          result.addChild(self.parseLatex(self.nextToken()))
          self.matchOptNL()
        else:
          result.addChild(self.parseCase(result.val))
      except PanicMode:
        self.recover()
    self.matchType(TokType.END_BLOCK)
    self.matchOptNL()
    
    if result.val in self.world.judgeTrees:
      self.world.judgeTrees[result.val].append(result)
    else:
      self.world.judgeTrees[result.val] = [result]
      self.world.judgeNames.append(result.val)
    
    return result
    
    
    
  def parseCase(self, name):
    self.matchKW("case")
    result = Ast(JUDGE_CASE, self.peek())
    result.val = self.parseJudgeExp()
    result.val.val = name
    #optional label
    if self.peek().type == TokType.STRING:
      result.label = self.nextToken().str
    else:
      result.label = ""
    
    self.checkEOS()
    
    #premises
    self.matchOptNL()
    if self.peek().type == TokType.START_BLOCK:
      self.matchType(TokType.START_BLOCK)
      while self.peek().type != TokType.END_BLOCK:
        try:
          if self.peek().type == TokType.LATEX_STRING:
            result.addChild(self.parseLatex(self.nextToken()))
            self.matchOptNL()
          else:
            result.addChild(self.parsePremise())
        except PanicMode:
          self.recover()
      self.matchType(TokType.END_BLOCK)
      self.matchOptNL()
    
    return result
    

  def checkEOS(self):
    t = self.peek().type
    if t != TokType.START_BLOCK and t != TokType.NEW_LINE and t != TokType.EOF:
      self.unexpect(self.peek())

      
  def parseJudgeExp(self):
    self.recurLimit = 50
    result = Ast(PREMISE, self.peek())

    result.subtype = "judge"
    result.envs = self.matchOptExpList()
    self.matchKW("|-")
    result.children = self.matchOptExpList()

    return result
  


  def isExp(self, tok):
    return tok.type == TokType.ID or tok.type == TokType.KEYWORD and tok.str in ("{", "(", "...", "[")
    
  def isKW(self, tok, v):  
    return tok.type == TokType.KEYWORD and tok.str == v
    
  def isId(self, tok):
    return tok.type == TokType.ID

  def isIdOrList(self, tok):
    return tok.type == TokType.ID or self.isKW(tok, '[')
    
      
  def matchOptExpList(self):
    if self.isExp(self.peek()):
      return self.matchExpList()
    else:
      return []
    

    
  def matchExpList(self):   
    result = []
    result.append(self.parseSyExp())
    peek = self.peek()
    while self.isKW(peek, ";"):
      self.nextToken()
      result.append(self.parseSyExp())
      peek = self.peek()
    return result
      
      
      
  def parsePremise(self):
    self.recurLimit = 50
    result = Ast(PREMISE, self.peek())
    
    #can be a judgement or an equality of expressions
    # p ::= j | e = e
    # j ::= je;* |- je;*
    # e ::= apply je; je | je 
    # je ::= jxe,+
    # jxe ::= xe+
    # xe ::= id | ( e ) | {xe/(id | [id])}xe | xe_v | [jxe]
    # v ::= x | n

    if self.isKW(self.peek(), "not"):
      self.nextToken()
      result.nt = True
    else:
      result.nt = False
      
    if self.searchLine("="):
      result.subtype = "eq"
      result.lhs = self.parseSemExp()
      self.matchKW("=")
      result.rhs = self.parseSemExp()
      self.matchOptNL()
    elif self.searchLine("|-"):
      name = self.matchRawId()
      nt = result.nt
      result = self.parseJudgeExp()
      result.nt = nt
      result.val = name
      self.matchOptNL()
    elif self.searchLine("in"):
      result.subtype = "in"
      result.lhs = self.parseSemExp()
      self.matchKW("in")
      result.rhs = self.parseSemExp()
      self.matchOptNL()
    else:
      tok = self.nextToken()
      self.addError("Unknown proposition", tok)
      self.panic()
      result.subtype = "unknown: " + tok.ctxtLine
      return result
    
    return result    
  

  def parseSemExp(self):
    # e ::= apply je (; je)* | id (( je )) | je 
    first = self.nextToken()
    if self.isKW(first, "apply"):
      #function application
      result = Ast(EXP, self.peek())
      result.subtype = "fun app"
      result.lhs = self.parseSyExp()
      result.rhs = []
      while self.isKW(self.peek(), ";"):
        self.matchKW(";")
        result.rhs.append(self.parseSyExp())
      return result
          
    #shorthand for an apply
    if self.isId(first) and self.isKW(self.peek(), "(("):
      self.pushBack(first)
      result = Ast(EXP, first)
      result.subtype = "fun app"
      result.lhs = self.matchId()
      self.matchKW('((')
      result.rhs = []
      if not self.isKW(self.peek(), ")"):
        result.rhs.append(self.parseSyExp())
      while self.isKW(self.peek(), ";"):
        self.matchKW(";")
        result.rhs.append(self.parseSyExp())
      self.matchKW(')')
      self.matchKW(')')
      return result
          
    #must be a syntactic expression
    self.pushBack(first)
    return self.parseSyExp()
    
  def parseSyExp(self):
    # je ::= jxe,+
    # jxe ::= xe+
    # xe ::= id | ( je ) | {xe/(id | [id])}xe | xe_v | [jxe]
    
    result = Ast(EXP, self.peek())
    result.subtype = "concat"     
    result.children = [self.parseSubSeq()]
    
    peek = self.peek()
    while self.isKW(peek, ","):
      self.matchKW(",")
      result.children.append(self.parseSubSeq())
      peek = self.peek()
            
    return result
    
    
    
  def parseSubSeq(self):
    # jxe ::= xe+
    # xe ::= id | ( je ) | {xe/(id | [id])}xe | xe_v | [jxe]
    result = Ast(EXP, self.peek())
    result.children = [self.parseSubExp()]
    result.subtype = "sequence"
    peek = self.peek()
    while self.isExp(peek):
      result.children.append(self.parseSubExp())
      peek = self.peek()
    return result
  
  
  

  def parseSubExp(self):
    # xe ::= id | ( je ) | {xe/(id | [id])}xe | xe_v | [jxe?]
    self.recurLimit -= 1
    if not self.recurLimit:
      raise Exception("Recursion detected in parseSubExp (internal error)", self.nextToken())
      
    peek = self.peek()
    if self.isKW(peek, "{"):
      result = Ast(EXP, peek)
      result.subtype = "subst"
      self.matchKW("{")
      result.lhs = self.parseSubExp()
      self.matchKW("/")
      result.rhs = self.matchIdLists()
      self.matchKW("}")
      result.val = self.parseSubExp()
      result = result

    elif self.isKW(peek, "("):
      self.matchKW("(")
      result = self.parseSemExp()
      self.matchKW(")")
      result = result
      
    elif self.isKW(peek, "..."):
      result = Ast(ELIPSES, self.nextToken())
      
    elif self.isKW(peek, "["):
      result = Ast(LIST, peek)
      self.matchKW("[")
      if self.isKW(self.peek(), "]"):
        result.val = Ast(EXP, peek)
        result.val.subtype = "sequence"
      else:
        result.val = self.parseSubSeq()
      self.matchKW("]")
      result = result
    else:  
      result = self.matchId()
    
    if self.isKW(self.peek(), "_"):
      newR = Ast(EXP, self.nextToken())
      newR.subtype = "subscript"
      newR.lhs = result
      newR.rhs = self.matchIdOrNum()
      return newR
    
    return result
    
  
  def parseJudgeSyntax(self):
    result = Ast(JUDGE_SYNTAX, self.peek())

    result.envs = self.matchOptIdList()
    self.matchKW("|-")
    result.children = self.matchOptIdList()

    return result

    

  def matchOptIdList(self):   
    if self.isIdOrList(self.peek()):
      return self.matchIdList()
    else:
      return []
    

       
  def parseLatex(self, tok):
    result = Ast(LATEX_STRING, tok)
    result.val = tok.str
    result.space = 0
    while self.isKW(self.peek(), "_"):
      self.nextToken()
      result.space += 1
    return result
    
  def matchType(self, t):
    tok = self.nextToken()
    if tok.type != t:
      self.expect(tok, TokType.strings[t])
  
  def matchKW(self, v):
    tok = self.nextToken()
    if not self.isKW(tok, v):
      self.expect(tok, v)
    
    
    
  def matchId(self):
    result = Ast(ID, self.peek())
    result.val = self.matchRawId()
    peek = self.peek()
    mod = ""
    while peek.type == TokType.ID and peek.str in MODS:
      mod += self.nextToken().str
      peek = self.peek()
    result.mod = mod
    return result
    
    
  #match an id or an id wrapped in lists
  # il ::= id | [il]
  def matchIdLists(self):
    if self.isKW(self.peek(), "["):
      result = Ast(LIST, self.nextToken())
      result.val = self.matchIdLists()
      self.matchKW("]")
      return result
      
    return self.matchId()
    
    
  def matchRawIdLists(self):
    if self.isKW(self.peek(), "["):
      result = Ast(LIST, self.nextToken())
      seq = Ast(EXP, self.peek())
      seq.subtype = "sequence"
      while not self.isKW(self.peek(), "]"):
        seq.children.append(self.matchRawIdLists())
      result.val = seq
      self.matchKW("]")
      return result
      
    return self.matchRawId()
    
    
  #match a ;-separated list of ids or lists of ids
  # mil ::= id | [id] | mil;mil
  def matchIdList(self):   
    result = []
    result.append(self.matchRawIdOrList())
    peek = self.peek()
    while self.isKW(peek, ";"):
      self.nextToken()
      result.append(self.matchRawIdOrList())
      peek = self.peek()

    return result

  def matchRawIdOrList(self):
    if self.isKW(self.peek(), "["):
      result = Ast(LIST, self.nextToken())
      result.val = self.matchRawIdOrList()
      self.matchKW("]")
      return result
      
    return self.matchRawId()

  def matchIdOrNum(self):
    peek = self.peek()
    if peek.type == TokType.ID and peek.str in MODS and peek.str != "'":
      result = Ast(INT, self.nextToken())
      result.val = int(peek.str)
      return result
      
    return self.matchId()
    
  
  
  
  def matchRawId(self):
    tok = self.nextToken()
    if tok.type != TokType.ID:
      self.expect(tok, "id")
    else:
      return tok.str
  
  
  
  def matchName(self):
    result = Ast(NAME, self.peek())
    result.val = self.matchRawId()
    
    if self.peek().type == TokType.LATEX_STRING:
      result.latex = self.parseLatex(self.nextToken())
      
    return result
    
  
  def matchOptNL(self):
    tok = self.nextToken()
    if tok.type != TokType.NEW_LINE:
      self.pushBack(tok)

  def expect(self, tok, v):      
    msg = "Syntax error, expected: " + v + ", found: " + TokType.strings[tok.type]
    self.addError(msg, tok)
    self.panic()
    
    
  #handle an unexpected token  
  def unexpect(self, tok):
    msg = "Unexpected token: "
    if hasattr(tok, 'str'):
      msg += tok.str
    else:
      msg += TokType.strings[tok.type]
    self.addError(msg, tok)
    self.panic()
    
  #skip the next block if there is one
  def skipBlock(self):
    self.matchOptNL()
    if self.peek().type != TokType.START_BLOCK:
      return
    tok = self.nextToken()
    while tok.type != TokType.END_BLOCK and self.peek().type != TokType.EOF:
      tok = self.nextToken()
      if tok.type == TokType.START_BLOCK:
        self.pushBack(tok)
        self.skipBlock()

  
  def addError(self, msg, tok, line = -1, col = -1):
    if line < 0:
      line = tok.line
    if col < 0:
      col = tok.col
    self.errs.append(Err(msg, tok, line, col))

  #panic mode error recovery - scan to the end of the line  
  def panic(self):
    t = self.peek().type
    while t != TokType.NEW_LINE and t != TokType.EOF and t != TokType.END_BLOCK:
      self.nextToken()
      t = self.peek().type
    self.skipBlock()
    
    raise PanicMode()
    if self.peek().type == TokType.EOF:
      raise Exception("End of File")
    else:
      raise PanicMode()

    
  #recover from panic mode
  def recover(self):
    t = self.peek().type
    while t == TokType.NEW_LINE:
      self.nextToken()
      t = self.peek().type
    self.skipBlock()
    
    
    
    
class Lexer:
  def __init__(self, src, parser):
    self.src = src
    self.curIndent = 0
    if not src:
      raise IOError('Empty file or problem reading file')
    self.curLine = self.getNextLine()
    self.curLineN = 1
    self.curColN = 0
    self.inSemantic = False
    self.indentStack = []
    self.endBlockCount = 0
    self.parser = parser
    self.proofIndent = -1
    self.resetProof = False  #True when we must later rest proofIndent, but only do this once there are no more outstanding END_BLOCKs to return

  def nextToken(self):
    colN = self.curColN
    
    if self.endBlockCount:
      self.endBlockCount -= 1
      result = self.makeToken(TokType.END_BLOCK)
      result.proofBlock = self.proofIndent >= 0
      return result
        
    if self.resetProof:
      self.resetProof = False
      self.proofIdent = -1

    if not self.curLine and self.src.closed:
      while self.indentStack:
        self.indentStack.pop()
        self.endBlockCount += 1
      if self.endBlockCount:
        self.endBlockCount -= 1
        result = self.makeToken(TokType.END_BLOCK)
        result.proofBlock = self.proofIndent >= 0
        return result
      else:
        return self.makeToken(TokType.EOF)
    
    if colN >= len(self.curLine):
      return self.handleNewLines()
      
    if len(self.curLine) - colN >= len(COMMENT) and self.curLine[colN:].lstrip()[:len(COMMENT)] == COMMENT:
      return self.handleComment()



    #handle indenting and blocks
    if colN == 0:
      oldIndent = self.curIndent
      self.curIndent = self.countIndent()
      self.curColN = self.curIndent
      if (oldIndent > self.curIndent):
        pops = 0
        while oldIndent > self.curIndent:
          pops += 1
          oldIndent = self.indentStack.pop()

        result = self.makeToken(TokType.END_BLOCK)
        result.proofBlock = self.proofIndent >= 0
        self.endBlockCount += pops-1
        if oldIndent < self.curIndent:
          self.addError("Indentation mismatch; found: " + str(self.curIndent) + ", expected: " + str(oldIndent), result)
          self.curIndent = oldIndent
        #if the new indent is less than the proof indent, then reset the proofIndent at a later time
        if self.curIndent <= self.proofIndent:
          self.resetProof = True
        return result
        
      if (self.curIndent > oldIndent):
        self.indentStack.append(oldIndent)
        result = self.makeToken(TokType.START_BLOCK)
        result.proofBlock = self.proofIndent >= 0
        return result
      
    colN = self.curColN


    if len(self.curLine) - colN >= 2 and self.curLine[colN:colN+1] == "\\":
      result = self.makeToken(TokType.ID)          
      result.str = self.curLine[colN+1:colN+2]
      self.curColN += 2
      self.handleWhiteSpace()
      return result


    if self.proofIndent < 0 and len(self.curLine) - colN >= 2 and self.curLine[colN:colN+2] == "[[":
      return self.handleLatexString()

    if len(self.curLine) - colN >= 1 and self.curLine[colN:colN+1] == "\"":
      return self.handleString()

    if self.proofIndent < 0 and len(self.curLine) - colN >= 1 and self.curLine[colN:colN+1] == "{":
      self.inSemantic = True
      result = self.makeToken(TokType.KEYWORD)
      result.str = "{"
      self.curColN += 1
      self.handleWhiteSpace()
      return result
    if self.proofIndent < 0 and len(self.curLine) - colN >= 1 and self.curLine[colN:colN+1] == "}":
      self.inSemantic = False
      result = self.makeToken(TokType.KEYWORD)
      result.str = "}"
      self.curColN += 1
      self.handleWhiteSpace()
      return result
    if self.proofIndent >= 0 and len(self.curLine) - colN >= 1 and self.curLine[colN:colN+1] == "{":
      return self.handleProofEmbed()
      
      
    word = self.firstWord()
    #check for keywords, including semantic keywords if inSemantic
    if (self.proofIndent >= 0 and word in PROOF_KEYWORDS + PROOF_RESERVED[1:]) or word in KEYWORDS + RESERVED or (self.inSemantic and word in SEM_KEYWORDS):
      result = self.makeToken(TokType.KEYWORD)
      if self.proofIndent < 0 and word == "proof":
        self.proofIndent = self.curIndent
    else:
      result = self.makeToken(TokType.ID)    
      
    result.str = word
    self.curColN += len(word)
    self.handleWhiteSpace()
    return result
    
  #counts the leading spaces on curLine, does not take the current column into account  
  def countIndent(self):
    return len(self.curLine) - len(self.curLine.lstrip())
      
  #returns the first word in a string  
  def firstWord(self):
    #error conditions: empty string or undealtwith whitesapce
    if self.curColN >= len(self.curLine) or self.curLine[self.curColN].isspace():
      raise Exception("Inconsistent string at firstWord: '" + self.curLine[self.curColN:] + "'")
    
    
    #check for starting with a symbol of some kind
    for k in RESERVED+SYMBOLS+PROOF_RESERVED:
      if self.curLine.startswith(k, self.curColN) and ((self.proofIndent < 0 and k in RESERVED+SYMBOLS) or (self.proofIndent >= 0 and k in PROOF_RESERVED[1:])):
        return k
        
    #otherwise, find the first alphanum seq up to the first whitespace or symbol or eol
    col = self.curColN
    result = self.curLine[col]
    col += 1
    while col < len(self.curLine):
      c = self.curLine[col]
      if (self.proofIndent < 0 and c in PREFIXES) or (self.proofIndent >= 0 and c in PROOF_PREFIXES) or c.isspace():
        return result
      result += c
      col += 1
    
    return result

      
  def handleNewLines(self):
    #check for inSemantic
    if self.inSemantic:
      self.inSemantic = False
      result = self.makeToken(TokType.KEYWORD)
      self.addError("Semantic not closed (missing '}')", result)
      result.err = True
      result.str = "}"
      return result
    
    result = self.makeToken(TokType.NEW_LINE)
    lines = 0
    
    self.curColN = 0
    while True:
      try:
        self.curLineN += 1
        lines += 1
        self.curLine = self.getNextLine()
      except StopIteration:
        self.src.close()
        self.curLine = None
        break
      if self.curLine and not self.curLine.isspace():
        break 
    
    result.lines = lines
    return result
    
    
  def handleComment(self):
    result = self.makeToken(TokType.COMMENT)
    result.str = self.curLine[self.curColN:].strip()[len(COMMENT):]
    self.curColN = len(self.curLine)
    return result
  
  #n syntax in proof mode
  def handleProofEmbed(self):
    #scan for the closing '}'
    string = ""
    bracCount = 0
    for c in self.curLine[self.curColN+1:]:
      self.curColN += 1
      if c == "{":
        string += c
        bracCount += 1
      elif c == "}":
        if bracCount:
          bracCount -= 1
          string += c
        else:
          self.curColN += 1
          break
      else:
        string += c
        
    result = self.makeToken(TokType.PROOF_EMBED)
    result.str = string
    if bracCount:
      self.addError("Embedded source code in proof not closed; missing '}'", result)
    return result
  
  def handleString(self):
    result = self.makeToken(TokType.STRING)
    str = ""
    #skip the first "
    self.curColN += 1
    while self.curColN < len(self.curLine):
      c = self.curLine[self.curColN]
      if c == "\"":
        result.str = str
        self.curColN += 1
        self.handleWhiteSpace()
        return result
        
      str += c
      self.curColN += 1
      
    #error: EOL before end of string
    self.addError("String not closed (missing '\"')", result)
    result.str = str
    return result

  def handleLatexString(self):
    result = self.makeToken(TokType.LATEX_STRING)
    str = ""
    #skip the first [[
    self.curColN += 2
    while True:
      while self.curColN < len(self.curLine):
        c = self.curLine[self.curColN]
        if c == "]" and len(self.curLine) > self.curColN+1 and self.curLine[self.curColN+1] == "]":
          result.str = str.rstrip(" ")
          self.curColN += 2
          self.handleWhiteSpace()
          return result
        
        str += c
        self.curColN += 1
      
      #handle the end of a line in a latex string
      str += "\n"
      self.curColN = 0
      try:
        self.curLineN += 1
        self.curLine = self.getNextLine()
      except StopIteration:
        self.src.close()
        self.curLine = None
        break
      
    #error: EOL before end of file
    self.addError("Latex string not closed (missing ']]')", result)
    result.str = str.rstrip(" ")
    return result
    
  def getNextLine(self):
    return self.src.next().rstrip()
    
  #skip trailing whitespace, do not call at the start of a line
  def handleWhiteSpace(self):
    while self.curColN < len(self.curLine) and self.curLine[self.curColN].isspace():
      self.curColN += 1
      
  def addError(self, msg, tok):
    self.parser.addError(msg, tok, self.curLineN, self.curColN+1)
    
  def makeToken(self, type):
    return Token(type, self.curLineN, self.curColN+1, self.curLine)
    

    
class TokType:
  ID = 1
  KEYWORD = 2
  START_BLOCK = 3
  END_BLOCK = 4
  NEW_LINE = 5
  LATEX_STRING = 6
  COMMENT = 7
  STRING = 8
  EOF = 9
  PROOF_EMBED = 10
  
  strings = ["ERROR", "ID", "KEYWORD", "START_BLOCK", "END_BLOCK", "NEW_LINE", "LATEX_STRING", "COMMENT", "STRING", "EOF", "PROOF_EMBED"]
    
class Token:
  def __init__(self, type, line, col, ctxtLine):
    self.ctxtLine = ctxtLine
    self.type = type
    self.line = line
    self.col = col
  
  def shortString(self):
    if self.type == TokType.COMMENT:
      return "//" + self.str
    if hasattr(self, 'str'):
      return self.str
      
    if self.type == TokType.NEW_LINE:
      return "NEW_LINE(" + str(self.lines) + ")"
      
    return TokType.strings[self.type]
  
  def longString(self):
    result = TokType.strings[self.type] + ", " + str(self.line) + ", " + str(self.col)
    if hasattr(self, 'lines'):
      result += ": " + str(self.lines) + " lines"
    else:
      ps = self.prettyString()
      if ps:
        result += ": " + ps
    return result
  
  def prettyString(self):
    if self.type in (TokType.ID, TokType.KEYWORD):
      return self.str
    if self.type in (TokType.START_BLOCK, TokType.END_BLOCK, TokType.EOF):
      return ""
    if self.type == TokType.NEW_LINE:
      return "\n"
    if self.type == TokType.STRING:
      return '"' + self.str + '"'
    if self.type == TokType.LATEX_STRING:
      return '[[' + self.str + ']]'
    if self.type == TokType.COMMENT:
      return '//' + self.str
      
      
#a string with a pointer to the nth char
def pointerString(n):
  result = n * " "
  result += "^"
  return result
  
  
class Err:
  def __init__(self, msg, tok, line, col):
    self.msg = msg
    self.tok = tok
    self.line = line
    self.col = col
  
  def shortMsg(self):
    return self.msg + " at " + str(self.line) + ", " + str(self.col)
      
  def longMsg(self):
    result = self.msg + " at line: " + str(self.line) + ", column: " + str(self.col) + "\n"
    if self.tok:
      if hasattr(self.tok, 'ctxtLine') and self.tok.ctxtLine:
        result += "At: " + self.tok.ctxtLine + "\n"
        result += "    " + pointerString(self.col-1) + "\n"
      result += "Token: " + self.tok.longString()
    return result
    
    
class PanicMode(Exception):
  def __init__(self):
    self.args = "Unresolved panic mode",
  