#TODO



from ast import *
import nparser

def pPrint(prog):
  result = ""
  for c in prog.children:
    if not c:
      result += "Could not print empty child\n"
    elif c.type == LATEX_STRING:
      result += ppLatexNode(c) + "\n\n"
    elif c.type == SYNTAX:
      result += ppSyntax(c) + "\n"
    elif c.type == JUDGE:
      result += ppJudge(c) + "\n"
    else:
      result += "Could not print " + str(c.type) + "\n"
      
  return result
    
def ppJudge(j):    
  result = "judge " + j.val + " " + ppJudgeSyntax(j.syntax) + " "
  
  if hasattr(j, "latex"):
    result += ppLatex(j.latex) + " "
  
  if j.label:
    result += "\"" + j.label + "\""
  
  result += "\n"
  for c in j.children:
    if c.type == LATEX_STRING:
      result += "  " + ppLatexNode(c) + "\n"
    else:
      result += "  " + ppJCase(c) + "\n"
  
  return result + "\n"
  
  

def ppJCase(c):
  if c.type != JUDGE_CASE:
    return "ERROR: expected case of judgement"

  result = "case " + ppJudgeExp(c.val)
  if c.label:
    result += " \"" + c.label + "\""
    
  #premises
  for ch in c.children:
    if ch.type == LATEX_STRING:
      result += "\n    " + ppLatexNode(ch)
    else:
      result += "\n    " + ppPremise(ch)
  
  return result


def ppPremise(p):
  nStr = ""
  if p.nt:
    nStr = "not "

  if p.subtype == "eq":
    return nStr + ppExp(p.lhs) + " = " + ppExp(p.rhs)
  elif p.subtype == "judge":
    return nStr + p.val + " " + ppJudgeExp(p)
  elif p.subtype == "in":
    return nStr + ppExp(p.lhs) + " in " + ppExp(p.rhs)
  else:
    return "Could not print (premise): " + p.subtype
  
def ppJudgeSyntax(j):
  result = ""
  
  result += "; ".join(j.envs)
  if result:
    result += " "
  result += "|- "
  result += "; ".join(map(ppSList, j.children))

  return result
  

#pretty print a string or list of strings
def ppSList(s):
  if isinstance(s, str):
    return escape(s)
    
  if isinstance(s, Ast) and s.type == LIST:
    return "[" + ppSList(s.val) + "]"
  elif isinstance(s, Ast) and s.type == EXP and s.subtype == "sequence":
    return " ".join(map(ppSList, s.children))
    
  return "Err: not string or list: " + str(s)
 
def ppJudgeExp(j): 
  result = ""
  
  result += "; ".join(map(ppExp, j.envs))
  if result:
    result += " "
  result += "|- "
  result += "; ".join(map(ppExp, j.children))

  return result
  
def ppExpB(e):
  return ppExp(e, True)
  
def ppExp(e, bracket = False):
  result = ""
  
  if bracket:
    result = "("
  
  if e.type == ID:
    result = escape(e.val) + e.mod
    bracket = False
  elif e.type == INT:
    result = e.val
    bracket = False
  elif e.type == ELIPSES:
    result = "..."
    bracket = False
  elif e.type == LIST:
    result = "[" + ppExp(e.val) + "]"
    bracket = False
  elif e.type != EXP:
    result += "Not an expression: " + str(e.type)
  elif e.subtype == "fun app":
    result += "apply " + ppExp(e.lhs) + "; ".join(map(lambda x: ppExp(x), e.rhs))
  elif e.subtype == "sequence":
    result += " ".join(map(ppExpB, e.children))
  elif e.subtype == "concat":
    result += ",".join(map(ppExp, e.children))
  elif e.subtype == "subst":
    result = "{" + ppExp(e.lhs) + "/" + ppExp(e.rhs) + "}" + ppExpB(e.val) 
    bracket = False
  elif e.subtype == "subscript":
    result += ppExp(e.lhs) + "_" + ppExp(e.rhs)
  else:
    result += "Could not print (expression): " + e.subtype
  
  if bracket:
    result += ")"
  
  return result
  
def escape(c):
  if c in nparser.RESERVED + nparser.SPECIAL:
    return "\\" + c
    
  return c
    
def ppSyntax(s):
  result = "syntax\n"
  for c in s.children:
    if not c:
      result += "Could not print empty child\n"
    if c.type == LATEX_STRING:
      result += "  " + ppLatexNode(c) + "\n"
    elif c.type == PRODUCTION:
      result += "  " + ppProduction(c) + "\n"
    else:
      result += "Could not print " + str(c.type) + "\n"
  return result
  
def ppLatexNode(s):
  return ppLatex(s.val) + "_"*s.space

def ppLatex(s):
  result = "[[" + s
  if s.endswith("]"):
    result += " "
  result += "]]"
  return result

def ppProduction(p):
  result = ""

  if p.subtype == "terminal":
    result += ppOptSemantic(p, " ")
    result += ppNameList(p.lhs)
  elif p.subtype == "variable":
    result += "var "
    result += ppOptSemantic(p, " ")
    result += ppNameList(p.lhs)
  elif p.subtype == "non-terminal":
    result += ppOptSemantic(p, " ")
    result += ppNameList(p.lhs)
    result += "::= "
    result += ppSynExps(p.children)    
  elif p.subtype == "environment":
    result += "env "
    result += ppOptSemantic(p, " ")
    result += ppNameList(p.lhs)
    result += "::= "
    result += ppSynExps(p.children)
  else:
    result += "ERROR: unknown subtype of production: " + p.subtype
    
  if p.label:
    result += "  \"" + p.label + "\""
  
  return result
  
  
def ppSynExps(l):
  return " | ".join(map(ppSynExp, l)) + " "
  
def ppSynExp(se):
  if se.type != SYN_EXP:
    return "ERROR: expected syntax expression"

  result = ""

  result += ppSynSubExp(se)
  
  result += ppOptSemantic(se, "", " ")
  return result
  
  
  
def ppSynSubExp(sse):
  result = ""
  first = True

  for c in sse.children:
    if first:
      first = False
    else:
      result += " "

    if c.type == ID:
      result += escape(c.val) + c.mod
    elif c.type == SYN_SEQ:
      result += "[" +  ppSynSubExp(c) + "]"
    else:
      result +=  "ERROR: unknown syntax expression: " + c.type
      
  return result

  
  
def ppNameList(l):
  return "; ".join(map(ppName, l)) + " "
    
    
    
def ppName(n):
  if n.type != NAME:
    return "ERROR: expected name"
    
  result = escape(n.val)
  
  if hasattr(n, "latex"):
    result += " " + ppLatexNode(n.latex)
  
  return result

def ppOptSemantic(ast, postfix = "", prefix = ""):
  result = ""
  for s in ast.semantic:
    if result:
      result += " "
    result += prefix + "{" + ppSemantic(s) + "}" + postfix
  return result
    
def ppSemantic(s):
  if s.type != SEMANTIC:
    return "ERROR: expected semantic"
  elif s.subtype == "ints":
    return "ints"
  elif s.subtype == "global":
    return "global"
  elif s.subtype == "binds":
    return "binds " + ppExp(s.children[0]) + " in " + ";".join(map(lambda x: ppExp(x), s.children[1:]))
  elif s.subtype == "maps":
    return s.children[0].val + " -> " + s.children[1].val
  elif s.subtype == "id":
    return s.children[0]
  else:
    return "ERROR: unknown subtype of semantic: " + s.subtype
