#TODO


import re
import nparser
from ast import *

macros = dict()
spaceHint = False
noSpace = []
jMacros = dict()

MACRO_PREFIX = "nnn"
J_MACRO_PREFIX = "nnj"

LATEX_SYMBOLS = ("{", "}", "%", "^", "&", "\\")

def lPrint(prog):
  macros.clear()
  result = """\input{nmacros.tex}
\input{npreboiler.tex}

"""
  for c in prog.children:
    if not c:
      result += "%Could not print empty child\n"
    elif c.type == LATEX_STRING:
      result += lpLatexNode(c) + "\n\n"
    elif c.type == SYNTAX:
      result += lpSyntax(c) + "\n\n"
    elif c.type == JUDGE:
      result += lpJudge(c) + "\n\n"
    else:
      result += "%Could not print " + str(c.type) + "\n"
      
  return makeMacros() + result + "\\input{npostboiler.tex}\n\n"
  
def makeMacros():
  result = ""
  
  for k in macros.iterkeys():
    result += "\\newcommand{\\" + MACRO_PREFIX + escape(k) + "}{" + macros[k] + "}\n"
    
  result += "\n"
  
  for k in jMacros.iterkeys():
    (envs, args, macro) = jMacros[k]
    result += "\\newcommand{\\" + J_MACRO_PREFIX + escape(k) + "}[" + str(envs+args) + "]{" + macro + "}\n"
  
  
  result += "\n\n"
  return result


def parseLStr(base, ids, startN):
  n = startN
  for id in ids:
    result = ""
    curWord = ""
    #the \v is used to delimit the string and make sure we catch the last word
    base+="\v"
    for i in range(len(base)):
      c = base[i]
      if c.isalpha() or c in nparser.MODS or c in {'[', ']'}:
        curWord += c
      else:
        if curWord == id:
          result += "{#" + str(n) + "}"
          if c != "\v":
            result += c
          curWord = ""
          result += base[i+1:-1]
          break;
        else:
          result += curWord
          curWord = ""
          if c != "*":
            result += c
    n += 1
    base = result
  
  return base

  
def lpJudge(j):
 
  #store a macro for the judgement
  mac = ""
  envs = len(j.syntax.envs)
  args = len(j.syntax.children)
  if hasattr(j, "latex"):
    #use the supplied latex
    mac = j.latex
    mac = parseLStr(mac, map(lpRawIdOrListLookup, j.syntax.envs), 1)
    mac = parseLStr(mac, map(lpRawIdOrListLookup, j.syntax.children), 1+envs)
  else:
    #no latex, use a default that just looks like a function application
    mac = j.val + "_{" + ", ".join(map(lambda x: "{#" + str(x) + "}", range(1, envs+1))) + "}(" + ", ".join(map(lambda x: "{#" + str(x) + "}", range(envs+1, envs+1+args))) + ")"
    
  jMacros[j.val] = (envs, args, mac)
  
  
  result = "\startJudgeFig{" 
  result += j.label.capitalize()
  result += "}{"
  result += lpJudgeSyntax(j.syntax)
  result += "}\n\n"
  
  
  for c in j.children:
    if c.type == LATEX_STRING:
      result += lpLatexNode(c) + "\n"
    else:
      result += lpJCase(c) + "\n"
  
  caption = ""
  if j.label:
    caption = "\lang " + j.label + "."
  result += r"\finJudgeFig{" + caption + "}{" + j.val + "}\n"
  
  return result
  
  

def lpJCase(c):
  if c.type != JUDGE_CASE:
    return "%ERROR: expected case of judgement"

  result = ""
  if c.label:
    result += r"\redRule{"
  else:
    result += r"\auxRule{"
    
  #premises
  lineBreak = 0
  for ch in c.children:
    if ch.type == LATEX_STRING:
      result += "\n" + lpLatexNode(ch)
      lineBreak = 0
    else:
      if lineBreak == 0:
        lineBreak += 1
      elif lineBreak > 2:
        result += "\\\\"
        lineBreak = 1
      else:
        result += "\qquad"
        lineBreak += 1
      result += "\n" + lpPremise(ch)
  
  result += "\n}{\n"
  result += lpJudgeExp(c.val)
  result += "\n}"
  
  if c.label:
    result += "{" + c.label + "}"
   
  
  return result


def lpPremise(p):
  if p.subtype == "eq":
    result = lpExpS(p.lhs) + " "
    if p.nt:
      result += r"\not"
    result += "= " + lpExpS(p.rhs)
    return result
  elif p.subtype == "judge":
    result = lpJudgeExp(p)
    if p.nt:
      result += r"\ \mbox{\em undefined}"
    return result
  elif p.subtype == "in":
    result = lpExpS(p.lhs)
    if p.nt:
      result += r" \notin "
    else:
      result += r" \in "
    result += lpExpS(p.rhs)
    return result
  else:
    return "err: " + p.subtype
  
def lpJudgeSyntax(j):
  result = "\\" + J_MACRO_PREFIX + escape(j.val) + "{"
  
  result += "}{".join(map(lpRawIdOrList, j.envs + j.children))

  return result + "}"
 
def lpJudgeExp(j): 
  result = "\\" + J_MACRO_PREFIX + escape(j.val) + "{"
  
  result += "}{".join(map(lpExpS, j.envs + j.children))

  return result + "}"
  
#latex an expression in brackets (hint)
def lpExpB(e):
  return lpExp(e, True)
  
  
#latex an expression without surrounding space
def lpExpS(e):
  global spaceHint
  spaceHint = False
  return lpExp(e)

inSeq = False  
  
#latex an expression
def lpExp(e, bracket = False):
  global spaceHint
  global inSeq
  oldSeq = inSeq
  result = ""
  
  if bracket:
    result = "("
  
  if e.type == ID:
    result = lpSpaceId(e.val) + lpIdMod(e.mod)
    bracket = False
  elif e.type == INT:
    result = e.val
    bracket = False
  elif e.type == ELIPSES:
    result = ""
    if spaceHint:
      result += "\\ "
    result += "..."
    bracket = False
    spaceHint = True
  elif e.type == LIST:
    #special case - empty list
    result = ""
    if spaceHint:
      result += "\\ "
    if e.val.type == EXP and e.val.subtype == "sequence" and len(e.val.children) == 0:
      if not inSeq:
        result += "\emptyset"
    else:
      inSeq = False
      result += "\overline{" + lpExpS(e.val) + "}"
    bracket = False
    spaceHint = True
  elif e.type != EXP:
    result += "err: " + str(e.type) + "\\ "
    spaceHint = false
  elif e.subtype == "fun app":
    inSeq = False
    if spaceHint:
      result += "\\ "
    result += lpExpS(e.lhs) + "(" + ", ".join(map(lambda x: lpExpS(x), e.rhs)) + ")"
    spaceHint = True
  elif e.subtype == "sequence":
    if len(e.children) > 1:
      inSeq = True
    result += " ".join(map(lpExpB, e.children))
  elif e.subtype == "concat":
    inSeq = False
    result += ",".join(map(lpExpS, e.children))
    spaceHint = True
  elif e.subtype == "subst":
    inSeq = False
    result = r"\code{[$"
    if e.rhs.type == ID:
      result += lpExpS(e.lhs) + "$/$" + lpExpS(e.rhs) 
    elif e.rhs.type == LIST and e.lhs.type == LIST:
      result += r"\overline{" + lpExpS(e.lhs.val) + "\code{/}" + lpExpS(e.rhs.val) + "}"
    else:
      result += "err"
    result += "$]}"
    spaceHint = False
    result += lpExpB(e.val) 
    bracket = False
  elif e.subtype == "subscript":
    inSeq = False
    result += lpExpB(e.lhs) + "_{" + lpExpS(e.rhs) + "}"
    spaceHint = True
  else:
    result += "err: " + e.subtype
    spaceHint = True
  
  if bracket:
    result += ")"
  
  inSeq = oldSeq
  return result
  
  
    
def lpSyntax(s):
  result = "\\startSyntaxFig\n\n"

  for c in s.children:
    if c.type == PRODUCTION:
      makeMacro(c)

  for c in s.children:
    if not c:
      result += "%Could not print empty child\n"
    if c.type == LATEX_STRING:
      result += lpLatexNode(c) + "\n"
    elif c.type == PRODUCTION:
      result += lpProduction(c) + "\n"
    else:
      result += "%Could not print " + str(c.type) + "\n"
      
  result += "\n\\finSyntaxFig\n\n\n"
  return result
  
def lpLatexNode(s):
  return lpLatex(s.val)

def lpLatex(s):
  if s == "":
    return "\\\\\n"
  return s

  
#adds a macro for the lhs of the given production
def makeMacro(p):
  for n in p.lhs:
    if n.type != NAME:
      continue
    string = "err"
    if hasattr(n, "latex"):
      string = n.latex.val
      if n.latex.space == 0:
        noSpace.append(n.val)
    elif p.subtype in ("non-terminal", "environment"):
      string = n.val
    elif p.subtype in ("terminal", "variable"):
      string = r"\code{" + n.val + "}"
    
    if hasattr(p, "semantic"):
      for s in p.semantic:
        if s.subtype == "ints":
          string = n.val
    
    macros[n.val] = string
  
def lpProduction(p):
  result = ""

  if p.subtype == "terminal":
    if not (p.semantic or p.label):
      result += "%"
    result += "$" + lpNameList(p.lhs) + "$"
    result += r"\>\> "
  elif p.subtype == "variable":
    result += "$" + lpNameList(p.lhs) + "$"
    result += r"\>\> "
  elif p.subtype == "non-terminal":
    result += "$" + lpNameList(p.lhs) + "$"
    result += r"\>\bbc\> "
    result += "$" + lpSynExps(p.children) + "$"
  elif p.subtype == "environment":
    result += "$" + lpNameList(p.lhs) + "$"
    result += r"\>\bbc\> "
    result += "$" + lpSynExps(p.children) + "$"
  else:
    result += "%ERROR: unknown subtype of production: " + p.subtype
    
  if p.label:
    result += r"\>\annot{" + p.label + "}"
  
  result += r"\\"
  
  return result
  
  
def lpSynExps(l):
  return " \OR ".join(map(lpSynSubExp, l)) + " "
  
  

def lpSynSubExp(sse):
  result = ""
  first = True
  global spaceHint
  spaceHint = False
  
  
  for c in sse.children:
    if first:
      first = False
    else:
      result += " "

    if c.type == ID:
      result += lpSpaceId(c.val) + lpIdMod(c.mod)
    elif c.type == SYN_SEQ:
      if spaceHint:
        result += r"\ "
      result += r"\overline{"
      result += lpSynSubExp(c)
      result += "}"
      spaceHint = True
    else:
      if spaceHint:
        result += r"\ "
      result +=  "err: " + c.type
      spaceHint = True
      
  return result

  
  
def lpIdMod(m):
  if re.match("^'+$", m):
    return m
  elif m:
    count = m.count("'")
    return "'"*count + "_{" + m.replace("'", "") + "}"
  else:
    return ""
  
def lpNameList(l):
  return ", ".join(map(lpName, l)) + " "
    
    
    
def lpName(n):
  if n.type != NAME:
    return "ERROR: expected name"
    
  return lpRawId(n.val)

def lpRawId(s):
  if s in macros:
    return "\\" + MACRO_PREFIX + escape(s)
  else:
    return r"\code{" + lEscape(s) + "}"
    
    
def lpRawIdOrList(s):
  if isinstance(s, str):
    return lpRawId(s)
    
  if isinstance(s, Ast) and s.type == LIST:
    return r"\overline{" + lpRawIdOrList(s.val) + "}"
    
  if isinstance(s, Ast) and s.type == EXP and s.subtype == "sequence":
    return " ".join(s.children)
    
  return "%Err: not string or list ast: " + str(s) + r"\n"

  
def lpRawIdOrListLookup(s):
  if isinstance(s, str):
    return s
    
  if isinstance(s, Ast) and s.type == LIST:
    return "[" + lpRawIdOrListLookup(s.val) + "]"
    
  if isinstance(s, Ast) and s.type == EXP and s.subtype == "sequence":
    return " ".join(s.children)
    
  return "Err"

  
  
def lpSpaceId(s):
  global spaceHint
  result = ""
  if s in macros and s in noSpace:
    result += "\\" + MACRO_PREFIX + escape(s)
    spaceHint = False
  elif s in macros:
    if spaceHint:
      result += r"\ "
    result += "\\" + MACRO_PREFIX + escape(s)
    spaceHint = True
  else:
    sh2 = True
    if s in nparser.SYMBOLS+nparser.RESERVED:
      sh2 = False
    if spaceHint and sh2:
      result += r"\ "
      
    result += r"\code{" + lEscape(s) + "}"
    spaceHint = sh2
  return result
  
  
def escape(s):
  if s in nparser.SYMBOLS:
    return nparser.SYM_MAP[s]
  return s
  
  
def lEscape(s):
  if s in LATEX_SYMBOLS:
    return "\\" + s
  else:
    return s