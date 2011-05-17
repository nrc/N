class Ast:
  def __init__(self, type, tok):
    self.children = []
    self.type = type
    self.tok = tok
      
  def addChild(self, x):
    self.children.append(x)
    
  def toTree(self, prefix = ""):
    result = prefix + BACK_LOOKUP[self.type]
    if hasattr(self, "subtype") and isinstance(self.subtype, str):
      result += ": " + self.subtype    
    if hasattr(self, "val") and isinstance(self.val, str):
      result += ": " + self.val
    result += "\n"
    
    if hasattr(self, "val") and isinstance(self.val, Ast):
      result += self.val.toTree(prefix + "  ")
    if hasattr(self, "lhs"):
      if isinstance(self.lhs, Ast):
        result += self.lhs.toTree(prefix + "  ")
      elif hasattr(self.lhs, "__iter__"):
        for c in self.lhs:
          if isinstance(c, Ast):
            result += c.toTree(prefix + "  ")
          elif isinstance(c, str):
            result += prefix + "  " + c
    
    for c in self.children:
      if isinstance(c, Ast):
        result += c.toTree(prefix + "  ")
      elif isinstance(c, str):
        result += prefix + "  " + c
        
    return result
    
    
PROGRAM = 1
SYNTAX = 2
JUDGE = 3
LATEX_STRING = 4
NAME = 5
ACTUAL = 6
SEMANTIC = 7
SYN_EXP = 8
PRODUCTION = 9
SYN_SEQ = 10
ID = 11
JUDGE_SYNTAX = 12
JUDGE_CASE = 13
PREMISE = 14
EXP = 15
ELIPSES = 16
INT = 17
LIST = 18
PROOF = 19
PROOF_LINE = 20
PROOF_ARG = 21
LEMMA = 22
PROOF_CASE = 23
BACK_LOOKUP =  dict([(globals()[x], x) for x in filter(lambda x: x.isupper(), dir())])
