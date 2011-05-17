from nparser import Parser
from nchecker import Checker
from env import Env
import util
import proof


class ProofMode:
  def __init__(self, world, parent = None):
    self.world = world
    self.curEnv = Env()
    self.prompt = "p"
    self.curProof = None
    self.stack = []
    self.callbacks = dict()
    
  def registerCallBack(self, obj, meth):
    key = self.stack[-1]
    if key not in self.callbacks:
      self.callbacks[key] = []

    self.callbacks[key].append((obj,meth))      
    
  def getIndent(self):
    return self.prompt[1:]
    
  def dispatch(self, input):
    words = input.split(" ")
    if len(words) == 0:
      self.close()
      return ""
    cmd = words[0]
    args = []
    if len(words) > 1:
      input = input.replace("\;", "__colon")
      args = map(lambda x: x.strip().replace("__colon", "\;"), input[len(cmd)+1:].split(";"))
      

    if cmd == "exit":
      return "_exit"
    elif cmd == "help":
      return self.help()
    
    if cmd:
      return "Unknown command, for help, use 'help', to leave animation mode, use 'exit'"
    
    return ""

    
  def help(self):
    return """Proof mode commands:
  help               print this message
  exit               leave proof mode

  lemma              prove the lemma
"""

  #close this level of proofs
  def close(self):
    if self.stack:
      closed = self.stack.pop()
      self.prompt = self.prompt[:-2]
      self.curEnv = self.curEnv.parent
      if self.stack:
        key = self.stack[-1]
        if key in self.callbacks and self.callbacks[key]:
          for (o, m) in self.callbacks[key]:
            getattr(o, m)(closed)
          self.callbacks[key] = []
    #TODO save what has happened so far
    
  def open(self, scope):
    self.stack.append(scope)
    self.prompt += "  "
    self.curEnv = Env(self.curEnv)
    