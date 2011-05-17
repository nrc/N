#TODO
#more proof stuff
# proof by sind
# substs
#ownership example
#output derivations
#TODOs in expSemantics.py
#maybe - remove "ints" semantic


import sys
import ast
import nparser
from pretty import pPrint
from latex import lPrint
from ast import Ast
from nchecker import Checker
from animate import Animate
from proofMode import ProofMode
import subprocess

class Global:
  def __init__(self):
    self.syntaxTrees = []
    self.judgeTrees = dict()
    self.judgeNames = []
    self.proofAsts = []
    self.topProof = None
    self.err = False
    self.proofMode = ProofMode(self)
  
curWorld = Global()
anim = None
proofMode = None


#run n on a given file
def loadFile(fName):
  global curWorld
  
  if "." not in fName:
    fName = fName+".n"
  f = open(fName)
  p = nparser.Parser(f)
  prog = p.parseTop(curWorld)
  f.close()
  if p.errs:
    print "Parsing errors:\n"
    for e in p.errs:
      print e.longMsg()
      print
    print "\nTotal: " + str(len(p.errs)) + " errors\n" 
    curWorld.err = True
    return

  print "Parsing succeeded (" + fName + ")\n"
  addAst(prog)
  ch = Checker(curWorld)
  ch.check()
  if ch.errs:
    print "Checking errors:\n"
    for e in ch.errs:
      print e.longMsg()
      print
    print "\nTotal: " + str(len(ch.errs)) + " errors\n" 
    curWorld.err = True
    return
    
  print "Checking succeeded (" + fName + ")\n"
  if ch.log:
    print ch.log
    
    
def loadScript(fName):
  if "." not in fName:
    fName = fName+".ns"
    
  for c in open(fName):
    if handleCommand(c.strip()) < 0:
      return -1
  return 0
  
  
  
def handleCommand(cmd, scr = True):
  global anim
  global curWorld
  global proofMode
  #strip any comments
  i = cmd.find("//")
  if i >= 0:
    cmd = cmd[:i].strip()
   
  if anim:
    if scr and cmd:
      print "a>" + cmd
    result = anim.dispatch(cmd)
    if result.startswith("_exit"):
      print " " + result[5:]
      anim = None
    elif result:
      print " " + result
    return 0
    
  if proofMode:
    if scr and cmd:
      print proofMode.prompt + ">" + cmd
    result = proofMode.dispatch(cmd)
    if result.startswith("_exit"):
      print " " + result[5:]
      proofMode = None
    elif result:
      print result
    return 0
    
  
  if cmd == "exit":
    return -1
  elif cmd == "animate":
    anim = Animate(curWorld)
  elif cmd == "proof":
    proofMode = curWorld.ProofMode(curWorld)
  elif cmd.startswith("load"):
    words = parseCommand(cmd)
    for f in words[1:]:
      loadFile(f)
  elif cmd.startswith("print"):
    words = parseCommand(cmd)
    if len(words) == 1:
      print pPrint(curWorld.top)
    else:
      fName = words[1]
      if "." not in fName:
        fName = fName + ".n.out"
      f = open(fName, "w")
      f.write(pPrint(curWorld.top))
      f.close()
      print "Success writing to: " + fName
  elif cmd.startswith("latex"):
    words = parseCommand(cmd)
    if len(words) == 1:
      print lPrint(curWorld.top)
    else:
      fName = words[1]
      if "." not in fName:
        fName = fName + ".tex"
      f = open(fName, "w")
      f.write(lPrint(curWorld.top))
      f.close()
      print "Success writing to: " + fName
  elif cmd.startswith("sh "):
    try:
      subprocess.call(cmd[3:], shell=True)
    except Exception as e:
      print "Error trying to execute '" + cmd[3:] + "': " + str(e)
    else:
      print "Executed " + cmd[3:]
  elif cmd == "**":
    curWorld.err = False
  elif cmd.startswith("*"):
    if curWorld.err:
      return handleCommand(cmd[1:])
  elif cmd == "help":
    print "N v0.09"
    print
    print "Supported commands:"
    print "  help                  print this message"
    print "  exit                  exit n"
    print "  load filenames        load the specified files"
    print "  latex [filename]      output the current formal system as latex"
    print "  print [filename]      output the current formal system in the source format"
    print "  proof                 switch to proof mode"
    print "  animate               switch to animation mode"
    print
    print "  * cmd                 execute cmd if an error has occured"
    print "  **                    reset the error flag"
    print
  elif cmd == "":
    pass
  else:
    print "Unknown command: ", cmd
    return 1
    
  return 0
  
#parse the command into an array of words, break by spaces and use quote marks
def parseCommand(cmd):
  if '"' not in cmd:
    return cmd.split(" ")
  
  result = []
  cur = ""
  quote = False
  for c in cmd:
    if c == '"':
      if cur:
        result.append(cur)
      cur = ""
      quote = not quote        
    elif c == " " and not quote:
      if cur:
        result.append(cur)
      cur = ""
    else:
      cur += c
  if cur:
    result.append(cur)
  return result

  
def nLoop():
  while True:
    prompt = ">"
    if anim:
      prompt = "a" + prompt
    elif proofMode:
      prompt = proofMode.prompt + prompt
    cmd = raw_input(prompt)
    flag = handleCommand(cmd, False)
    if flag < 0:
      return

      
def addAst(a):
  if a.type == ast.PROGRAM:
    curWorld.top.children.extend(a.children)
  else:
    curWorld.top.addChild(a)
      
def main(argv = None):
  if argv is None:
    argv = sys.argv
    
  curWorld.top = Ast(ast.PROGRAM, None)
  
  if len(argv) > 1:
    for p in argv[1:]:
      if p.endswith(".n"):
        loadFile(p) 
      else:
        if loadScript(p) < 0:
          return 0

  nLoop()
  return 0

if __name__ == "__main__":
  sys.exit(main())
  
  
