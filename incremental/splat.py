#!/usr/bin/python

from __future__ import print_function
import sys, string, tokenize, copy, re, types
from collections import namedtuple

singletons = { '!', '&', '|', '*', '+', '-', '/', ',',
               '(', ')', '[', ']', '{', '}', '=', '<', '>', '#' }
literals = { 'true', 'false', 'nil' }
keywords = { 'let', 'letrec', 'def', 'set', 'lambda', 'if', 'elseif', 'else', 
             'guard', 'raise', 'catch' }
reserved = set().union(singletons, literals, keywords)
bad_expr = {'&', '|', '*', '+', '/', ',', ')', ']', '{', '}', 
            '=', '<', '>', '#', 'elseif', 'else', 'guard' }
ok_sexpr = { '!', '-', '(', '[', 'true', 'false', 'nil' }

print_rules = "-r" in sys.argv
verbose = "-v" in sys.argv


class Str(str):
  pass


class ScanError(Exception):
  def __init__(self, msg, tok):
    self.msg = msg
    self.tok = tok

  def __str__(self):
    return repr(self.msg)


class ParseError(Exception):
  def __init__(self, value, tok):
    self.value = value
    self.tok = tok

  def __str__(self):
    return repr(self.value)


class EvalError(Exception):
  def __init__(self, value, line, col):
    self.value = value
    self.line = line
    self.col = col

  def __str__(self):
    return repr(self.value)


def reStr(s, t):
  r = Str(s)
  r.line = t.line
  r.col = t.col
  return r


def char_generator(program):
  line = 1
  col = 0
  for b in program:
    c = Str(b);
    col = col + 1
    if c == '\n':
      line = line + 1
      col = 0

    c.line = line
    c.col = col
    yield c;

  c = Str("")
  c.line = line
  c.col = col
  yield c


def scan(stream, acc, cond):
  c = next(stream)
  while cond(acc, c):
    acc = acc + c
    c = next(stream)
  return acc, c
 
 
def scanner(program):
  stream = char_generator(program)
  numtest = lambda acc, c: c.isdigit()
  symtest = lambda acc, c: c.isalpha() or c.isdigit() or c == '_'
  strtest = lambda acc, c: c != '"' and c != "" 

  c = next(stream)
  while c != "":
    first = c
    acc = c

    if c.isspace():
      c = next(stream)
      continue
    elif c in singletons:
      c = next(stream)
    elif c == '"':
      acc, c = scan(stream, acc, strtest)
      if c != "":
        acc = acc + c
        c = next(stream)
    elif c.isdigit():
      acc, c = scan(stream, acc, numtest)
    elif c.isalpha() or c == '_':
      acc, c = scan(stream, acc, symtest)
    else:
      raise ScanError('Unexpected character', c)

    yield reStr(acc, first)

  yield c


tokens = scanner(sys.stdin.read())
cur_token = None

def lookahead():
  global cur_token

  if cur_token == None:
    try:
      cur_token = next(tokens)
    except StopIteration:
      cur_token = None

  return cur_token


def next_token():
  global cur_token

  n = lookahead()
  cur_token = None
  return n


def rule(r):
  if print_rules:
    print(r)


class RefEnv:
  zeroStr = Str("")
  zeroStr.line = 0
  zeroStr.col = 0

  def __init__(self, prev = None):
    self.prev = prev
    self.map = dict()

  def getStr(self, s):
    if isinstance(s, Str):
      return s
    if isinstance(s, str):
      return reStr(s, RefEnv.zeroStr)
    elif isinstance(s, SymbolExpr):
      return s.sym
    else:
      return reStr(str(s), RefEnv.zeroStr)

  def lookup(self, id):
    id = self.getStr(id)
    if id in self.map:
      return self.map[id]
    elif self.prev != None:
      return self.prev.lookup(id)
    else:
      raise EvalError("Cannot find: " + str(id), id.line, id.col)

  def update(self, id, val):
    id = self.getStr(id)
    if id in self.map:
      self.map[id] = val
    elif self.prev != None:
      self.prev.update(id, val)
    else:
      raise EvalError("Cannot find: " + str(id), id.line, id.col)

  def define(self, id, val):
    id = self.getStr(id)
    if id in self.map:
      raise EvalError("Duplicate symbol defined: " + id, id.line, id.col)
    self.map[id] = val


OpFunc = namedtuple('OpFunc', ['typ', 'op'])
OpTypInt = type(1)
OpTypBool = type(True)
operators = { '+' : OpFunc(None, lambda a, b : a + b),
              '-' : OpFunc(OpTypInt, lambda a, b : a - b),
              '*' : OpFunc(OpTypInt, lambda a, b : a * b),
              '/' : OpFunc(OpTypInt, lambda a, b : a // b),
              '&' : OpFunc(OpTypBool, lambda a, b : a & b),
              '|' : OpFunc(OpTypBool, lambda a, b : a | b),
              '!' : OpFunc(OpTypBool, lambda a, b : not b),
              '<' : OpFunc(None, lambda a, b : a < b),
              '>' : OpFunc(None, lambda a, b : a > b),
              '=' : OpFunc(None, lambda a, b : a == b),
              '#' : OpFunc(None, lambda a, b : a != b)
              }


class Lambda:
  def __init__(self, ref, params, exprs):
    self.ref = ref
    self.params = copy.deepcopy(params)
    self.exprs = copy.deepcopy(exprs)

  def __str__(self):
    return "<lambda>"


class EList:
  def __init__(self):
    self.list = []
    self.parse()

  def parse(self):
    tok = lookahead()
    if tok in bad_expr:
      raise ParseError("Invalid expression", tok)

    rule("E_LIST -> EXPR E_TAIL");

    self.list.append(parseExpr())
    self.parseETail()
   
  def parseETail(self):
    tok = lookahead()
    if tok == '}' or tok == "":
      rule("E_TAIL -> epsilon");
      return
  
    rule("E_TAIL -> E_LIST");
    self.parse()

  def eval(self, env, toplevel = False):
    if toplevel:
      v = []
      for e in self.list:
        v.append(e.eval(env))
      return v
    else:
      v = None
      for e in self.list:
        v = e.eval(env)
      return v


class DefExpr:
  def __init__(self):
    rule("DEF -> 'def' SYMBOL '=' EXPR");
    next_token()
    self.sym = SymbolExpr()
    tok = next_token()
    if tok != '=':
      raise ParseError("Expecting '=' after symbol", tok)
    self.expr = parseExpr()

  def eval(self, env):
    val = self.expr.eval(env)
    env.define(self.sym, val)
    return val


class AssignExpr:
  def __init__(self, is_expr):
    if is_expr:
      rule("ASSIGN -> 'set' SYMBOL '=' EXPR");
      next_token()

    self.sym = SymbolExpr()
    tok = next_token()
    if tok != '=':
      raise ParseError("Expecting '=' after symbol", tok)

    self.expr = parseExpr()

  def eval(self, env, add_env = None):
    val = self.expr.eval(env)
    if add_env != None:
      result = val
      add_env.define(self.sym, val)
    else:
      result = env.lookup(self.sym)
      env.update(self.sym, val)
    return result


class LambdaExpr:
  def __init__(self):
    rule("LAMBDA -> 'lambda' '(' PARAMS ')' BODY")
    next_token()

    tok = next_token()
    if tok != '(':
      raise ParseError("Expecting '('", tok)
    self.params = []
    self.parseParams()
    tok = next_token()
    if tok != ')':
      raise ParseError("Expecting ')'", tok)

    self.body = parseBody()

  def parseParams(self):
    tok = lookahead()
    if tok == ')':
      rule("PARAMS -> epsilon")
    else:
      self.params.append(SymbolExpr())
      self.parsePList()

  def parsePList(self):
    tok = lookahead()
    if tok == ')':
      rule("P_LIST -> epsilon")
    elif tok == ',':
      rule("P_LIST -> ',' SYMBOL P_LIST")
      next_token()
      self.params.append(SymbolExpr())
      self.parsePList()
    else:
      raise ParseError("Expecting ',' or ')'", tok)

  def eval(self, env):
    return Lambda(env, self.params, self.body)


class LetExpr:
  def __init__(self):
    self.rec = next_token() == 'letrec'
    if self.rec:
      rule("LET -> 'letrec' V_LIST BODY")
    else:
      rule("LET -> 'let' V_LIST BODY")

    self.vars = []
    self.parseVList()
    self.body = parseBody()
  
  def parseVList(self):
    rule("V_LIST -> SYM '=' EXPR V_TAIL")
    self.vars.append(AssignExpr(False))
    self.parseVTail()

  def parseVTail(self):
    if lookahead() == ',':
      rule("V_TAIL -> ',' V_LIST")
      next_token()
      self.parseVList()
    else:
      rule("V_TAIL -> epsilon")

  def eval(self, env):
    let_env = RefEnv(env)
    if self.rec:
      env = let_env

    for v in self.vars:
      v.eval(env, let_env)

    return self.body.eval(let_env)


class IfExpr:
  def __init__(self):
    self.cond = None
    self.next = None

    tok = next_token()
    if tok == 'if':
      rule("IF -> 'if' EXPR BODY ELIF ELSE" )
      self.tok = lookahead()
      self.cond = parseExpr()
    elif tok == 'elseif':
      rule("ELIF -> 'elseif' EXPR BODY ELIF" )
      self.tok = lookahead()
      self.cond = parseExpr()
    elif tok == 'else':
      rule("ELSE -> 'ELSE' BODY" )

    self.body = parseBody()

    tok = lookahead()
    if self.cond != None:
      if tok == 'elseif':
        self.next = IfExpr()
      else:
        rule("ELIF -> epsilon" )
        if lookahead() == 'else':
          self.next = IfExpr()
        else:
          rule("ELSE -> epsilon" )

  def eval(self, env):
    cond = True
    if self.cond != None:
      cond = self.cond.eval(env)
      if type(cond) != OpTypBool:
        raise EvalError("Condition not boolean", self.tok.line, self.tok.col)
  
    if cond:
      return self.body.eval(env)
    elif self.next != None:
      return self.next.eval(env)
    else:
      return False

OpLevel = namedtuple('OpLevel', ['expr', 'head', 'tail', 'ops', 'next' ])

fact_lvl = OpLevel("FACT", "VALUE", "F_TAIL", { '*', '/' }, None)
term_lvl = OpLevel("TERM", "FACT", "T_TAIL", { '+', '-' }, fact_lvl)
rel_lvl = OpLevel("RELOP", "TERM", "R_TAIL", { '<', '>', '=', '#' }, term_lvl)
and_lvl = OpLevel("ANDOP", "RELOP", "A_TAIL", { '&' }, rel_lvl)
top_lvl = OpLevel("S_EXPR", "ANDOP", "S_TAIL", { '|' }, and_lvl)
  
class SimpleExpr:
  def __init__(self, op_lvl = top_lvl):
    self.atoms = []
    self.parse(op_lvl)

  def parse(self, op_lvl):
    rule(op_lvl.expr + " -> " + op_lvl.head + " " + op_lvl.tail)
    if op_lvl.next != None:
      self.atoms.append(SimpleExpr(op_lvl.next))
    else:
      self.atoms.append(parseValue())

    self.parseTail(op_lvl)

  def parseTail(self, op_lvl):
    if lookahead() in op_lvl.ops:
      tok = next_token()
      rule(op_lvl.tail + " -> '" + tok + "' " + op_lvl.expr)
      self.atoms.append(tok)
      self.parse(op_lvl)
    else:
      rule(op_lvl.tail + " -> epsilon")

  def pack(self):
    if len(self.atoms) == 1 :
      if isinstance(self.atoms[0], SimpleExpr):
        return self.atoms[0].pack()
      else:
        return self.atoms[0]
    else:
      return self

  def eval(self, env):
    atoms = iter(self.atoms)
    acc = next(atoms).eval(env)

    while True:
      try:
        op = next(atoms)
        val = next(atoms).eval(env)
      except StopIteration:
        return acc

      func = operators[op]
      if type(acc) != type(val):
        raise EvalError("Operand type " + str(type(acc)) + " != " +\
                         str(type(val)), op.line, op.col)
      elif func.typ != None and type(acc) != func.typ:
        raise EvalError("Operand types are not correct", op.line, op.col)
      
      acc = func.op(acc, val)


class ListExpr:
  def __init__(self):
    rule("LIST -> '[' ARGS ']'")

    next_token()
    self.args = []

    self.parseArgs()
    next_token()          # closing ']' token

  def parseArgs(self):
    if lookahead() == ']':  
      rule("ARGS -> epsilon")
    else:
      rule("ARGS -> EXPR A_LIST")
      self.args.append(parseExpr())
      self.parseAList()
       
  def parseAList(self):
    tok = lookahead()
    if tok == ']':  
      rule("A_LIST -> epsilon")
    elif tok == ',':
      rule("A_LIST -> ',' EXPR A_LIST")
      next_token()
      self.args.append(parseExpr())
      self.parseAList()
    else:
      raise ParseError("Expecting ',' or ']' after list item", tok)
       
  def eval(self, env):
    return [ a.eval(env) for a in self.args ]

class CallExpr:
  def __init__(self, expr):
    self.loc =  expr
    self.args = []

    self.tok = next_token()
    if self.tok != '(':
      raise ParseError("Expecting '(' in call", self.tok)
   
    self.parseArgs()
    next_token()          # closing ')' token
    

  def parseArgs(self):
    if lookahead() == ')':  
      rule("ARGS -> epsilon")
    else:
      rule("ARGS -> EXPR A_LIST")
      self.args.append(parseExpr())
      self.parseAList()
       
  def parseAList(self):
    tok = lookahead()
    if tok == ')':  
      rule("A_LIST -> epsilon")
    elif tok == ',':
      rule("A_LIST -> ',' EXPR A_LIST")
      next_token()
      self.args.append(parseExpr())
      self.parseAList()
    else:
      raise ParseError("Expecting ',' or ')' after argument", tok)
       
  def eval(self, env):
    loc = self.loc.eval(env)
    if isinstance(loc, types.LambdaType):
      if len(self.args) != loc.__code__.co_argcount:
        raise EvalError("Incorrect number of arguments", self.tok.line,
                         self.tok.col)
      args = []
      for a in self.args:
        args.append(a.eval(env))
      return loc(*args)
    elif isinstance(loc, Lambda):
      call_env = RefEnv(loc.ref)
      args = iter(self.args)
      for p in loc.params:
        call_env.define(p, next(args).eval(env))

      return loc.exprs.eval(call_env)
    else:
      raise EvalError("Cannot call a non-lambda expression", self.tok.line,
                        self.tok.col)
    

class UnaryExpr:
  def __init__(self):
    self.op = next_token()
    rule("UNARY -> '" + self.op + "' VALUE")
    self.expr = parseValue()
  
  def eval(self, env):
    acc = self.expr.eval(env)
    func = operators[self.op]
    if func.typ != None and type(acc) != func.typ:
      raise EvalError("Operand types are incorrect", self.op.line, self.op.col)
    return func.op(0, acc)


class LiteralExpr:
  def __init__(self):
    tok = next_token()
    if tok.isdigit():
      rule("LITERAL -> int(" + tok + ")")
      self.val = int(tok)
    elif tok[0] == '"':
      rule("LITERAL -> string(" + tok + ")")
      self.val = tok[1:-1]
    elif tok == 'true':
      rule("LITERAL -> 'true'")
      self.val = True
    elif tok == 'false':
      rule("LITERAL -> 'false'")
      self.val = False
    elif tok == 'nil':
      rule("LITERAL -> 'nil'")
      self.val = None
  
  def eval(self, env):
    return self.val


class SymbolExpr:
  def __init__(self):
    self.sym = next_token()
    rule("SYMBOL -> symbol(" + self.sym + ")")
    if self.sym in reserved or self.sym.isdigit():
      raise ParseError("Invalid symbol name", self.sym)

  def eval(self, env):
    return env.lookup(self.sym)


def parseS():
  tok = lookahead()
  if tok in bad_expr:
    raise ParseError("Invalid expression", tok)
  elif tok == "":
    rule("S -> epsilon");
    return None
  
  rule("S -> E_LIST");
  return EList()
  

def parseExpr():
  tok = lookahead()
 
  if tok in bad_expr:
    raise ParseError("Invalid expression", tok)
  elif tok == 'def':
    rule("EXPR -> DEF");
    return DefExpr()
  elif tok == 'set':
    rule("EXPR -> ASSIGN");
    return AssignExpr(True)
  elif tok == 'lambda':
    rule("EXPR -> LAMBDA");
    return LambdaExpr()
  elif tok == 'let':
    rule("EXPR -> LET");
    return LetExpr()
  elif tok == 'if':
    rule( "EXPR -> IF" );
    return IfExpr()
  elif tok in ok_sexpr or tok not in reserved: 
    rule("EXPR -> S_EXPR");
    return SimpleExpr().pack()
  else:
    raise ParseError("Invalid expression", tok)


def parseBody():
  tok = next_token()
  if tok != '{':
    raise ParseError("Expecting '{' at start of block", tok)

  rule("BODY -> '{' E_LIST '}'")
  l = EList()

  tok = next_token() 
  if tok != '}':
    raise ParseError("Expecting '}' at end of block", tok)

  return l


def parseCall(expr):
    while lookahead() == '(':
      rule("CALL -> '(' ARGS ')' CALL")
      expr = CallExpr(expr)
    
    rule("CALL -> epsilon")
    return expr


def parseValue():
  tok = lookahead()
  if tok == "":
    raise ParseError("Unexpected end of program", tok)
  elif tok == "(":
    rule("VALUE -> '(' EXPR ')' CALL")
    next_token()
    e = parseExpr()
    tok = next_token() 
    if tok != ')':
      raise ParseError("Expecting ')' after expression", tok)

    return parseCall(e)
  elif tok == '[':
    rule("VALUE -> LIST")
    return ListExpr()
  elif tok == "-" or tok == '!':   # unary operation
    rule("VALUE -> UNARY")
    return UnaryExpr()
  elif tok.isdigit() or tok[0] == '"' or tok in literals:  # literal
    rule("VALUE -> LITERAL")
    return LiteralExpr()
  elif tok.isidentifier():                           # identifier
    rule("VALUE -> SYMBOL")
    return parseCall(SymbolExpr())
  else:                                              # error
    raise ParseError("Unexpected token ", tok)


def correct(v):
  if isinstance(v, list):
    s = "["
    for i in v:
      if len(s) > 1:
        s += ", "
      s += correct(i)
    s += "]"
    return s
  elif isinstance(v, str):
    return '"' + v + '"'
  elif isinstance(v, bool):
    if v:
      return 'true'
    else:
      return 'false'
  elif v == None:
    return 'nil'
  else:
    return str(v)


def print_arg(arg):
  print(arg)
  return arg


top_ref = RefEnv()
top_ref.define('head', lambda lst : lst[0])
top_ref.define('tail', lambda lst : lst[1:])
top_ref.define('prepend', lambda head, tail : [head] + tail)
top_ref.define('print', print_arg)

try:
  l = parseS()
  tok = lookahead()
  if tok != "":
    raise ParseError("Extraneous input", tok)
  if l != None:
    for a in l.eval(top_ref, True):
      print(correct(a))
except ScanError as p:
  if verbose:
    print("{} at line {} col {} : {}".format(p.msg,p.tok.line,p.tok.col,p.tok))
except ParseError as p:
  if verbose:
    print("Syntax error on line " + str(p.tok.line) + ", col " + \
          str(p.tok.col) + " : " + str(p))
  else:
    print("Syntax Error")
except EvalError as p:
  print("Evaluation Error while evaluating " + str(p) + " on line " +\
        str(p.line) + ", column " + str(p.col))
