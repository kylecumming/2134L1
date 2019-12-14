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


try:
  tok = next_token()
  while tok != None and tok != "":
    print("line {} col {} : {}".format(tok.line, tok.col, tok))
    tok = next_token()
   
except ScanError as p:
  if verbose:
    print("{} at line {} col {} : {}".format(p.msg,p.tok.line,p.tok.col,p.tok))
