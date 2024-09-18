from antlr4 import *

from .myVisitor import myVisitor
from .CKBLexer import CKBLexer
from .CKBParser import CKBParser
import os
#from .QUERYLexer import QUERYLexer
#from .QUERYParser import QUERYParser
#from .myQueryVisitor import myQueryVisitor

from inference.queries import Queries
from inference.belief_base import BeliefBase



from antlr4.error.ErrorListener import ErrorListener

class ThrowingErrorListener(ErrorListener):
    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        raise Exception(f"Syntax error at line {line}, column {column}: {msg}")

def getParseTree(ckbs_string):
    stream = InputStream(ckbs_string)
    lexer = CKBLexer(stream)
    lexer.removeErrorListeners()
    lexer.addErrorListener(ThrowingErrorListener())

    stream = CommonTokenStream(lexer)
    parser = CKBParser(stream)
    parser.removeErrorListeners()
    parser.addErrorListener(ThrowingErrorListener())

    tree = parser.ckbs()
    return tree


def parse_belief_base(string: str) -> BeliefBase:
    if os.path.isfile(string):
        with open(string) as f: file = f.read() 
        belief_base = parseCKB(file)
    else:
        belief_base = parseCKB(string)
    return belief_base


def parse_queries(string: str) -> Queries:
    if os.path.isfile(string):
        with open(string) as f: file = f.read() 
        queries = parse_queries_from_str(file)
    else:
        queries = parse_queries_from_str(string)
    return queries


def parse_queries_from_str(string: str) -> Queries:
    if 'signature' and 'conditionals' in string:
        belief_base = parseCKB(string)
        queries = Queries(belief_base)
    else:
        query_dict = parseQuery(string)
        if query_dict: queries = Queries(query_dict)
    return queries #type: ignore

def parse_belief_base_from_str(string: str):
    return parseCKB(string)

def parseCKB(ckbs_string):
    """
    stream = InputStream(ckbs_string)
    lexer = CKBLexer(stream)
    stream = CommonTokenStream(lexer)
    parser = CKBParser(stream)
    """
    tree = getParseTree(ckbs_string)
    visitor = myVisitor()
    ckbs = visitor.visit(tree)
    ckb = list(ckbs.values())[0]
    return ckb

        



def parseQuery(querystring):
    ckb_template=f"signature \n a,b,c,d,e,f \n conditionals \n dummy \n {{ \n {querystring}\n }}" 
    ckbquery=parseCKB(ckb_template)
    #print(query)
    #query.__class__ = Queries
    return ckbquery.conditionals

