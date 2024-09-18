# Generated from CKB.g4 by ANTLR 4.13.2
# encoding: utf-8
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
	from typing import TextIO
else:
	from typing.io import TextIO

def serializedATN():
    return [
        4,1,15,128,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,1,0,1,
        0,4,0,15,8,0,11,0,12,0,16,1,1,5,1,20,8,1,10,1,12,1,23,9,1,1,1,1,
        1,4,1,27,8,1,11,1,12,1,28,1,1,1,1,1,2,1,2,1,2,1,2,1,2,3,2,38,8,2,
        1,3,5,3,41,8,3,10,3,12,3,44,9,3,1,3,1,3,4,3,48,8,3,11,3,12,3,49,
        1,3,1,3,5,3,54,8,3,10,3,12,3,57,9,3,1,3,1,3,5,3,61,8,3,10,3,12,3,
        64,9,3,1,3,1,3,1,3,5,3,69,8,3,10,3,12,3,72,9,3,1,3,5,3,75,8,3,10,
        3,12,3,78,9,3,1,4,1,4,1,4,1,4,1,4,1,4,1,4,5,4,87,8,4,10,4,12,4,90,
        9,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,5,4,100,8,4,10,4,12,4,103,9,
        4,3,4,105,8,4,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,3,5,115,8,5,1,5,1,
        5,1,5,1,5,1,5,1,5,5,5,123,8,5,10,5,12,5,126,9,5,1,5,0,1,10,6,0,2,
        4,6,8,10,0,0,138,0,12,1,0,0,0,2,21,1,0,0,0,4,37,1,0,0,0,6,42,1,0,
        0,0,8,104,1,0,0,0,10,114,1,0,0,0,12,14,3,2,1,0,13,15,3,6,3,0,14,
        13,1,0,0,0,15,16,1,0,0,0,16,14,1,0,0,0,16,17,1,0,0,0,17,1,1,0,0,
        0,18,20,5,15,0,0,19,18,1,0,0,0,20,23,1,0,0,0,21,19,1,0,0,0,21,22,
        1,0,0,0,22,24,1,0,0,0,23,21,1,0,0,0,24,26,5,1,0,0,25,27,5,15,0,0,
        26,25,1,0,0,0,27,28,1,0,0,0,28,26,1,0,0,0,28,29,1,0,0,0,29,30,1,
        0,0,0,30,31,3,4,2,0,31,3,1,0,0,0,32,33,5,11,0,0,33,34,5,2,0,0,34,
        38,3,4,2,0,35,36,5,11,0,0,36,38,5,15,0,0,37,32,1,0,0,0,37,35,1,0,
        0,0,38,5,1,0,0,0,39,41,5,15,0,0,40,39,1,0,0,0,41,44,1,0,0,0,42,40,
        1,0,0,0,42,43,1,0,0,0,43,45,1,0,0,0,44,42,1,0,0,0,45,47,5,3,0,0,
        46,48,5,15,0,0,47,46,1,0,0,0,48,49,1,0,0,0,49,47,1,0,0,0,49,50,1,
        0,0,0,50,51,1,0,0,0,51,55,5,11,0,0,52,54,5,15,0,0,53,52,1,0,0,0,
        54,57,1,0,0,0,55,53,1,0,0,0,55,56,1,0,0,0,56,58,1,0,0,0,57,55,1,
        0,0,0,58,62,5,4,0,0,59,61,5,15,0,0,60,59,1,0,0,0,61,64,1,0,0,0,62,
        60,1,0,0,0,62,63,1,0,0,0,63,65,1,0,0,0,64,62,1,0,0,0,65,66,3,8,4,
        0,66,70,5,5,0,0,67,69,5,15,0,0,68,67,1,0,0,0,69,72,1,0,0,0,70,68,
        1,0,0,0,70,71,1,0,0,0,71,76,1,0,0,0,72,70,1,0,0,0,73,75,3,6,3,0,
        74,73,1,0,0,0,75,78,1,0,0,0,76,74,1,0,0,0,76,77,1,0,0,0,77,7,1,0,
        0,0,78,76,1,0,0,0,79,80,5,6,0,0,80,81,3,10,5,0,81,82,5,7,0,0,82,
        83,3,10,5,0,83,84,5,8,0,0,84,88,5,2,0,0,85,87,5,15,0,0,86,85,1,0,
        0,0,87,90,1,0,0,0,88,86,1,0,0,0,88,89,1,0,0,0,89,91,1,0,0,0,90,88,
        1,0,0,0,91,92,3,8,4,0,92,105,1,0,0,0,93,94,5,6,0,0,94,95,3,10,5,
        0,95,96,5,7,0,0,96,97,3,10,5,0,97,101,5,8,0,0,98,100,5,15,0,0,99,
        98,1,0,0,0,100,103,1,0,0,0,101,99,1,0,0,0,101,102,1,0,0,0,102,105,
        1,0,0,0,103,101,1,0,0,0,104,79,1,0,0,0,104,93,1,0,0,0,105,9,1,0,
        0,0,106,107,6,5,-1,0,107,108,5,9,0,0,108,115,3,10,5,5,109,110,5,
        6,0,0,110,111,3,10,5,0,111,112,5,8,0,0,112,115,1,0,0,0,113,115,5,
        11,0,0,114,106,1,0,0,0,114,109,1,0,0,0,114,113,1,0,0,0,115,124,1,
        0,0,0,116,117,10,4,0,0,117,118,5,2,0,0,118,123,3,10,5,5,119,120,
        10,3,0,0,120,121,5,10,0,0,121,123,3,10,5,4,122,116,1,0,0,0,122,119,
        1,0,0,0,123,126,1,0,0,0,124,122,1,0,0,0,124,125,1,0,0,0,125,11,1,
        0,0,0,126,124,1,0,0,0,16,16,21,28,37,42,49,55,62,70,76,88,101,104,
        114,122,124
    ]

class CKBParser ( Parser ):

    grammarFileName = "CKB.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'signature'", "','", "'conditionals'", 
                     "'{'", "'}'", "'('", "'|'", "')'", "'!'", "';'" ]

    symbolicNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "ID", "WS", 
                      "COMMENT", "BLOCKCOMMENT", "NEWLINE" ]

    RULE_ckbs = 0
    RULE_signature = 1
    RULE_myid = 2
    RULE_conditionals = 3
    RULE_condition = 4
    RULE_formula = 5

    ruleNames =  [ "ckbs", "signature", "myid", "conditionals", "condition", 
                   "formula" ]

    EOF = Token.EOF
    T__0=1
    T__1=2
    T__2=3
    T__3=4
    T__4=5
    T__5=6
    T__6=7
    T__7=8
    T__8=9
    T__9=10
    ID=11
    WS=12
    COMMENT=13
    BLOCKCOMMENT=14
    NEWLINE=15

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.2")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class CkbsContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def signature(self):
            return self.getTypedRuleContext(CKBParser.SignatureContext,0)


        def conditionals(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(CKBParser.ConditionalsContext)
            else:
                return self.getTypedRuleContext(CKBParser.ConditionalsContext,i)


        def getRuleIndex(self):
            return CKBParser.RULE_ckbs

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitCkbs" ):
                return visitor.visitCkbs(self)
            else:
                return visitor.visitChildren(self)




    def ckbs(self):

        localctx = CKBParser.CkbsContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_ckbs)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 12
            self.signature()
            self.state = 14 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 13
                self.conditionals()
                self.state = 16 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==3 or _la==15):
                    break

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class SignatureContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def myid(self):
            return self.getTypedRuleContext(CKBParser.MyidContext,0)


        def NEWLINE(self, i:int=None):
            if i is None:
                return self.getTokens(CKBParser.NEWLINE)
            else:
                return self.getToken(CKBParser.NEWLINE, i)

        def getRuleIndex(self):
            return CKBParser.RULE_signature

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitSignature" ):
                return visitor.visitSignature(self)
            else:
                return visitor.visitChildren(self)




    def signature(self):

        localctx = CKBParser.SignatureContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_signature)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 21
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==15:
                self.state = 18
                self.match(CKBParser.NEWLINE)
                self.state = 23
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 24
            self.match(CKBParser.T__0)
            self.state = 26 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 25
                self.match(CKBParser.NEWLINE)
                self.state = 28 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==15):
                    break

            self.state = 30
            self.myid()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class MyidContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser
            self.num = None # Token

        def myid(self):
            return self.getTypedRuleContext(CKBParser.MyidContext,0)


        def ID(self):
            return self.getToken(CKBParser.ID, 0)

        def NEWLINE(self):
            return self.getToken(CKBParser.NEWLINE, 0)

        def getRuleIndex(self):
            return CKBParser.RULE_myid

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitMyid" ):
                return visitor.visitMyid(self)
            else:
                return visitor.visitChildren(self)




    def myid(self):

        localctx = CKBParser.MyidContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_myid)
        try:
            self.state = 37
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,3,self._ctx)
            if la_ == 1:
                self.enterOuterAlt(localctx, 1)
                self.state = 32
                localctx.num = self.match(CKBParser.ID)
                self.state = 33
                self.match(CKBParser.T__1)
                self.state = 34
                self.myid()
                pass

            elif la_ == 2:
                self.enterOuterAlt(localctx, 2)
                self.state = 35
                localctx.num = self.match(CKBParser.ID)
                self.state = 36
                self.match(CKBParser.NEWLINE)
                pass


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ConditionalsContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser
            self.name = None # Token

        def condition(self):
            return self.getTypedRuleContext(CKBParser.ConditionContext,0)


        def ID(self):
            return self.getToken(CKBParser.ID, 0)

        def NEWLINE(self, i:int=None):
            if i is None:
                return self.getTokens(CKBParser.NEWLINE)
            else:
                return self.getToken(CKBParser.NEWLINE, i)

        def conditionals(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(CKBParser.ConditionalsContext)
            else:
                return self.getTypedRuleContext(CKBParser.ConditionalsContext,i)


        def getRuleIndex(self):
            return CKBParser.RULE_conditionals

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitConditionals" ):
                return visitor.visitConditionals(self)
            else:
                return visitor.visitChildren(self)




    def conditionals(self):

        localctx = CKBParser.ConditionalsContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_conditionals)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 42
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==15:
                self.state = 39
                self.match(CKBParser.NEWLINE)
                self.state = 44
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 45
            self.match(CKBParser.T__2)
            self.state = 47 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 46
                self.match(CKBParser.NEWLINE)
                self.state = 49 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==15):
                    break

            self.state = 51
            localctx.name = self.match(CKBParser.ID)
            self.state = 55
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==15:
                self.state = 52
                self.match(CKBParser.NEWLINE)
                self.state = 57
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 58
            self.match(CKBParser.T__3)
            self.state = 62
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==15:
                self.state = 59
                self.match(CKBParser.NEWLINE)
                self.state = 64
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 65
            self.condition()
            self.state = 66
            self.match(CKBParser.T__4)
            self.state = 70
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,8,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    self.state = 67
                    self.match(CKBParser.NEWLINE) 
                self.state = 72
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,8,self._ctx)

            self.state = 76
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,9,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    self.state = 73
                    self.conditionals() 
                self.state = 78
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,9,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ConditionContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser
            self.consequent = None # FormulaContext
            self.antecedent = None # FormulaContext

        def condition(self):
            return self.getTypedRuleContext(CKBParser.ConditionContext,0)


        def formula(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(CKBParser.FormulaContext)
            else:
                return self.getTypedRuleContext(CKBParser.FormulaContext,i)


        def NEWLINE(self, i:int=None):
            if i is None:
                return self.getTokens(CKBParser.NEWLINE)
            else:
                return self.getToken(CKBParser.NEWLINE, i)

        def getRuleIndex(self):
            return CKBParser.RULE_condition

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitCondition" ):
                return visitor.visitCondition(self)
            else:
                return visitor.visitChildren(self)




    def condition(self):

        localctx = CKBParser.ConditionContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_condition)
        self._la = 0 # Token type
        try:
            self.state = 104
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,12,self._ctx)
            if la_ == 1:
                self.enterOuterAlt(localctx, 1)
                self.state = 79
                self.match(CKBParser.T__5)
                self.state = 80
                localctx.consequent = self.formula(0)
                self.state = 81
                self.match(CKBParser.T__6)
                self.state = 82
                localctx.antecedent = self.formula(0)
                self.state = 83
                self.match(CKBParser.T__7)
                self.state = 84
                self.match(CKBParser.T__1)
                self.state = 88
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                while _la==15:
                    self.state = 85
                    self.match(CKBParser.NEWLINE)
                    self.state = 90
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)

                self.state = 91
                self.condition()
                pass

            elif la_ == 2:
                self.enterOuterAlt(localctx, 2)
                self.state = 93
                self.match(CKBParser.T__5)
                self.state = 94
                localctx.consequent = self.formula(0)
                self.state = 95
                self.match(CKBParser.T__6)
                self.state = 96
                localctx.antecedent = self.formula(0)
                self.state = 97
                self.match(CKBParser.T__7)
                self.state = 101
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                while _la==15:
                    self.state = 98
                    self.match(CKBParser.NEWLINE)
                    self.state = 103
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)

                pass


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class FormulaContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return CKBParser.RULE_formula

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class OrContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a CKBParser.FormulaContext
            super().__init__(parser)
            self.left = None # FormulaContext
            self.right = None # FormulaContext
            self.copyFrom(ctx)

        def formula(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(CKBParser.FormulaContext)
            else:
                return self.getTypedRuleContext(CKBParser.FormulaContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitOr" ):
                return visitor.visitOr(self)
            else:
                return visitor.visitChildren(self)


    class NegationContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a CKBParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def formula(self):
            return self.getTypedRuleContext(CKBParser.FormulaContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitNegation" ):
                return visitor.visitNegation(self)
            else:
                return visitor.visitChildren(self)


    class VarContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a CKBParser.FormulaContext
            super().__init__(parser)
            self.atom = None # Token
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(CKBParser.ID, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitVar" ):
                return visitor.visitVar(self)
            else:
                return visitor.visitChildren(self)


    class AndContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a CKBParser.FormulaContext
            super().__init__(parser)
            self.left = None # FormulaContext
            self.right = None # FormulaContext
            self.copyFrom(ctx)

        def formula(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(CKBParser.FormulaContext)
            else:
                return self.getTypedRuleContext(CKBParser.FormulaContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitAnd" ):
                return visitor.visitAnd(self)
            else:
                return visitor.visitChildren(self)


    class ParenContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a CKBParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def formula(self):
            return self.getTypedRuleContext(CKBParser.FormulaContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitParen" ):
                return visitor.visitParen(self)
            else:
                return visitor.visitChildren(self)



    def formula(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = CKBParser.FormulaContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 10
        self.enterRecursionRule(localctx, 10, self.RULE_formula, _p)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 114
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [9]:
                localctx = CKBParser.NegationContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 107
                self.match(CKBParser.T__8)
                self.state = 108
                self.formula(5)
                pass
            elif token in [6]:
                localctx = CKBParser.ParenContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 109
                self.match(CKBParser.T__5)
                self.state = 110
                self.formula(0)
                self.state = 111
                self.match(CKBParser.T__7)
                pass
            elif token in [11]:
                localctx = CKBParser.VarContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 113
                localctx.atom = self.match(CKBParser.ID)
                pass
            else:
                raise NoViableAltException(self)

            self._ctx.stop = self._input.LT(-1)
            self.state = 124
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,15,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 122
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,14,self._ctx)
                    if la_ == 1:
                        localctx = CKBParser.AndContext(self, CKBParser.FormulaContext(self, _parentctx, _parentState))
                        localctx.left = _prevctx
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 116
                        if not self.precpred(self._ctx, 4):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 4)")
                        self.state = 117
                        self.match(CKBParser.T__1)
                        self.state = 118
                        localctx.right = self.formula(5)
                        pass

                    elif la_ == 2:
                        localctx = CKBParser.OrContext(self, CKBParser.FormulaContext(self, _parentctx, _parentState))
                        localctx.left = _prevctx
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 119
                        if not self.precpred(self._ctx, 3):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                        self.state = 120
                        self.match(CKBParser.T__9)
                        self.state = 121
                        localctx.right = self.formula(4)
                        pass

             
                self.state = 126
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,15,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx



    def sempred(self, localctx:RuleContext, ruleIndex:int, predIndex:int):
        if self._predicates == None:
            self._predicates = dict()
        self._predicates[5] = self.formula_sempred
        pred = self._predicates.get(ruleIndex, None)
        if pred is None:
            raise Exception("No predicate with index:" + str(ruleIndex))
        else:
            return pred(localctx, predIndex)

    def formula_sempred(self, localctx:FormulaContext, predIndex:int):
            if predIndex == 0:
                return self.precpred(self._ctx, 4)
         

            if predIndex == 1:
                return self.precpred(self._ctx, 3)
         




