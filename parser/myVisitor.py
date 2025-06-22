# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------

import logging
from collections import OrderedDict, Counter

# ---------------------------------------------------------------------------
# Third-party
# ---------------------------------------------------------------------------

from pysmt.shortcuts import Symbol, And, Or, Not, Iff, Bool
from pysmt.typing import BOOL

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------

from .CKBVisitor import CKBVisitor
from inference.belief_base import BeliefBase
from inference.conditional import Conditional

from infocf import get_logger

logger = get_logger(__name__)

from antlr4 import *
from .CKBLexer import CKBLexer
from .CKBParser import CKBParser

class myVisitor(CKBVisitor):
    def visitSignature(self, ctx):
        signature = self.visit(ctx.myid())
        if len(signature) != len(set(signature)):
            raise ValueError("Duplicate variables in signature detected")
        if ('Top' in signature):
            raise ValueError("Top is not an allowed variable name")
        if ('Bottom' in signature):
            raise ValueError("Bottom is not an allowed variable name")
        return signature


    def visitMyid(self,ctx):
        ids =[str(ctx.num.text)]
        nextid = (ctx.myid())
        if nextid != None:
            return ids + self.visit(nextid)
        return ids


    def visitCkbs(self, ctx:CKBParser.CkbsContext):
        counter = Counter()
        order = OrderedDict()
        self.signature=self.visit(ctx.signature())
        self.sigcheck = []
        ckbs = [self.visit(i) for i in ctx.conditionals()]
        self.sigcheck=all([s in self.signature for s in self.sigcheck])
        for ckb in ckbs:
            counter.update([ckb.name])
            newid = counter[ckb.name]
            order.update({(ckb.name, newid): ckb})
        return order




    # Visit a parse tree produced by CKBParser#ckb.
    """
    def visitCkb(self, ctx:CKBParser.CkbContext):
        self.visit(ctx.signature())
        name = str(ctx.name.text)
        conditionals = {i:c for i,c in enumerate(self.visit(ctx.condition()),start=1)}
        return BeliefBase(self.signature, conditionals, name)
    """


    # Visit a parse tree produced by CKBParser#conditionals.
    def visitConditionals(self, ctx:CKBParser.ConditionalsContext):
        name = str(ctx.name.text)
        conditionals=dict()
        if (ctx.condition()!=None):
            conditionals = {i:c for i,c in enumerate(self.visit(ctx.condition()),start=1)}
        #if len(conditionals) < 3:
        #    raise ValueError("Only CKB's with at least 3 conditionals are supported")
        bb=BeliefBase(self.signature, conditionals, name)
        bb.sigcheck=self.sigcheck
        return bb


    # Visit a parse tree produced by CKBParser#StrongConditional.
    def visitCondition(self, ctx:CKBParser.ConditionContext):
        consequent = self.visit(ctx.consequent)
        antecedent = self.visit(ctx.antecedent)
        text = f"({ctx.consequent.getText()}|{ctx.antecedent.getText()})"
        c=Conditional(consequent, antecedent, text, weak = False)
        if ctx.condition() != None:
            return [c] + self.visit(ctx.condition())
        return [c]


    # Visit a parse tree produced by CKBParser#WeakConditional.
    """
    def visitWeakConditional(self, ctx:CKBParser.WeakConditionalContext):
        consequent = self.visit(ctx.consequent)
        antecedent = self.visit(ctx.antecedent)
        return Conditional(consequent, antecedent, weak = True)
    """

    # Visit a parse tree produced by CKBParser#Or.
    def visitOr(self, ctx:CKBParser.OrContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        return Or(left, right)


    # Visit a parse tree produced by CKBParser#Negation.
    def visitNegation(self, ctx:CKBParser.NegationContext):
        return Not(self.visit(ctx.formula()))

    def visitVar(self, ctx:CKBParser.VarContext):
        v = str(ctx.atom.text)
        if v == "Top":
            return Bool(True)
        if v == "Bottom":
            return Bool(False)
        #if v not in self.signature:
        #    raise ValueError("variable %s not defined in signature" % v)
        self.sigcheck.append(v)
        return Symbol(v, BOOL)

    # Visit a parse tree produced by CKBParser#And.
    def visitAnd(self, ctx:CKBParser.AndContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        return And(left, right)

    def visitParen(self, ctx:CKBParser.ParenContext):
        return self.visit(ctx.formula())


def getCondAndVars(f):
    lines = f.split('\n')
    var = lines[1]
    conds = lines[4:-1]
    return len(conds), len(var.split(','))
