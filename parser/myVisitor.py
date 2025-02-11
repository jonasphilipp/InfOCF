

from antlr4 import *
from .CKBLexer import CKBLexer
from .CKBParser import CKBParser
from .CKBVisitor import CKBVisitor

from pysmt.shortcuts import Symbol, And, Or, Not, Iff, Bool
from pysmt.typing import BOOL

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from collections import OrderedDict, Counter



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

"""
E = "../../../../hiwi/Osiak_Anna_2020_Bachelorarbeit_Beispiele/E_Wirbeltiere12/KB_Wirbeltiere12/kb_Wirbeltiere12.cl"
E = "../../../../hiwi/Osiak_Anna_2020_Bachelorarbeit_Beispiele/E_Wirbeltiere12/KB_Wirbeltiere12/kb_Wirbeltiere12.cl"
G = "../../../../hiwi/Osiak_Anna_2020_Bachelorarbeit_Beispiele/G_TZellen6/KB_TZellen6/kb_TZellen6.cl"
i = "N"
n = "abcd"
G = "../../../../hiwi/Osiak_Anna_2020_Bachelorarbeit_Beispiele/"+i+"_"+n+"/KB_"+n+"/kb_"+n+".cl"
F = "../../../../hiwi/Osiak_Anna_2020_Bachelorarbeit_Beispiele/F_Wirbeltiere24/KB_Wirbeltiere24/kb_Wirbeltiere24.cl"
thorax= "../../../../hiwi/thoraxschmerzen.cl"
#tester = "../../../../../../fstAttempt.cl"
tester = "../../../bench/test25cwMinima.cl"
#tester = "test5.cl"
file = tester
with open(file) as f:
    e12 = f.read()
#test = InputStream("signature\nd\t  ,f, k\nconditionals abc{\n(!(f,k)|d),\n(d|f)\n}")
test = InputStream(e12)
lexer = CKBLexer(test)
stream = CommonTokenStream(lexer)
parser = CKBParser(stream)
#=tree = parser.signature()
#tree2= parser.conditionals()
visitor = myVisitor()
E = visitor.visit(parser.ckbs())

from time import time_ns as time
print(' ')
E = E[(n, 0)]
t1 = time()
core =E.compile_constraint_test()
a,b = core
t2 = time()
print(t2-t1)
cond, var = getCondAndVars(e12)
print(cond,var)
sol1 = set()
opt1 = makeOptimizer()
opt1.add(E.translate_experimental())
o1 = [opt1.minimize(Int('eta_%i'%i) ) for i in range(1,cond)]
print(o1)
i = 0
csp = E.translate()
for _,abc in E.vMin.items():
    print(len(abc))
t1=time()
while (sat == opt1.check()):
    i+=1
    print(i)
    m1 = opt1.model()
    sol1.add(tuple([('eta_%i'%i,m1.eval(Int('eta_%i'%i))) for i in range(1,cond)]))
t2 = time()
time1 = t2 - t1
print(time1)

sol2=set()
i = 0
opt2= makeOptimizer()
csp = E.translate()
o2= [opt2.minimize(Int('eta_%i'%i)) for i in range(1,cond)]
t1=time()
while (sat == opt2.check()):
    i+=1
    m1 = opt2.model()
    sol2.add(tuple([('eta_%i'%i,m1.eval(Int('eta_%i'%i))) for i in range(1,cond)]))
    print(i)
t2 = time()
print(" %i conditionals,%i variables" %getCondAndVars(e12))
print("If-then-else encoding, time for all cw-minima:", (t2-t1)/1000/1000/1000)
print("new encoding, time for all cw-minima:", (time1)/1000/1000/1000)
print("solution-sets are equal: ", sol1 == sol2)

"""
