import os
import string
from random import choice

from parser.Wrappers import parseQuery


def NotFormula(l):
    f = l.pop()
    l.insert(0, "(!%s)" % f)


def AndFormula(l):
    f1 = l.pop()
    f2 = l.pop()
    l.insert(0, "(%s,%s)" % (f1, f2))


def OrFormula(l):
    f1 = l.pop()
    f2 = l.pop()
    l.insert(0, "(%s;%s)" % (f1, f2))


def makeCKB(conditionals, classes, filename):
    dirname = os.path.dirname(filename)
    if dirname:
        os.makedirs(dirname, exist_ok=True)
    with open(filename, "w+") as f:
        print("signature", file=f)
        print(*classes, sep=",", file=f)
        print("\n", file=f)
        print("conditionals", file=f)
        print("abcd {", file=f)
        print(*conditionals, sep=",\n", file=f)
        print("}", file=f)


def makeConditional(classes, i):
    B = makeSelector(classes, i)
    Bflipped = makeSelector(["!" + v for v in classes], i)
    A = [makeSelector(classes, j) for j in range(i + 1, len(classes))]
    return "(%s | %s)" % (B, ";".join(A + [Bflipped, B]))


def makeSelector(classes, i):
    B = [v for v in classes]
    B[i] = "!" + B[i]
    Bstr = ",".join(B)
    return Bstr


def sampling(classes, filename):
    conditionals = [makeConditional(classes, i) for i, c in enumerate(classes, start=0)]
    # print(conditionals)
    return makeCKB(conditionals, classes, filename)


def createVariables(amount):
    v = set()
    while len(v) < amount:
        nv = "".join([choice(string.ascii_lowercase) for i in range(4)])
        v.add(nv)
    return list(v)


def sampleAsConditionals(classes):
    conditionals = [makeConditional(classes, i) for i, c in enumerate(classes, start=0)]
    COND = {i: parseQuery(c)[1] for i, c in enumerate(conditionals, start=1)}
    return COND


for u in range(5, 200):
    v = createVariables(u)
    conds = sampling(v, "komo/test%i.cl" % u)
