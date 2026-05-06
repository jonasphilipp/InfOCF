import os
import random


def makeCKB(conditionals, classes, filename):
    name = os.path.basename(filename).split(".")[0]

    with open(filename, "w+") as f:
        print("signature", file=f)
        print(*classes, sep=",", file=f)
        print("\n", file=f)
        print("conditionals", file=f)
        print(name + " {", file=f)
        print(*conditionals, sep=",\n", file=f)
        print("}", file=f)


def makeConditional(classes, k):
    B, A = makeSelector(classes, k)
    return "(%s | %s)" % (B, A)


def makeSelector(classes, k):
    B = random.sample(classes, k=2 * k)
    Neg = random.choices(["!", "", ""], k=2 * k)
    c1 = "!(" + ",".join([n + b for (n, b) in zip(Neg[:k], B[:k], strict=False)]) + ")"
    # c1='Top'
    c2 = (
        "("
        + ";".join(
            [n + b for (n, b) in zip(Neg[k : k + 2], B[k : k + 2], strict=False)]
        )
        + ")"
    )
    return c2, c1


def sampling(classes, c, k, filename):
    conditionals = [makeConditional(classes, k) for i, c in enumerate(range(c))]
    print(conditionals)
    return makeCKB(conditionals, classes, filename)


v = ["a%i" % i for i in range(50)]
conds = sampling(v, 80, 3, "cnf.cl")
