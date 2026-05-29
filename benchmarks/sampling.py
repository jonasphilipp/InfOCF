from collections import Counter
from random import choice, choices


def sample_operation():
    """
    returns a random operations that works on a list of formulas
    whether the operation is appropriate to do on the list,
    i.e. the list has enough entries, has to be checked by the caller
    """

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

    return choice([OrFormula, AndFormula, NotFormula])


def sampleProperties(properties):
    bits = sampleBits(len(properties))
    return [k for k, b in zip(properties, bits, strict=False) if b == 1]


def sampleFormula(allProperties):
    properties = sampleProperties(allProperties)
    print(properties)
    while len(properties) != 1:
        print(properties)
        op = sample_operation()
        op(properties)
    return properties[0]


def sampleBits(length):
    while not any(bits := choices([0, 1], k=(length))):
        # Resample until at least one bit is set.
        ...
    print(bits)
    return bits


def lookupThenIncrease(counter, obj):
    """
    basically used to get fresh variable names
    assumes the base names dont use any letters, otherwise wont work properly, i.e. collisions could happen
    """
    name = obj + counter[obj]
    counter.update(obj)
    return name


def increaseThenLookup(counter, obj):
    counter.update(obj)
    name = obj + str(counter[obj])
    return name


def lookup(counter, name):
    return name + str(counter[name])


def makeCKB(logbook, properties, conditionals, filename):
    allVars = properties
    for c, i in logbook.items():
        for j in range(i + 1):
            allVars.append(c + str(j))
    with open(filename, "w+") as f:
        print("signature", file=f)
        print(*allVars, sep=",", file=f)
        print("\n", f)
        print("conditionals", file=f)
        print("abcd {", file=f)
        print(*conditionals, sep=",\n", file=f)
        print("}", file=f)


def sampling(classes, properties, iterations, filename):
    logbook = Counter(classes)
    conditionals = [
        "( %s | %s )" % (sampleFormula(properties), lookup(logbook, c)) for c in classes
    ]  # initalizes base cases, so to speak
    for i in range(iterations):
        oldVars = [lookup(logbook, c) for c in classes]
        inheritance = [
            increaseThenLookup(logbook, c)
            for b, c in zip(sampleBits(len(classes)), classes, strict=False)
            if b == 1
        ]
        [
            conditionals.append("(%s | %s)" % (sampleFormula(oldVars), child))
            for child in inheritance
        ]
        [
            conditionals.append("(%s | %s)" % (sampleFormula(properties), i))
            for i in inheritance
        ]
    return makeCKB(logbook, properties, conditionals, filename)


sampling(
    ["b", "c", "d", "e", "f", "g"],
    ["ert", "i", "j", "k", "l", "m", "z", "y"],
    9,
    "test.cl",
)
