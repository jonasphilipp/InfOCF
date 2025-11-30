from pysmt.shortcuts import And, Not,Or, Implies


class Conditional:
    def __init__(self,consequence, antecedence, textRepresentation, weak=False):
        self.antecedence=antecedence
        self.consequence=consequence
        self.weak=weak
        self.textRepresentation = textRepresentation
        self.A = self.antecedence
        self.B = self.consequence

    def verify(self):
        return And(self.A, self.B)

    def falsify(self):
        return And(self.A, Not(self.B))

    def imply(self):
        return Implies(self.A, self.B)

    def make_A_then_B(self):
        return And(self.antecedence, self.consequence)


    def make_A_then_not_B(self):
        return And(self.antecedence, Not(self.consequence))

    def make_B(self):
        return self.consequence

    def __str__(self):
        return self.textRepresentation

    def __repr__(self):
        return self.textRepresentation

