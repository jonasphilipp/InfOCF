from pysmt.shortcuts import Solver
from z3 import And, Not, Implies
from inference.conditional import Conditional


class Conditional_z3(Conditional):
    def __init__(self, consequence, antecedence, textRepresentation, weak=False):

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
    
    @classmethod
    def translate_from_existing(cls, existing):
        with Solver(name="z3") as s:
            antecedence = s.converter.convert(existing.antecedence)
            consequence = s.converter.convert(existing.consequence)
        return cls(consequence, antecedence, existing.textRepresentation, existing.weak) 
