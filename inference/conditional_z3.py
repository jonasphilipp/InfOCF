# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Third-party
# ---------------------------------------------------------------------------

from pysmt.shortcuts import Solver
from z3 import And, Not, Or

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------
from inference.conditional import Conditional
from infocf.log_setup import get_logger

logger = get_logger(__name__)


class Conditional_z3(Conditional):
    def __init__(self, consequence, antecedence, textRepresentation, weak=False):
        self.antecedence = antecedence
        self.consequence = consequence
        self.weak = weak
        self.textRepresentation = textRepresentation

    def make_A_then_B(self):
        return And(self.antecedence, self.consequence)

    def make_A_then_not_B(self):
        return And(self.antecedence, Not(self.consequence))

    def make_not_A_or_B(self):
        return Or(Not(self.antecedence), self.consequence)

    @classmethod
    def translate_from_existing(cls, existing):
        with Solver(name="z3") as s:
            antecedence = s.converter.convert(existing.antecedence)
            consequence = s.converter.convert(existing.consequence)
        return cls(consequence, antecedence, existing.textRepresentation, existing.weak)
