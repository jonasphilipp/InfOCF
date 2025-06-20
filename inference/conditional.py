# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------

import logging

# ---------------------------------------------------------------------------
# Third-party
# ---------------------------------------------------------------------------

from pysmt.shortcuts import Symbol, Not, And, Or, Iff, is_unsat, is_sat
from pysmt.typing import BOOL

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------

from infocf import get_logger

logger = get_logger(__name__)

class Conditional:
    def __init__(self,consequence, antecedence, textRepresentation, weak=False):
        self.antecedence=antecedence
        self.consequence=consequence
        self.weak=weak
        self.textRepresentation = textRepresentation

    def make_A_then_B(self):
        return And(self.antecedence, self.consequence)

    def setTexts(self,consequenceText, antecedenceText):
        self.consequenceText=consequenceText
        self.antecedenceText=antecedenceText
        self.consequenceVars = set(str.split(self.consequenceText.translate(a))) # type: ignore
        self.antecedenceVars = set(str.split(self.antecedenceText.translate(a))) # type: ignore


    def make_A_then_not_B(self):
        return And(self.antecedence, Not(self.consequence))

    def make_B(self):
        return self.consequence
    
    def make_not_A_or_B(self):
        return Or(Not(self.antecedence), self.consequence)
    
    def __str__(self):
        return self.textRepresentation

    def __repr__(self):
        return self.textRepresentation

