# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Third-party
# ---------------------------------------------------------------------------

from pysmt.shortcuts import And, Not, Or

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------


class Conditional:
    def __init__(self, consequence, antecedence, textRepresentation, weak=False):
        self.antecedence = antecedence
        self.consequence = consequence
        self.weak = weak
        self.textRepresentation = textRepresentation
        # Optional external identifier used across the codebase (e.g., as keys
        # in belief bases or intermediate structures). Some callers set it
        # explicitly; others leave it unset.
        self.index: int | None = None

    def make_A_then_B(self):
        return And(self.antecedence, self.consequence)

    def setTexts(self, consequenceText, antecedenceText):
        self.consequenceText = consequenceText
        self.antecedenceText = antecedenceText
        self.consequenceVars = set(str.split(self.consequenceText.translate(a)))  # type: ignore
        self.antecedenceVars = set(str.split(self.antecedenceText.translate(a)))  # type: ignore

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
