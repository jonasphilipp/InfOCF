# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Third-party
# ---------------------------------------------------------------------------

from typing import cast

from pysmt.shortcuts import Solver
from z3 import And, BoolRef, Not, Or

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------
from inference.conditional import Conditional
from infocf.log_setup import get_logger

logger = get_logger(__name__)


class Conditional_z3(Conditional):
    antecedence: BoolRef
    consequence: BoolRef

    def __init__(
        self,
        consequence: BoolRef,
        antecedence: BoolRef,
        textRepresentation: str,
        weak: bool = False,
    ):
        super().__init__(
            consequence=consequence,
            antecedence=antecedence,
            textRepresentation=textRepresentation,
            weak=weak,
        )

    def make_A_then_B(self) -> BoolRef:
        return cast(BoolRef, And(self.antecedence, self.consequence))

    def make_A_then_not_B(self) -> BoolRef:
        return cast(BoolRef, And(self.antecedence, Not(self.consequence)))

    def make_not_A_or_B(self) -> BoolRef:
        return cast(BoolRef, Or(Not(self.antecedence), self.consequence))

    @classmethod
    def translate_from_existing(cls, existing: Conditional) -> "Conditional_z3":
        with Solver(name="z3") as s:
            antecedence = s.converter.convert(existing.antecedence)
            consequence = s.converter.convert(existing.consequence)
        return cls(consequence, antecedence, existing.textRepresentation, existing.weak)
