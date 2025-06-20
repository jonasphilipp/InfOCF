# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------

import logging

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------

from inference.conditional import Conditional

from infocf import get_logger

logger = get_logger(__name__)

class BeliefBase:
    """
    currently only supports strong conditionals
    several functionalities currently exist as multiple implementation within this class.
    The inferior one, that uses if-then-then encoding, will moved somewhere else some day.
    """
    def __init__(self, signature: list[str], conditionals: dict[int, Conditional], name: str) -> None:
        self.signature=signature
        self.conditionals=conditionals
        self.name = name


