# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------


from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from infocf.log_setup import get_logger

logger = get_logger(__name__)


class Queries(BeliefBase):
    """
    Initializes Queries object either from dict or from BeliefBase object
    """

    # Explicit attributes to satisfy type checker on subclasses
    conditionals: dict[int, Conditional]
    name: str
    signature: list[str]

    def __init__(self, queries: dict[int, Conditional] | BeliefBase) -> None:
        # Initialise with safe defaults; overwritten below
        super().__init__(signature=[], conditionals={}, name="queries")
        if isinstance(queries, dict):
            self._from_dict(queries)
        elif isinstance(queries, BeliefBase):
            self._from_belief_base(queries)

    def _from_dict(self, query_dict: dict[int, Conditional]) -> None:
        self.conditionals = query_dict
        self.name = "from_dict"

    def _from_belief_base(self, belief_base: BeliefBase) -> None:
        self.conditionals = belief_base.conditionals
        self.name = belief_base.name
        self.signature = belief_base.signature
