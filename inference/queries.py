from inference.belief_base import BeliefBase

class Queries(BeliefBase):
    """
    Initializes Queries object either from dict or from BeliefBase object
    """
    def __init__(self, queries: dict | BeliefBase) -> None:
        if type(queries) == dict:
            self._from_dict(queries)
        elif type(queries) == BeliefBase:
            self._from_belief_base(queries)

    def _from_dict(self, query_dict: dict) -> None:
        self.conditionals = query_dict
        self.name = 'from_dict'

    def _from_belief_base(self, belief_base: BeliefBase) -> None:
        self.conditionals = belief_base.conditionals
        self.name = belief_base.name
        self.signature = belief_base.signature


