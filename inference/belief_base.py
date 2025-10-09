from inference.conditional import Conditional
from inference.conditional_z3 import Conditional_z3 as Cond

class BeliefBase:
    def __init__(self, signature: list[str], conditionals: dict[int, Conditional], name: str) -> None:
        self.signature=signature
        self.conditionals=conditionals
        self.name = name


    def transform_to_z3_objects(self):
        signature = self.signature
        conditionals = {i:Cond.translate_from_existing(c) for i,c in self.conditionals.items()}
        name = self.name
        return BeliefBase(signature, conditionals, name)


