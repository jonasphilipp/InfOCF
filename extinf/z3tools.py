
from inference.conditional_z3 import Conditional_z3
from inference.belief_base import BeliefBase




def transform_partition_to_z3(partition):
    return [[Conditional_z3.translate_from_existing(c) for c in p] for p in partition]

def transform_beliefbase_to_z3(bb):
    return bb.transform_to_z3_objects()

def transform_conditional_to_z3(conditional):
    return Conditional_z3.translate_from_existing(conditional)
