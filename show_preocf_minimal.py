"""
Minimal example of PreOCF usage, focused on the core functionality:
1. Creating a PreOCF instance
2. Computing ranks for possible worlds
3. Testing conditional acceptance
"""

from parser.Wrappers import parse_belief_base, parse_queries
from inference.belief_base import BeliefBase
from inference.preocf import PreOCF
from inference.conditional import Conditional
from pysmt.shortcuts import Symbol, Not
from pysmt.typing import BOOL

# Define a simple belief base (birds/penguins example)
kb_string = """signature
b,p,f,w

conditionals
birds{
(f|b),
(!f|p),
(b|p),
(w|b)
}"""

# Parse the belief base and create a BeliefBase object
# Note: Filepaths (.cl files) can also be parsed
belief_base = parse_belief_base(kb_string)

# Print the loaded belief base
print(f"Signature: {belief_base.signature}")
print("Conditionals:")
for idx, cond in belief_base.conditionals.items():
    print(f"  {idx}: {cond}")
print()

# Create a PreOCF using System Z
preocf = PreOCF.init_system_z(belief_base)
print(f"Created PreOCF with {len(preocf.ranks)} possible worlds")

# Compute all ranks
preocf.compute_all_ranks()
print("All world ranks computed")

# Display ranks by value
print(f"Ranks:")
for world, rank in preocf.ranks.items():
    print(f'  {world, rank}')           

# Test acceptance of some conditionals
print("\nConditional acceptance:")
conditional_string = "(f|b),(!f|b),(!f|p),(b|p),(w|b),(f|p)"
# Initialize conditionals using the parser
queries = parse_queries(conditional_string)
print(queries.conditionals)
conditionals = queries.conditionals

for cond in conditionals.values():
    accepted = preocf.conditional_acceptance(cond)
    print(f"  {cond}: {'Accepted' if accepted else 'Rejected'}") 
