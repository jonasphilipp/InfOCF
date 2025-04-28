"""
In this file we demonstrate the use of the PreOCF module to work with ordinal conditional functions.

INTRODUCTION TO PREOCF:
-----------------------
PreOCF (Pre-Ordinal Conditional Function) represents a belief state about possible worlds using a
ranking function. It assigns non-negative integers (ranks) to each possible world, where:
- Lower ranks indicate more plausible worlds
- Rank 0 is assigned to the most plausible worlds
- Higher ranks indicate less plausible worlds

This ranking is used to evaluate formulas and conditionals:
- The rank of a formula is the minimum rank of any world that satisfies it
- A conditional (B|A) is accepted if worlds satisfying A∧B have lower rank than worlds satisfying A∧¬B

PreOCF provides powerful tools for belief representation and nonmonotonic reasoning. It implements
system Z, one of the most prominent approaches for nonmonotonic reasoning with conditionals. The
ranking expresses a preference relation over possible worlds that reflects the conditional beliefs.

KEY FEATURES:
- System Z ranking computation
- Formula evaluation and conditional acceptance testing
- Conditionalization (focusing on worlds satisfying a formula)
- Marginalization (projecting to a smaller signature)
- Conversion between ranks and total preorders (TPO)

This showcase demonstrates all these features using the classic birds/penguins example.
"""

import os
from inference import belief_base
from parser.Wrappers import parse_belief_base, parse_queries, parse_formula
from inference.belief_base import BeliefBase
from inference.preocf import PreOCF, ranks2tpo, tpo2ranks
from inference.conditional import Conditional
from pysmt.shortcuts import Symbol, Not, And, Or
from pysmt.typing import BOOL
from BitVector import BitVector

# 1. First, let's load and prepare a belief base
# We'll use the birds example which is small but illustrative
print("=== Creating Belief Base ===")
birds_kb_string = "signature\nb,p,f,w\n\nconditionals\nbirds{\n(f|b),\n(!f|p),\n(b|p),(w|b)\n}"

# Parse the belief base string
# Note: Filepaths (.cl files) can also be parsed
belief_base_birds = parse_belief_base(birds_kb_string)

# Print information about the belief base
print(f"Signature: {belief_base_birds.signature}")
print(f"Number of conditionals: {len(belief_base_birds.conditionals)}")
print("Conditionals:")
for idx, cond in belief_base_birds.conditionals.items():
    print(f"  {idx}: {cond}")
print()

# 2. Create a PreOCF using System Z
print("=== Creating PreOCF with System Z Ranking ===")
preocf_birds = PreOCF.init_system_z(belief_base_birds)
print(f"PreOCF created with {len(preocf_birds.ranks)} possible worlds")
print(f"Ranking system: {preocf_birds.ranking_system}")
print(f"Is OCF (all worlds ranked): {preocf_birds.is_ocf()}")
print()

# 3. Compute ranks for specific worlds
print("=== Computing Ranks for Specific Worlds ===")
# Initially worlds have None as their rank, we'll compute some specific ones
worlds_to_check = ['1111', '0000', '1010', '0101']
worlds_descriptions = [preocf_birds.bv2strtuple(w) for w in worlds_to_check]

print("Before computing ranks:")
print('With internal representation:')
for i, world in enumerate(worlds_to_check):
    print(f'{world}: {preocf_birds.ranks[world]}')
print()

print('With verbose representation (bitvec -> strtuple):')
for i, world in enumerate(worlds_to_check):
    print(f"  World {world} {worlds_descriptions[i]}: Rank = {preocf_birds.ranks[world]}")

# Compute ranks for these worlds
for world in worlds_to_check:
    preocf_birds.rank_world(world)

print("\nAfter computing ranks:")
print('With internal representation:')
for world in worlds_to_check:
    print(f'{world}: {preocf_birds.ranks[world]}')
print()

print('With verbose representation (bitvec -> strtuple):')

for i, world in enumerate(worlds_to_check):
    print(f"  World {world} {worlds_descriptions[i]}: Rank = {preocf_birds.ranks[world]}")
print()
print(f"Is OCF (all worlds ranked): {preocf_birds.is_ocf()}")
print()
# 4. Compute all ranks
print("=== Computing All Ranks ===")
preocf_birds.compute_all_ranks()
print()
print(f"Is OCF (all worlds ranked): {preocf_birds.is_ocf()}")
print()
# Group worlds by rank for readability
ranks_by_value = {}
for world, rank in preocf_birds.ranks.items():
    if rank not in ranks_by_value:
        ranks_by_value[rank] = []
    ranks_by_value[rank].append(world)

print("Ranks distribution:")
for rank, worlds in sorted(ranks_by_value.items()):
    worlds_desc = [preocf_birds.bv2strtuple(w) for w in worlds[:3]]
    print(f"  Rank {rank}: {len(worlds)} worlds (e.g., {worlds_desc})")
print()

# 5. Show ranks in original and verbose format for whole dictionary 
print("=== Original Representation ===")
for world, rank in preocf_birds.ranks.items():
    print(world, rank)
print()

print("=== Verbose Representation ===")
verbose_ranks = preocf_birds.ranks_verbose
print("Example verbose world representations:")
for world_tuple, rank in list(verbose_ranks.items())[:5]:
    print(world_tuple, rank)
print()

# 6. Working with formulas and conditionals
print("=== Formula Evaluation ===")
# Parse formulas using parser
formulas_str = ["b", "p", "b,p", "b;p", "!b", "b,!p"]
formulas = {desc: parse_formula(desc) for desc in formulas_str}

print("Formula ranks (minimum rank of any world satisfying the formula):")
for desc, formula in formulas.items():
    rank = preocf_birds.formula_rank(formula)
    print(f"  Formula '{desc}': Rank = {rank}")
print()

# 7. Conditional acceptance
print("=== Conditional Acceptance ===")
conditional_string = "(f|b),(!f|p),(b|p),(w|b),(f|p),(w|p)"
# Initialize conditionals using the parser
queries = parse_queries(conditional_string)
print(queries.conditionals)

print("Testing conditional acceptance:")
for cond in queries.conditionals.values():
    acceptance = preocf_birds.conditional_acceptance(cond)
    print(f"  {cond}: {'Accepted' if acceptance else 'Rejected'}")
print()

# 8. Conditionalization
print("=== Conditionalization ===")
# Conditionalize on 'b' (bird) using parsed formula
conditionalization = formulas["b"]
print(f"Conditionalizing on formula: b")

# Filter worlds satisfying the conditionalization
filtered_worlds = preocf_birds.filter_worlds_by_conditionalization(conditionalization)
print(f"Number of worlds satisfying condition: {len(filtered_worlds)}")

# Get conditionalized ranks
conditionalized_ranks = preocf_birds.conditionalize_existing_ranks(conditionalization)
print("Conditionalized ranks (worlds satisfying the condition):")
for world, rank in list(conditionalized_ranks.items()):
    world_desc = preocf_birds.bv2strtuple(world)
    print(f"  World {world} {world_desc}: Rank = {rank}")
print()

# 9. Total Preorder Conversion
print("=== Total Preorder Conversion ===")
# Convert ranks to total preorder
tpo = ranks2tpo(preocf_birds.ranks)
print("Total preorder layers (worlds grouped by rank):")
for i, layer in enumerate(tpo):
    print(f"  Layer {i} (rank {i}): {len(layer)} worlds")
print(tpo)

# Persisting data in the PreOCF instance
preocf_birds.save("tpo_layers", tpo)
print("Stored total preorder layers in persistence. Retrieved:", preocf_birds.load("tpo_layers"))

missing = preocf_birds.load("non_existing_key", default="<no data>")
print("Attempt to load non-existing key gives:", missing)

# Save persistence to disk and reload
preocf_birds.save_persistence("birds_state.json", fmt="json")
# Reset store to show reload works
preocf_birds._persistence.clear()
preocf_birds.load_persistence("birds_state.json")
print("Reloaded from disk, tpo_layers len:", len(preocf_birds.load("tpo_layers")))

# Convert back to ranks with a different ranking function
def custom_rank_function(layer_num):
    return layer_num * 10  # Multiply rank by 10

custom_ranks = tpo2ranks(tpo, custom_rank_function)
print("\nCustom ranks using function layer_num * 10:")
custom_ranks_by_value = {}
for world, rank in custom_ranks.items():
    if rank not in custom_ranks_by_value:
        custom_ranks_by_value[rank] = []
    custom_ranks_by_value[rank].append(world)

for rank, worlds in sorted(custom_ranks_by_value.items()):
    print(f"  Rank {rank}: {len(worlds)} worlds")

# Verify that the structure is preserved
tpo_custom = ranks2tpo(custom_ranks)
print("\nVerifying structure preservation:")
for i, (orig_layer, custom_layer) in enumerate(zip(tpo, tpo_custom)):
    print(f"  Layer {i}: Same worlds = {orig_layer == custom_layer}")

# 10. Marginalization
print("\n=== Marginalization ===")
print("Marginalizing the PreOCF by projecting out certain variables")
print("Original signature:", preocf_birds.signature)

# Marginalize by removing 'w' (wings) from the signature
vars_to_remove = {'w'}
print(f"Variables to remove: {vars_to_remove}")

# Create marginalized PreOCF
marginalized_preocf = preocf_birds.marginalize(vars_to_remove)
print(f"Marginalized signature: {marginalized_preocf.signature}")
print(f"Number of worlds in marginalized PreOCF: {len(marginalized_preocf.ranks)}")

# Compute marginalized ranks
marginalized_preocf.compute_all_ranks()

# Show example of marginalized worlds
print("\nExamples of marginalized worlds and their ranks:")
for world, rank in list(marginalized_preocf.ranks.items()):
    world_desc = marginalized_preocf.bv2strtuple(world)
    print(f"  World {world} {world_desc}: Rank = {rank}")

# Let's verify that marginalization preserves the structure
# For each marginalized world, original worlds that map to it should all have the same rank
print("\nTesting marginalization properties:")

# Take a marginalized world and find all original worlds that map to it
test_marginalized_world = list(marginalized_preocf.ranks.keys())[5]
print(f"Testing marginalized world: {test_marginalized_world}")

# Find original worlds that would map to this marginalized world
# (they should have the same values for non-marginalized variables)
matching_original_worlds = []
for orig_world in preocf_birds.ranks.keys():
    # Remove the marginalized variable position from comparison
    # For simplicity, assuming 'w' is the last variable in the signature
    if orig_world[:-1] == test_marginalized_world:
        matching_original_worlds.append(orig_world)

print(f"Matching original worlds: {matching_original_worlds}")
print("Ranks of matching original worlds:")
for world in matching_original_worlds:
    print(f"  World {world} {preocf_birds.bv2strtuple(world)}: Rank = {preocf_birds.ranks[world]}")

# 11. Initializing with Custom Ranks
print("\n=== Custom OCF Initialization ===")
print("Creating a PreOCF with custom ranks")

# Create a new belief base
custom_kb_string = "signature\na,b\n\nconditionals\ncustom{\n(a|b),\n(!a|!b)\n}"
custom_belief_base = parse_belief_base(custom_kb_string)

print(f"Custom belief base signature: {custom_belief_base.signature}")
print("Custom belief base conditionals:")
for idx, cond in custom_belief_base.conditionals.items():
    print(f"  {idx}: {cond}")

# Create an empty rank dictionary for all possible worlds
custom_ranks_dict = PreOCF.create_bitvec_world_dict(custom_belief_base.signature)
print(f"Created empty ranks dictionary with {len(custom_ranks_dict)} worlds")

# World '00': a=False, b=False
custom_ranks_dict['00'] = 1

# World '01': a=False, b=True
custom_ranks_dict['01'] = 1

# World '10': a=True, b=False
custom_ranks_dict['10'] = 0

# World '11': a=True, b=True 
custom_ranks_dict['11'] = 1

# Create a PreOCF with these custom ranks
custom_preocf = PreOCF.init_custom(custom_ranks_dict, custom_belief_base)
print(f"Custom PreOCF created with ranking system: {custom_preocf.ranking_system}")

# Check if it's a valid OCF
print(f"Is valid OCF: {custom_preocf.is_ocf()}")

# Display the ranks in verbose format
print("\nCustom PreOCF ranks:")
for world, rank in custom_preocf.ranks.items():
    world_desc = custom_preocf.bv2strtuple(world)
    print(f"  World {world} {world_desc}: Rank = {rank}")

# Create symbols for checking conditional acceptance with custom PreOCF
a = Symbol('a', BOOL)
b = Symbol('b', BOOL)

# Test acceptance of conditionals in our custom OCF
print("\nConditional acceptance in custom OCF:")
custom_conditionals = [
    Conditional(b, a, "(b|a)"),
    Conditional(b, Not(a), "(b|!a)"),
    Conditional(Not(b), a, "(!b|a)"),
    Conditional(Not(b), Not(a), "(!b|!a)")
]

for cond in custom_conditionals:
    accepted = custom_preocf.conditional_acceptance(cond)
    print(f"  {cond}: {'Accepted' if accepted else 'Rejected'}")

# Convert to total preorder for visualization
custom_tpo = ranks2tpo(custom_preocf.ranks)
print("\nCustom OCF total preorder layers:")
for i, layer in enumerate(custom_tpo):
    layer_worlds = [custom_preocf.bv2strtuple(w) for w in layer]
    print(f"  Layer {i} (rank {i}): {layer_worlds}")

# 12. Bare Custom OCF Demo (no belief base or signature)
print("\n=== Bare Custom OCF Demo ===")
# Manually define a ranks dict
bare_ranks = {'00': 2, '01': 0, '10': 1, '11': 3}
# Initialize a custom PreOCF directly from ranks only
bare_ocf = PreOCF.init_custom(bare_ranks)
print("Signature:", bare_ocf.signature)
print("Conditionals:", bare_ocf.conditionals)
print("Is valid OCF:", bare_ocf.is_ocf())
print("Raw ranks:", bare_ocf.ranks)
# compute_all_ranks on custom should simply return the preset ranks
print("Computed all ranks:", bare_ocf.compute_all_ranks())
# Convert to total preorder and back
bare_tpo = ranks2tpo(bare_ocf.ranks)
print("Total preorder layers:", bare_tpo)
recomputed = tpo2ranks(bare_tpo, lambda layer: layer)
print("Recomputed ranks from TPO (identity function):", recomputed)

# Demonstrate persistence with bare_ocf
bare_ocf.save("comment", "Bare OCF created for demo")
print("Bare OCF comment:", bare_ocf.load("comment")) 
