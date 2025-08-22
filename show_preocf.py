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

from pysmt.shortcuts import And

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from inference.preocf import PreOCF, ranks2tpo, tpo2ranks
from parser.Wrappers import parse_belief_base, parse_formula, parse_queries

# First, let's load and prepare a belief base
# We'll use the birds example which is small but illustrative
print("=== Creating Belief Base ===")
birds_kb_string = (
    "signature\nb,p,f,w\n\nconditionals\nbirds{\n(f|b),\n(!f|p),\n(b|p),(w|b)\n}"
)

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

# Create a PreOCF using System Z
print("=== Creating PreOCF with System Z Ranking ===")
preocf_birds = PreOCF.init_system_z(belief_base_birds)
print(f"PreOCF created with {len(preocf_birds.ranks)} possible worlds")
print(f"Ranking system: {preocf_birds.ranking_system}")
print(f"Is OCF (all worlds ranked): {preocf_birds.is_ocf()}")
print()

# Compute ranks for specific worlds
print("=== Computing Ranks for Specific Worlds ===")
# Initially worlds have None as their rank, we'll compute some specific ones
worlds_to_check = ["1111", "0000", "1010", "0101"]
worlds_descriptions = [preocf_birds.bv2strtuple(w) for w in worlds_to_check]

print("Before computing ranks:")
print("With internal representation:")
for i, world in enumerate(worlds_to_check):
    print(f"{world}: {preocf_birds.ranks[world]}")
print()

print("With verbose representation (bitvec -> strtuple):")
for i, world in enumerate(worlds_to_check):
    print(
        f"  World {world} {worlds_descriptions[i]}: Rank = {preocf_birds.ranks[world]}"
    )

# Compute ranks for these worlds
for world in worlds_to_check:
    preocf_birds.rank_world(world)

print("\nAfter computing ranks:")
print("With internal representation:")
for world in worlds_to_check:
    print(f"{world}: {preocf_birds.ranks[world]}")
print()

print("With verbose representation (bitvec -> strtuple):")

for i, world in enumerate(worlds_to_check):
    print(
        f"  World {world} {worlds_descriptions[i]}: Rank = {preocf_birds.ranks[world]}"
    )
print()
print(f"Is OCF (all worlds ranked): {preocf_birds.is_ocf()}")
print()

# Compute all ranks
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

# Show ranks in original and verbose format for whole dictionary
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

# Working with formulas and conditionals
print("=== Formula Evaluation ===")
# Parse formulas using parser
formulas_str = ["b", "p", "b,p", "b;p", "!b", "b,!p"]
formulas = {desc: parse_formula(desc) for desc in formulas_str}

print("Formula ranks (minimum rank of any world satisfying the formula):")
for desc, formula in formulas.items():
    rank = preocf_birds.formula_rank(formula)
    print(f"  Formula '{desc}': Rank = {rank}")
print()

# Conditional acceptance
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

# Conditional Acceptance using random_min_c_rep
print("=== Conditional Acceptance (Random Min C-Representation) ===")
# Initialize PreOCF with c-representation
preocf_birds_c = PreOCF.init_random_min_c_rep(belief_base_birds)
# Compute all ranks to prepare for conditional acceptance
actions = preocf_birds_c.compute_all_ranks()
for cond in queries.conditionals.values():
    acceptance_c = preocf_birds_c.conditional_acceptance(cond)
    print(f"  {cond}: {'Accepted' if acceptance_c else 'Rejected'}")
print()

# Conditionalization
print("=== Conditionalization ===")
# Conditionalize on 'b' (bird) using parsed formula
conditionalization = formulas["b"]
print("Conditionalizing on formula: b")

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

# Total Preorder Conversion
print("=== Total Preorder Conversion ===")
# Convert ranks to total preorder
tpo = ranks2tpo(preocf_birds.ranks)
print("Total preorder layers (worlds grouped by rank):")
for i, layer in enumerate(tpo):
    print(f"  Layer {i} (rank {i}): {len(layer)} worlds")
print(tpo)
print()

# Partial TPO demonstration on a non-OCF instance
print("=== Partial PreOCF → TPO (manual ranks only) ===")
# Fresh instance to avoid full ranking side-effects
partial_ocf = PreOCF.init_system_z(belief_base_birds)
# Compute ranks for some worlds only
for w in ["0000", "1111", "0101"]:
    partial_ocf.rank_world(w)
print(f"world, rank: {[(w, partial_ocf.ranks[w]) for w in ['0000', '1111', '0101']]}")
print(f"Is OCF now? {partial_ocf.is_ocf()}")
partial_tpo2 = ranks2tpo(partial_ocf.ranks)
print("Partial total-preorder layers:")
for i, layer in enumerate(partial_tpo2):
    print(f"  Layer {i} (rank {i}) {len(layer)} worlds: {layer}")
print()

# Metadata Storage and Persistence
print("=== Metadata Storage and Persistence ===")
# Store metadata about this experiment
preocf_birds.save_meta("experiment_name", "Birds Knowledge Base Analysis")
preocf_birds.save_meta("author", "PreOCF Demo")
preocf_birds.save_meta("creation_date", "2024-01-15")
preocf_birds.save_meta(
    "analysis_results",
    {
        "total_worlds": len(preocf_birds.ranks),
        "ranking_system": preocf_birds.ranking_system,
        "tpo_layers": len(tpo),
    },
)
preocf_birds.save_meta("tpo_layers", tpo)

print("Stored metadata:")
print(f"  Experiment: {preocf_birds.load_meta('experiment_name')}")
print(f"  Author: {preocf_birds.load_meta('author')}")
print(f"  Date: {preocf_birds.load_meta('creation_date')}")
print(f"  Analysis results: {preocf_birds.load_meta('analysis_results')}")

# Test loading non-existing metadata
missing = preocf_birds.load_meta("non_existing_key", default="<no metadata>")
print(f"  Non-existing key: {missing}")

# Save metadata to disk and reload
print("\nSaving metadata to disk...")
preocf_birds.save_metadata("birds_metadata.json", fmt="json")

# Clear metadata to demonstrate reload
original_metadata = preocf_birds.metadata.copy()
preocf_birds.metadata.clear()
print(f"Metadata cleared, current keys: {list(preocf_birds.metadata.keys())}")

# Reload from disk
preocf_birds.load_metadata("birds_metadata.json")
print(f"Metadata reloaded, keys: {list(preocf_birds.metadata.keys())}")
print(f"Reloaded TPO layers count: {len(preocf_birds.load_meta('tpo_layers'))}")
print()

# Full Object-Level Persistence
print("=== Full Object-Level Persistence ===")
print("Demonstrating complete PreOCF serialization and restoration...")

# Save the entire PreOCF object to disk
print("Saving complete PreOCF object to 'birds_preocf.pkl'...")
preocf_birds.save_ocf("birds_preocf.pkl")
print("✓ Object saved successfully")

# Create a different PreOCF to show the difference
print("\nCreating a different PreOCF (Random Min C-Rep) for comparison...")
preocf_birds_c = PreOCF.init_random_min_c_rep(belief_base_birds)
preocf_birds_c.compute_all_ranks()
preocf_birds_c.save_meta("ranking_system_note", "This uses c-representation")
print(f"C-Rep PreOCF ranking system: {preocf_birds_c.ranking_system}")
print(f"C-Rep PreOCF metadata keys: {list(preocf_birds_c.metadata.keys())}")

# Load the original System Z PreOCF back
print("\nLoading the saved System Z PreOCF...")
loaded_preocf = PreOCF.load_ocf("birds_preocf.pkl")
print("✓ Object loaded successfully")

# Verify the loaded object is identical
print("\nVerifying loaded object integrity:")
print(f"  Ranking system: {loaded_preocf.ranking_system}")
print(f"  Signature: {loaded_preocf.signature}")
print(f"  Number of worlds: {len(loaded_preocf.ranks)}")
print(f"  Is OCF: {loaded_preocf.is_ocf()}")
print(f"  Metadata keys: {list(loaded_preocf.metadata.keys())}")
print(f"  Experiment name: {loaded_preocf.load_meta('experiment_name')}")

# Test that ranks are preserved
sample_worlds = ["1111", "0000", "1010"]
print("\nRank comparison for sample worlds:")
for world in sample_worlds:
    orig_rank = preocf_birds.ranks[world]
    loaded_rank = loaded_preocf.ranks[world]
    match = "✓" if orig_rank == loaded_rank else "✗"
    print(f"  World {world}: Original={orig_rank}, Loaded={loaded_rank} {match}")

# Test conditional acceptance is preserved
print("\nConditional acceptance comparison:")
test_conditional = list(belief_base_birds.conditionals.values())[0]
orig_acceptance = preocf_birds.conditional_acceptance(test_conditional)
loaded_acceptance = loaded_preocf.conditional_acceptance(test_conditional)
match = "✓" if orig_acceptance == loaded_acceptance else "✗"
print(
    f"  {test_conditional}: Original={orig_acceptance}, Loaded={loaded_acceptance} {match}"
)

# Demonstrate state inspection with __getstate__
print("\nObject state inspection:")
state_dict = loaded_preocf.__getstate__()
print(f"  State contains {len(state_dict)} attributes")
print(f"  Key attributes: {[k for k in state_dict.keys() if not k.startswith('_')]}")
print(f"  Internal attributes: {[k for k in state_dict.keys() if k.startswith('_')]}")

# Clean up demonstration files
for file in ["birds_metadata.json", "birds_preocf.pkl"]:
    if os.path.exists(file):
        os.remove(file)
        print(f"Cleaned up: {file}")
print()

# Impact Vector Persistence Demonstration
print("=== Impact Vector Persistence (RandomMinCRepPreOCF) ===")
print("Demonstrating impact vector save/load and export/import functionality...")

try:
    # Create a RandomMinCRepPreOCF with computed impacts
    print("\n1. Creating RandomMinCRepPreOCF with computed impacts...")
    preocf_random = PreOCF.init_random_min_c_rep(belief_base_birds)
    print(f"   Impact vector computed: {preocf_random._impacts}")
    print(f"   Impact vector length: {len(preocf_random._impacts)}")

    # Demonstrate simple save/load with Python lists
    print("\n2. Simple Impact Save/Load (Python lists)...")

    # Save impacts to a Python list
    saved_impacts = preocf_random.save_impacts()
    print(f"   Saved impacts: {saved_impacts}")
    print(f"   Type: {type(saved_impacts)}")

    # Create a new instance and load the impacts
    print("\n   Creating new instance and loading impacts...")
    from inference.preocf import RandomMinCRepPreOCF

    preocf_loaded = RandomMinCRepPreOCF.__new__(RandomMinCRepPreOCF)
    ranks = PreOCF.create_bitvec_world_dict(belief_base_birds.signature)
    PreOCF.__init__(
        preocf_loaded,
        ranks,
        belief_base_birds.signature,
        belief_base_birds.conditionals,
        "random_min_c_rep",
        None,
    )
    preocf_loaded._csp = None
    preocf_loaded._optimizer = None
    preocf_loaded.load_impacts(saved_impacts)

    print(f"   Loaded impacts: {preocf_loaded._impacts}")
    print(f"   Impacts match: {preocf_loaded._impacts == preocf_random._impacts}")

    # Test that both instances produce identical ranks
    print("\n   Verifying rank computation consistency...")
    test_worlds = ["0000", "1111", "1010", "0101"]
    for world in test_worlds:
        orig_rank = preocf_random.rank_world(world)
        loaded_rank = preocf_loaded.rank_world(world)
        match = "✓" if orig_rank == loaded_rank else "✗"
        print(f"   World {world}: Original={orig_rank}, Loaded={loaded_rank} {match}")

    # Demonstrate factory method with list
    print("\n3. Factory Method with Impact List...")
    preocf_factory = RandomMinCRepPreOCF.init_with_impacts_list(
        belief_base_birds, saved_impacts
    )
    print(f"   Factory impacts: {preocf_factory._impacts}")
    print(
        f"   Factory metadata: {preocf_factory.load_meta('impacts_loaded_from_list')}"
    )

    # Demonstrate file-based export/import
    print("\n4. File-based Export/Import...")

    # Export to JSON
    print("   Exporting impacts to JSON...")
    preocf_random.export_impacts("impacts_demo.json", fmt="json")
    print("   ✓ Exported to impacts_demo.json")

    # Export to pickle
    print("   Exporting impacts to pickle...")
    preocf_random.export_impacts("impacts_demo.pkl", fmt="pickle")
    print("   ✓ Exported to impacts_demo.pkl")

    # Import from JSON
    print("\n   Creating new instance and importing from JSON...")
    preocf_json_import = RandomMinCRepPreOCF.__new__(RandomMinCRepPreOCF)
    ranks = PreOCF.create_bitvec_world_dict(belief_base_birds.signature)
    PreOCF.__init__(
        preocf_json_import,
        ranks,
        belief_base_birds.signature,
        belief_base_birds.conditionals,
        "random_min_c_rep",
        None,
    )
    preocf_json_import._csp = None
    preocf_json_import._optimizer = None
    preocf_json_import.import_impacts("impacts_demo.json")

    print(f"   JSON imported impacts: {preocf_json_import._impacts}")
    print(f"   Import source: {preocf_json_import.load_meta('impacts_imported_from')}")

    # Import from pickle using factory method
    print("\n   Using factory method with pickle file...")
    preocf_pickle_factory = RandomMinCRepPreOCF.init_with_impacts(
        belief_base_birds, "impacts_demo.pkl"
    )
    print(f"   Pickle factory impacts: {preocf_pickle_factory._impacts}")

    # Performance comparison demonstration
    print("\n5. Performance Comparison...")
    import time

    # Time the original computation
    print("   Timing original impact computation...")
    start_time = time.time()
    preocf_computed = PreOCF.init_random_min_c_rep(belief_base_birds)
    computation_time = time.time() - start_time
    print(f"   Original computation time: {computation_time:.4f} seconds")

    # Time the loading from list
    print("   Timing impact loading from list...")
    start_time = time.time()
    preocf_list_loaded = RandomMinCRepPreOCF.init_with_impacts_list(
        belief_base_birds, saved_impacts
    )
    list_load_time = time.time() - start_time
    print(f"   List loading time: {list_load_time:.4f} seconds")

    # Time the loading from file
    print("   Timing impact loading from file...")
    start_time = time.time()
    preocf_file_loaded = RandomMinCRepPreOCF.init_with_impacts(
        belief_base_birds, "impacts_demo.json"
    )
    file_load_time = time.time() - start_time
    print(f"   File loading time: {file_load_time:.4f} seconds")

    # Calculate speedup
    if list_load_time > 0:
        list_speedup = computation_time / list_load_time
        print(f"   List loading speedup: {list_speedup:.1f}x faster")

    if file_load_time > 0:
        file_speedup = computation_time / file_load_time
        print(f"   File loading speedup: {file_speedup:.1f}x faster")

    # Demonstrate validation
    print("\n6. Validation and Error Handling...")

    # Test with mismatched belief base
    print("   Testing validation with different belief base...")
    simple_kb = "signature\na,b\n\nconditionals\nsimple{\n(a|b)\n}"
    simple_bb = parse_belief_base(simple_kb)
    simple_belief_base = BeliefBase(
        simple_bb.signature, simple_bb.conditionals, "simple"
    )

    try:
        # This should fail due to size mismatch
        test_preocf = RandomMinCRepPreOCF.__new__(RandomMinCRepPreOCF)
        ranks = PreOCF.create_bitvec_world_dict(simple_belief_base.signature)
        PreOCF.__init__(
            test_preocf,
            ranks,
            simple_belief_base.signature,
            simple_belief_base.conditionals,
            "random_min_c_rep",
            None,
        )
        test_preocf._csp = None
        test_preocf._optimizer = None
        test_preocf.load_impacts(saved_impacts)
        print("   ✗ Validation failed to catch size mismatch")
    except ValueError as e:
        print(f"   ✓ Validation caught size mismatch: {str(e)[:50]}...")

    # Test with invalid impact values
    print("   Testing validation with negative impacts...")
    try:
        preocf_loaded.load_impacts([1, 2, -1, 4])
        print("   ✗ Validation failed to catch negative values")
    except ValueError as e:
        print(f"   ✓ Validation caught negative values: {str(e)[:50]}...")

    # Demonstrate metadata tracking
    print("\n7. Metadata Tracking...")
    print(
        f"   List load metadata: {preocf_loaded.load_meta('impacts_loaded_from_list')}"
    )
    print(
        f"   List load timestamp: {preocf_loaded.load_meta('impacts_load_timestamp')}"
    )
    print(
        f"   File import source: {preocf_json_import.load_meta('impacts_imported_from')}"
    )
    print(
        f"   File import timestamp: {preocf_json_import.load_meta('impacts_import_timestamp')}"
    )

    # Clean up demonstration files
    print("\n8. Cleaning up demonstration files...")
    for file in ["impacts_demo.json", "impacts_demo.pkl"]:
        if os.path.exists(file):
            os.remove(file)
            print(f"   Cleaned up: {file}")

    print("\n✓ Impact vector persistence demonstration completed successfully!")

except Exception as e:
    print(f"\n✗ Impact persistence demonstration failed: {e}")
    print("This is expected if RandomMinCRepPreOCF dependencies are not available.")

    # Clean up any partial files
    for file in ["impacts_demo.json", "impacts_demo.pkl"]:
        if os.path.exists(file):
            os.remove(file)

print()


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
for i, (orig_layer, custom_layer) in enumerate(zip(tpo, tpo_custom, strict=False)):
    print(f"  Layer {i}: Same worlds = {orig_layer == custom_layer}")

# Marginalization
print("\n=== Marginalization ===")
print("Marginalizing the PreOCF by projecting out certain variables")
print("Original signature:", preocf_birds.signature)

# Marginalize by removing 'w' (wings) from the signature
vars_to_remove = {"w"}
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
    print(
        f"  World {world} {preocf_birds.bv2strtuple(world)}: Rank = {preocf_birds.ranks[world]}"
    )

# Initializing with Custom Ranks
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
custom_ranks_dict["00"] = 1

# World '01': a=False, b=True
custom_ranks_dict["01"] = 1

# World '10': a=True, b=False
custom_ranks_dict["10"] = 0

# World '11': a=True, b=True
custom_ranks_dict["11"] = 1

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

from parser.Wrappers import parse_queries as parse_queries_custom

# Test acceptance of conditionals in our custom OCF
print("\nConditional acceptance in custom OCF:")
custom_queries = parse_queries_custom("(b|a),(b|!a),(!b|a),(!b|!a)")
for cond in custom_queries.conditionals.values():
    accepted = custom_preocf.conditional_acceptance(cond)
    print(f"  {cond}: {'Accepted' if accepted else 'Rejected'}")

# Convert to total preorder for visualization
custom_tpo = ranks2tpo(custom_preocf.ranks)
print("\nCustom OCF total preorder layers:")
for i, layer in enumerate(custom_tpo):
    layer_worlds = [custom_preocf.bv2strtuple(w) for w in layer]
    print(f"  Layer {i} (rank {i}): {layer_worlds}")

# Bare Custom OCF Demo (no belief base or signature)
print("\n=== Bare Custom OCF Demo ===")
# Manually define a ranks dict
bare_ranks = {"00": 2, "01": 0, "10": 1, "11": 3}
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
bare_ocf.save_meta("comment", "Bare OCF created for demo")
print("Bare OCF comment:", bare_ocf.load_meta("comment"))


# Demonstrate world acceptance of formulas
print("\n=== World Acceptance of Formulas ===")

# Test acceptance of formulas in our custom OCF
print("\nTesting formula acceptance in custom OCF:")

new_custom_ocf = PreOCF.init_custom({}, None, ["a", "b", "c", "d"])
print(f"new_custom_ocf signature: {new_custom_ocf.signature}")
formula_string = "a,b,c,d"
print(f"formula: {formula_string}")
formula = parse_formula(formula_string)
print(
    f"world 0000 satisfies formula {formula_string}: {new_custom_ocf.world_satisfies_conditionalization('0000', formula)}"
)
print(
    f"world 0001 satisfies formula {formula_string}: {new_custom_ocf.world_satisfies_conditionalization('0001', formula)}"
)
print(
    f"world 0011 satisfies formula {formula_string}: {new_custom_ocf.world_satisfies_conditionalization('0011', formula)}"
)
print(
    f"world 1111 satisfies formula {formula_string}: {new_custom_ocf.world_satisfies_conditionalization('1111', formula)}"
)


# Facts Application (conditionalization-based)
print("\n=== Facts Application (conditionalization-based) ===")

# Non-destructive filtering by building a formula and constructing a new PreOCF
print("Using conditionalization (non-destructive) with facts: {'b': 1, 'p': 0}")
facts_formula_np = parse_formula("b,!p")
filtered_ranks = preocf_birds.compute_conditionalization(facts_formula_np)
filtered_preocf = PreOCF.init_custom(filtered_ranks, belief_base_birds)
print(
    f"Original worlds: {len(preocf_birds.ranks)} | Filtered worlds: {len(filtered_preocf.ranks)}"
)

# Ensure ranks exist and preview a few entries
filtered_preocf.compute_all_ranks()
sample = list(filtered_preocf.ranks.items())[:3]
for world, rank in sample:
    print(f"  world {world} {filtered_preocf.bv2strtuple(world)} -> rank {rank}")

# Demonstrate filtering with another formula (no in-place mutation)
print("\nUsing conditionalization with formula: b & w")
facts_formula = parse_formula("b,w")
print(f"Before: {len(preocf_birds.ranks)} worlds")
filtered_ranks_2 = preocf_birds.compute_conditionalization(facts_formula)
filtered_preocf_2 = PreOCF.init_custom(filtered_ranks_2, belief_base_birds)
print(f"After:  {len(filtered_preocf_2.ranks)} worlds")
filtered_preocf_2.compute_all_ranks()
sample2 = list(filtered_preocf_2.ranks.items())[:3]
for world, rank in sample2:
    print(f"  world {world} {filtered_preocf_2.bv2strtuple(world)} -> rank {rank}")


print("\n=== System Z with Facts (weak consistency) ===")
print(
    "Enforcing facts: {'b': 1, 'p': 0} via (Bottom | !fact) conditionals in last layer"
)
try:
    sz_with_facts = PreOCF.init_system_z(belief_base_birds, facts={"b": 1, "p": 0})
    # Show partition sizes and last layer contents (should include the fact conditionals)
    part_sizes = [len(layer) for layer in sz_with_facts._z_partition]
    print("Partition layer sizes:", part_sizes)
    last_layer = sz_with_facts._z_partition[-1] if sz_with_facts._z_partition else []
    preview = ", ".join(str(c) for c in last_layer[: min(3, len(last_layer))])
    print("Last layer preview:", preview)

    # Optional: show that violating worlds are penalized
    sz_with_facts.compute_all_ranks()
    # Find one world that violates b=1 or p=0, and one that satisfies both
    violating = next(
        (w for w in sz_with_facts.ranks if w[0] == "0" or w[1] == "1"), None
    )
    satisfying = next(
        (w for w in sz_with_facts.ranks if w[0] == "1" and w[1] == "0"), None
    )
    if violating and satisfying:
        print(
            f"satisfying world {satisfying} rank={sz_with_facts.ranks[satisfying]} |"
            f" violating world {violating} rank={sz_with_facts.ranks[violating]}"
        )
except ValueError as e:
    print("Facts inconsistent:", e)


### Show c-revision ###

print("\n\n")
print("=== C-Revision Demonstration ===")
print(
    "C-revision computes gamma_plus/gamma_minus parameters for belief change using conditionals."
)
print(
    "This showcases how to revise an existing ranking function with new conditionals.\n"
)

# Import c-revision functionality
from inference.c_revision import c_revision

# Create a uniform rank 0 PreOCF for demonstration
print("1. Creating uniform rank 0 PreOCF...")
uniform_ranks = PreOCF.create_bitvec_world_dict(belief_base_birds.signature)
for world in uniform_ranks:
    uniform_ranks[world] = 0  # All worlds have rank 0

uniform_preocf = PreOCF.init_custom(uniform_ranks, belief_base_birds)
print(f"Created uniform PreOCF with all {len(uniform_preocf.ranks)} worlds at rank 0")

# Create revision conditionals
revision_conditionals = []
for i, cond in enumerate(belief_base_birds.conditionals.values()):
    rev_cond = Conditional(cond.consequence, cond.antecedence, cond.textRepresentation)
    rev_cond.index = i + 1  # c-revision expects 1-based indexing
    revision_conditionals.append(rev_cond)

print(f"Created {len(revision_conditionals)} revision conditionals:")
for cond in revision_conditionals:
    print(f"  Index {cond.index}: {cond}")
print()

# C-revision with gamma_plus_zero=False
print("2. C-revision with gamma_plus variables (gamma_plus_zero=False)...")
model_with_gamma_plus = c_revision(
    uniform_preocf, revision_conditionals, gamma_plus_zero=False
)

if model_with_gamma_plus:
    print("Found model with gamma_plus and gamma_minus variables:")

    # Extract gamma_plus and gamma_minus vectors
    gamma_plus_vec = tuple(
        model_with_gamma_plus.get(f"gamma+_{i}", 0)
        for i in range(1, len(revision_conditionals) + 1)
    )
    gamma_minus_vec = tuple(
        model_with_gamma_plus.get(f"gamma-_{i}", 0)
        for i in range(1, len(revision_conditionals) + 1)
    )

    print(f"  gamma_plus vector:  {gamma_plus_vec}")
    print(f"  gamma_minus vector: {gamma_minus_vec}")
else:
    print("No feasible model found!")
print()

# C-revision with gamma_plus_zero=True
print("3. C-revision with gamma_plus fixed to zero (gamma_plus_zero=True)...")
print("This focuses on finding minimal gamma_minus parameters.")
model_gamma_plus_zero = c_revision(
    uniform_preocf, revision_conditionals, gamma_plus_zero=True
)

if model_gamma_plus_zero:
    print("Found model with gamma_plus fixed to 0:")

    # Extract gamma_minus vector (gamma_plus are all 0)
    gamma_minus_minimal = tuple(
        model_gamma_plus_zero.get(f"gamma-_{i}", 0)
        for i in range(1, len(revision_conditionals) + 1)
    )
    print(f"  gamma_minus vector: {gamma_minus_minimal}")
else:
    print("No feasible model found!")
print()

# Compare to c-representation
print("4. Comparison to c-representation...")
print(
    "When gamma_plus is fixed to 0, input ranking is uniform 0, c-revision should produce eta-vectors from c-representation with same conditionals."
)

try:
    # Create a c-representation PreOCF for comparison
    preocf_c_rep = PreOCF.init_random_min_c_rep(belief_base_birds)

    # Check if we can access the impacts (eta-vector)
    if hasattr(preocf_c_rep, "_impacts"):
        eta_vector = preocf_c_rep._impacts
        print(f"C-representation eta-vector: {eta_vector}")

        if model_gamma_plus_zero:
            print(f"C-revision gamma_minus:      {gamma_minus_minimal}")

            # Check if they match
            eta_tuple = tuple(eta_vector)
            if eta_tuple == gamma_minus_minimal:
                print(
                    "Perfect match: C-revision gamma_minus equals c-representation eta-vector!"
                )
            else:
                print(
                    "Note: Vectors may differ due to different optimization or indexing."
                )
                print("Both represent the same underlying belief change parameters.")
    else:
        print("C-representation impacts not directly accessible in this instance.")

except Exception as e:
    print(f"C-representation comparison failed: {e}")
    print("This might indicate missing dependencies for c-representation.")
print()

# Summary comparison
print("5. Summary comparison...")
if model_with_gamma_plus and model_gamma_plus_zero:
    print("Comparison of both approaches:")
    print(
        f"  With gamma_plus variables:    gamma_plus={gamma_plus_vec}, gamma_minus={gamma_minus_vec}"
    )
    print(
        f"  With gamma_plus fixed to 0:   gamma_plus=(0,0,0,0), gamma_minus={gamma_minus_minimal}"
    )
    print()
    print("Key insights:")
    print("- gamma_plus_zero=False allows more flexibility in the solution")
    print(
        "- gamma_plus_zero=True focuses on minimal gamma_minus (like c-representation)"
    )
    print("- Both approaches solve the same underlying belief change problem")

print("\n=== C-Revision demonstration completed ===")
print("Key takeaways:")
print("- C-revision computes gamma_plus/gamma_minus parameters for belief change")
print(
    "- gamma_plus_zero=True focuses on minimal gamma_minus (matches c-representation)"
)
print("- Results depend on the initial ranking function and revision conditionals")
print("- C-revision bridges between different approaches to belief change")
print()


# --- Fixed gamma showcase: add a new conditional and pin its gamma value ---
print("=== Fixed Gamma Showcase ===")
print("Demonstrating how to add a new revision conditional and fix its gamma value.")

# Create a simple new revision conditional over existing birds signature via parser (e.g., (f|p))
new_cond = list(parse_queries("(f|p)").conditionals.values())[0]
new_cond.index = len(revision_conditionals) + 1

extended_revision_conditionals = revision_conditionals + [new_cond]

print(f"Added new conditional at index {new_cond.index}: {new_cond}")
print(
    "Fixing gamma_minus for the new conditional to 2 while keeping gamma_plus fixed to 0 (gamma_plus_zero=True)..."
)

from inference.c_revision import c_revision as c_revision_fn

model_fixed = c_revision_fn(
    uniform_preocf,
    extended_revision_conditionals,
    gamma_plus_zero=True,
    fixed_gamma_minus={new_cond.index: 2},
)

if model_fixed:
    gamma_minus_fixed_vec = tuple(
        model_fixed.get(f"gamma-_{i}", 0)
        for i in range(1, len(extended_revision_conditionals) + 1)
    )
    print(f"  gamma_minus (with fixed entry): {gamma_minus_fixed_vec}")
    print(
        f"  Confirm fixed value: gamma-_{{{new_cond.index}}} = {model_fixed.get(f'gamma-_{new_cond.index}')}"
    )
else:
    print(
        "No feasible model found with fixed gamma value (this should be rare for this demo)."
    )
print()

# --- Incremental c-revision compilation demo ---
print("=== Incremental c-revision compilation demo ===")
print(
    "Comparing full recompute vs incremental caches for a short sequence of additions."
)

from inference.c_revision import compile_alt_fast
from inference.c_revision_model import CRevisionModel

# Small signature and all-zero ranks
sig_demo = ["a", "b", "c"]
preocf_demo = PreOCF.init_custom(
    {format(i, "03b"): 0 for i in range(8)}, signature=sig_demo
)

# Base conditionals
from parser.Wrappers import parse_queries as pq_inc

base_conds = list(pq_inc("(b|a),(!b|a)").conditionals.values())
add_conds = list(pq_inc("(c|a),(!c|b)").conditionals.values())

# Ensure each conditional carries a unique index as required by c-revision APIs
for i, cond in enumerate(base_conds, start=1):
    cond.index = i
for j, cond in enumerate(add_conds, start=len(base_conds) + 1):
    cond.index = j

import time

t0 = time.perf_counter()
conds_seq = base_conds[:]
for cond in add_conds:
    conds_seq.append(cond)
    _ = compile_alt_fast(preocf_demo, conds_seq)
full_time = (time.perf_counter() - t0) * 1000.0

model = CRevisionModel.from_preocf_and_conditionals(preocf_demo, base_conds)
t0 = time.perf_counter()
for cond in add_conds:
    model.add_conditional(cond)
    _ = model.to_compilation()
incr_time = (time.perf_counter() - t0) * 1000.0

speedup = full_time / incr_time if incr_time else float("inf")
print(f"Full recompute time: {full_time:.2f} ms")
print(f"Incremental time:   {incr_time:.2f} ms")
print(f"Speedup:            {speedup:.2f}x")
print()


#### This part is important for the student lars told me about


print("\nTesting formula acceptance in a custom preocf_birds OCF:")
# this is how you can create a preocf from a belief base
new_custom_ocf_birds = PreOCF.init_custom({}, belief_base_birds, [])

print(f" belief base signature: {belief_base_birds.signature}")
print(f"belief base conditionals: {belief_base_birds.conditionals}")

# this is how you can create a formula that is the conjunction of all the negated falsifictions of all conditionals in a belief base
formula = And(
    [
        belief_base_birds.conditionals[i].make_not_A_or_B()
        for i in belief_base_birds.conditionals
    ]
)

# this is only to print the formula in a more readable format
formula_string = str(formula)
# exchange | for ; and & for , to match our syntax in print statement, this is not actually changing the formula
formula_string = formula_string.replace("|", ";").replace("&", ",")
print(f"formula: {formula_string}")

# this is how you can check if a world satisfies a formula
print(
    f"world 0000 satisfies formula {formula_string}: {new_custom_ocf_birds.world_satisfies_conditionalization('0000', formula)}"
)
print(
    f"world 0001 satisfies formula {formula_string}: {new_custom_ocf_birds.world_satisfies_conditionalization('0001', formula)}"
)
print(
    f"world 1011 satisfies formula {formula_string}: {new_custom_ocf_birds.world_satisfies_conditionalization('1011', formula)}"
)
print(
    f"world 1101 satisfies formula {formula_string}: {new_custom_ocf_birds.world_satisfies_conditionalization('1101', formula)}"
)
print(
    f"world 1111 satisfies formula {formula_string}: {new_custom_ocf_birds.world_satisfies_conditionalization('1111', formula)}"
)
