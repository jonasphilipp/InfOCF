"""
calculate extended z partition for the birds002 knowledge base.

signature: p, b, f, w, a
conditionals:
  (f | b)       - birds fly
  (!f | p)      - penguins don't fly
  (Bottom | p,!b) - penguins that are not birds lead to contradiction
  (w | b)       - birds have wings
"""

import logging
import warnings

# suppress verbose logging and warnings for cleaner output
logging.getLogger("inference").setLevel(logging.WARNING)
warnings.filterwarnings("ignore")

from inference.consistency_sat import consistency
from inference.inference_manager import InferenceManager
from inference.preocf import PreOCF
from parser.Wrappers import parse_belief_base, parse_queries

# define the knowledge base string
kb_string = """
signature
   p, b, f, w, a

conditionals
birds002{
   (f | b),
   (!f | p),
   (Bottom | p,!b),
   (w | b)
}
"""

# parse the belief base
belief_base = parse_belief_base(kb_string)

print("=== Knowledge Base ===")
print(f"Signature: {belief_base.signature}")
print(f"Number of conditionals: {len(belief_base.conditionals)}")
print("Conditionals:")
for idx, cond in belief_base.conditionals.items():
    print(f"  {idx}: {cond}")
print()

# calculate the extended z partition directly using consistency function
print("=== Extended Z Partition (raw) ===")
partition, stats = consistency(belief_base, solver="z3", weakly=True)

if partition:
    print(f"Partition stats: layers={stats[0]}, calls={stats[1]}, levels={stats[2]}")
    print(f"Number of layers: {len(partition)}")
    print()
    for i, layer in enumerate(partition):
        # mark the last layer as infinity if extended
        if i == len(partition) - 1 and len(layer) == 0:
            print(f"  Layer {i} (∞): [] (empty - KB is consistent)")
        elif i == len(partition) - 1:
            print(f"  Layer {i} (∞): {[str(c) for c in layer]}")
        else:
            print(f"  Layer {i}: {[str(c) for c in layer]}")
else:
    print("Knowledge base is inconsistent!")
print()

# create a PreOCF with extended System Z for more detailed output
print("=== Extended System Z PreOCF ===")
preocf = PreOCF.init_system_z(belief_base, extended=True)
print(preocf.summary())
print()

# detailed layer information with conditionals
print("=== Partition Layers with Conditionals ===")
print(preocf.format_layers_with_conditionals())
print()

# partition statistics
print("=== Partition Statistics ===")
print(f"Uses extended partition: {preocf.uses_extended_partition}")
print(f"Has infinity partition: {preocf.has_infinity_partition}")
print(f"Infinity partition index: {preocf.infinity_partition_index}")
print(f"Layer sizes: {preocf.partition_layer_sizes()}")
print()

# access infinity partition specifically
print("=== Infinity Partition ===")
inf_part = preocf.infinity_partition
if inf_part is not None:
    print(f"  Conditionals in infinity layer: {[str(c) for c in inf_part]}")
else:
    print("  No infinity partition (not extended mode)")
print()

# diagnostics
print("=== Diagnostics ===")
diag = preocf.diagnostics
if diag:
    for key, val in diag.items():
        print(f"  {key}: {val}")
else:
    print("  No diagnostics available")
print()

# inference with query (b | p,f) - "if penguin and flies, then bird"
print("=== Inference ===")
query_string = "(b | p,f)"
print(f"Query: {query_string}")
print("  Meaning: if something is a penguin and flies, is it a bird?")
print()

# parse the query
query = parse_queries(query_string)
query_cond = list(query.conditionals.values())[0]
print(f"Parsed query: {query_cond}")
print(f"  Antecedence: {query_cond.antecedence}")
print(f"  Consequence: {query_cond.consequence}")
print()

# perform inference using System Z (standard mode)
print("--- Standard System Z Inference ---")
try:
    manager = InferenceManager(belief_base, "system-z", weakly=False)
    result_df = manager.inference(query)
    for _, row in result_df.iterrows():
        entailed = row["result"]
        print(f"  {query_string}: {'Entailed' if entailed else 'Not entailed'}")
except AssertionError as e:
    print(f"Cannot perform standard inference: {e}")
    print("  (KB is not strictly consistent due to Bottom conditional)")
print()

# perform inference using System Z (weakly/extended mode)
print("--- Extended System Z Inference (weakly=True) ---")

# enable debug output for System Z internals
from inference.system_z import SystemZ

SystemZ.DEBUG = True

manager_ext = InferenceManager(belief_base, "system-z", weakly=True)
result_ext_df = manager_ext.inference(query)

SystemZ.DEBUG = False  # disable after inference

for _, row in result_ext_df.iterrows():
    entailed = row["result"]
    print(
        f"\n  Final answer: {query_string}: {'Entailed' if entailed else 'Not entailed'}"
    )
