"""
calculate extended p-entailment for the birds002 knowledge base.

signature: p, b, f, w, a
conditionals:
  (f | b)       - birds fly
  (!f | p)      - penguins don't fly
  (Bottom | p,!b) - penguins that are not birds lead to contradiction
  (w | b)       - birds have wings

query: (b | p,f) - if something is a penguin and flies, is it a bird?
"""

import logging
import warnings

# suppress verbose logging and warnings for cleaner output
logging.getLogger("inference").setLevel(logging.WARNING)
warnings.filterwarnings("ignore")

from inference.consistency_sat import consistency
from inference.inference_manager import InferenceManager
from inference.p_entailment import PEntailment
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

# calculate the extended z partition for reference
print("=== Extended Z Partition (for reference) ===")
partition, stats = consistency(belief_base, solver="z3", weakly=True)

if partition:
    print(f"Partition stats: layers={stats[0]}, calls={stats[1]}, levels={stats[2]}")
    print(f"Number of layers: {len(partition)}")
    for i, layer in enumerate(partition):
        if i == len(partition) - 1 and len(layer) == 0:
            print(f"  Layer {i} (∞): [] (empty - KB is consistent)")
        elif i == len(partition) - 1:
            print(f"  Layer {i} (∞): {[str(c) for c in layer]}")
        else:
            print(f"  Layer {i}: {[str(c) for c in layer]}")
else:
    print("Knowledge base is inconsistent!")
print()

# diagnostics
print("=== Diagnostics ===")
preocf = PreOCF.init_system_z(belief_base, extended=True)
diag = preocf.diagnostics
if diag:
    for key, val in diag.items():
        print(f"  {key}: {val}")
print()

# inference query
print("=== P-Entailment Inference ===")
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

# perform inference using P-Entailment (standard mode)
print("--- Standard P-Entailment ---")
try:
    manager = InferenceManager(belief_base, "p-entailment", weakly=False)
    result_df = manager.inference(query)
    for _, row in result_df.iterrows():
        entailed = row["result"]
        print(f"  {query_string}: {'P-Entailed' if entailed else 'Not P-Entailed'}")
except AssertionError as e:
    print(f"Cannot perform standard inference: {e}")
print()

# perform inference using P-Entailment (weakly/extended mode - Pinf)
print("--- Extended P-Entailment (weakly=True, Pinf Algorithm) ---")

# enable debug output for P-Entailment internals
PEntailment.DEBUG = True

manager_ext = InferenceManager(belief_base, "p-entailment", weakly=True)
result_ext_df = manager_ext.inference(query)

PEntailment.DEBUG = False  # disable after inference

for _, row in result_ext_df.iterrows():
    entailed = row["result"]
    print(
        f"\n  Final answer: {query_string}: {'P-Entailed' if entailed else 'Not P-Entailed'}"
    )
