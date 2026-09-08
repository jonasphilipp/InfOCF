#!/usr/bin/env python3
"""
Run c-revision with custom birds knowledge base and all-zero ranking function.

This script demonstrates how to use the c_revision function and allows
for easy experimentation with different configurations.
"""

import os
import sys

# Add the project root to the path
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from pysmt.shortcuts import Not, Symbol
from pysmt.typing import BOOL

from inference.belief_base import BeliefBase
from inference.c_revision import c_inference_pareto_front, c_revision
from inference.conditional import Conditional
from inference.preocf import CustomPreOCF


def create_all_zero_ranking(signature):
    """Create a ranking function where all worlds have rank 0."""
    all_zero_ranks = {}
    for i in range(2 ** len(signature)):
        world_bitstring = format(i, f"0{len(signature)}b")
        all_zero_ranks[world_bitstring] = 0
    return all_zero_ranks


def create_custom_ranking(signature, custom_ranks=None):
    """Create a custom ranking function. If custom_ranks is None, uses all zeros."""
    if custom_ranks is None:
        return create_all_zero_ranking(signature)

    # Validate that all worlds are covered
    expected_worlds = set()
    for i in range(2 ** len(signature)):
        expected_worlds.add(format(i, f"0{len(signature)}b"))

    if set(custom_ranks.keys()) != expected_worlds:
        raise ValueError(f"Custom ranks must cover all {len(expected_worlds)} worlds")

    return custom_ranks


def print_ranking_function(ranks, signature):
    """Print the ranking function in a readable format."""
    print("Ranking function:")
    for world, rank in ranks.items():
        world_desc = []
        for j, var in enumerate(signature):
            if world[j] == "1":
                world_desc.append(var)
            else:
                world_desc.append(f"!{var}")
        print(f"  {world} ({', '.join(world_desc)}): rank {rank}")


def print_conditionals(conditionals, title="Conditionals"):
    """Print conditionals in a readable format."""
    print(f"\n{title}:")
    for idx, cond in conditionals.items():
        print(f"  {idx}: {cond.textRepresentation}")


def print_revision_conditionals(revision_conditionals, title="Revision conditionals"):
    """Print revision conditionals, showing the index used by c_revision."""
    print(f"\n{title}:")
    for cond in revision_conditionals:
        print(f"  Index {cond.index}: {cond.textRepresentation}")


def print_results(model, revision_conditionals):
    """Print the c-revision results in a readable format."""
    if model:
        print("\nC-revision successful!")
        print("Resulting gamma model:")

        sorted_model = dict(sorted(model.items(), key=lambda item: str(item[0])))

        for var_name, value in sorted_model.items():
            print(f"  {var_name}: {value}")

    else:
        print("\nC-revision failed: No satisfying model found!")
        print("This could indicate inconsistency in the constraints.")


def calculate_pareto_front(belief_base):
    """Compute the Pareto front of eta-vectors for the given belief base.

    Delegates to :func:`inference.c_revision.c_inference_pareto_front`.
    """
    return c_inference_pareto_front(belief_base) or None


def print_pareto_front(pareto_vectors):
    """Pretty-print the list of Pareto eta-vectors."""
    if not pareto_vectors:
        print("\nNo Pareto-optimal eta-vectors found (or computation skipped).")
        return

    print("\nPareto front of c-representation (eta impacts):")
    for idx, vec in enumerate(pareto_vectors, 1):
        vec_str = ", ".join(f"eta{j + 1}={val}" for j, val in enumerate(vec))
        print(f"  Solution {idx}: {vec_str}")


def main():
    """Run c-revision with the specified parameters."""

    # ========================================
    # CONFIGURATION
    # ========================================

    signature = ["b", "p", "f"]
    ranks = create_all_zero_ranking(signature)
    print_ranking_function(ranks, signature)

    b = Symbol("b", BOOL)
    p = Symbol("p", BOOL)
    f = Symbol("f", BOOL)

    # Define revision conditionals. The `.index` attribute is now the source of truth.
    # It must be unique and is recommended to be 0-indexed.
    cond1 = Conditional(f, b, "(f|b)")
    cond1.index = 1

    cond2 = Conditional(Not(f), p, "(!f|p)")
    cond2.index = 2

    cond3 = Conditional(b, p, "(b|p)")
    cond3.index = 3

    revision_conditionals = [cond1, cond2, cond3]

    belief_base = BeliefBase(
        signature, {c.index: c for c in revision_conditionals}, "custom_birds"
    )

    preocf = CustomPreOCF(ranks, belief_base, signature)

    print_revision_conditionals(revision_conditionals)

    print("\nRunning c-revision...")
    print("=" * 50)

    model = c_revision(preocf, revision_conditionals, gamma_plus_zero=True)

    print_results(model, revision_conditionals)

    # ----------------------------------------
    # Pareto front of c-representation
    # ----------------------------------------

    pareto_vectors = calculate_pareto_front(belief_base)
    print_pareto_front(pareto_vectors)


if __name__ == "__main__":
    main()
