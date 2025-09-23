"""
Consistency diagnostics utilities for PreOCF-compatible belief bases.

This module provides an efficient diagnostic that computes the following
booleans depending on two switches, `extended` and `uses_facts`:

- facts_consistent: facts are jointly satisfiable
- belief_base_consistent: belief base consistent
- belief_base_weakly_consistent: belief base weakly consistent
- combination_consistent: combination (BB + facts) is consistent
- combination_infinity_increase: (only for extended=True and uses_facts=True)
  whether the size of the ∞-partition increased after adding facts

Notes on efficiency:
- When extended=True, a single extended partition run is reused to derive
  both belief_base_weakly_consistent and belief_base_consistent (the latter via
  checking if the last layer is empty).
- For combined checks, only one run is done for the selected mode
  (standard or extended) and reused for the infinity-size comparison.

The functions operate purely on `BeliefBase` and lists of facts (strings or FNode),
making them reusable across different PreOCF implementations.
"""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Literal, Optional, Tuple, TypedDict

from pysmt.fnode import FNode
from pysmt.shortcuts import FALSE, And, Not, Solver, get_free_variables

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from inference.consistency_sat import consistency
from infocf.log_setup import get_logger
from parser.Wrappers import parse_formula

logger = get_logger(__name__)


class Diagnostics(TypedDict, total=False):
    facts_consistent: Optional[bool]
    belief_base_consistent: Optional[bool]
    belief_base_weakly_consistent: Optional[bool]
    combination_consistent: Optional[bool]
    combination_infinity_increase: Optional[bool]


def _parse_fact(entry: str | FNode) -> FNode:
    if isinstance(entry, FNode):
        return entry
    if isinstance(entry, str):
        return parse_formula(entry)
    raise TypeError("facts entries must be formula strings or pysmt FNode objects")


def _validate_fact_vars(signature: Iterable[str], phi: FNode) -> None:
    free_vars = {v.symbol_name() for v in get_free_variables(phi)}
    unknown = free_vars.difference(set(signature))
    if unknown:
        raise ValueError(f"unknown variable(s) in facts formula: {sorted(unknown)}")


def facts_jointly_satisfiable(
    signature: Iterable[str], facts: List[str | FNode]
) -> bool:
    """Return True iff all facts are jointly satisfiable.

    Facts may be strings in project syntax or FNode objects.
    Variables are validated against the provided signature.
    """
    if not facts:
        return True
    formulas: List[FNode] = []
    for entry in facts:
        phi = _parse_fact(entry)
        _validate_fact_vars(signature, phi)
        formulas.append(phi)
    with Solver(name="z3") as s:
        s.add_assertion(And(formulas) if len(formulas) > 1 else formulas[0])
        return s.solve()


def build_fact_conditionals(
    signature: Iterable[str],
    facts: List[str | FNode],
    *,
    start_index: int = 0,
) -> Dict[int, Conditional]:
    """Convert facts φ into weak constraints of the form (FALSE | ¬φ).

    Returns a dict indexed from start_index+1 upward with Conditional objects.
    """
    fact_conditionals: Dict[int, Conditional] = {}
    next_index = start_index + 1
    for entry in facts:
        phi = _parse_fact(entry)
        _validate_fact_vars(signature, phi)

        antecedent = Not(phi)
        # Pretty-print antecedent using project syntax: '|' -> ';', '&' -> ','
        antecedent_str = str(antecedent).replace(" | ", "; ").replace(" & ", ", ")

        fact_cond = Conditional(
            consequence=FALSE(),
            antecedence=antecedent,
            textRepresentation=f"(Bottom|{antecedent_str})",
        )
        # Assign a 1-based index as used across the project
        fact_cond.index = next_index  # type: ignore[attr-defined]
        fact_conditionals[next_index] = fact_cond
        next_index += 1

    return fact_conditionals


def augment_belief_base_with_facts(
    bb: BeliefBase, facts: List[str | FNode]
) -> BeliefBase:
    """Return a new BeliefBase that includes weak constraints for each provided fact.

    Each fact φ is turned into (FALSE | ¬φ), biasing models toward satisfying φ.
    """
    if not facts:
        return bb
    existing = dict(bb.conditionals)
    start_idx = max(existing.keys(), default=0)
    new_conds = build_fact_conditionals(bb.signature, facts, start_index=start_idx)
    augmented = dict(existing)
    augmented.update(new_conds)
    return BeliefBase(bb.signature, augmented, f"{bb.name}-with-facts")


from typing import List as _List


def _last_layer_size(partition: _List[_List[Any]] | Literal[False]) -> int:
    return len(partition[-1]) if partition and isinstance(partition, list) else 0


def consistency_diagnostics(
    belief_base: BeliefBase,
    *,
    extended: bool,
    uses_facts: bool,
    facts: Optional[List[str | FNode]] = None,
    solver: str = "z3",
    precomputed: Optional[Dict[str, Tuple[Any, Tuple[List[int], int, int]]]] = None,
    on_inconsistent: Literal["warn", "raise", "silent"] = "warn",
) -> Diagnostics:
    """Compute diagnostics per the (extended, uses_facts) mode.

    Case matrix:
    1) extended=False, uses_facts=False → belief_base_consistent
    2) extended=False, uses_facts=True  → facts_consistent, belief_base_consistent,
                                          combination_consistent
    3) extended=True,  uses_facts=False → belief_base_consistent,
                                          belief_base_weakly_consistent
    4) extended=True,  uses_facts=True  → facts_consistent, belief_base_consistent,
                                          belief_base_weakly_consistent,
                                          combination_consistent,
                                          combination_infinity_increase
    """
    precomputed = precomputed or {}
    diag: Diagnostics = {}

    # Optional facts check
    if uses_facts:
        if not facts:
            raise ValueError("uses_facts=True requires non-empty 'facts'")
        try:
            f_ok = facts_jointly_satisfiable(belief_base.signature, facts)
        except Exception:
            # parsing/validation errors bubble up
            raise
        diag["facts_consistent"] = f_ok
        if f_ok is False and on_inconsistent == "warn":
            logger.warning(
                "Facts are mutually inconsistent (no model satisfies all facts)"
            )
        if f_ok is False and on_inconsistent == "raise":
            raise ValueError("Facts are mutually inconsistent")

    # Base (belief base only)
    base_part_ext: _List[_List[Any]] | Literal[False] = False
    if extended:
        # Try to reuse extended partition if provided
        if "base_extended" in precomputed:
            base_part_ext, _ = precomputed["base_extended"]
        else:
            base_part_ext, _ = consistency(belief_base, solver=solver, weakly=True)

        if base_part_ext is False:
            diag["belief_base_weakly_consistent"] = False
            diag["belief_base_consistent"] = False
        else:
            diag["belief_base_weakly_consistent"] = True
            # Standard consistency is equivalent to empty last layer in extended partition
            diag["belief_base_consistent"] = _last_layer_size(base_part_ext) == 0
    else:
        # Standard-only check
        if "base_standard" in precomputed:
            base_part_std, _ = precomputed["base_standard"]
        else:
            base_part_std, _ = consistency(belief_base, solver=solver, weakly=False)
        diag["belief_base_consistent"] = base_part_std is not False

    # Combined (BB + facts as weak constraints)
    if uses_facts:
        augmented = augment_belief_base_with_facts(belief_base, facts or [])
        if extended:
            if "combined_extended" in precomputed:
                comb_part_ext, _ = precomputed["combined_extended"]
            else:
                comb_part_ext, _ = consistency(augmented, solver=solver, weakly=True)
            diag["combination_consistent"] = comb_part_ext is not False

            # Infinity partition size comparison only if both are partitions
            if (comb_part_ext is not False) and (base_part_ext is not False):
                diag["combination_infinity_increase"] = _last_layer_size(
                    comb_part_ext
                ) > _last_layer_size(base_part_ext)
        else:
            if "combined_standard" in precomputed:
                comb_part_std, _ = precomputed["combined_standard"]
            else:
                comb_part_std, _ = consistency(augmented, solver=solver, weakly=False)
            diag["combination_consistent"] = comb_part_std is not False

    # Backward-compatible short-key aliases used by existing tests
    alias_map = {
        "f_consistent": "facts_consistent",
        "bb_consistent": "belief_base_consistent",
        "bb_w_consistent": "belief_base_weakly_consistent",
        "c_consistent": "combination_consistent",
        "c_infinity_increase": "combination_infinity_increase",
    }
    for short_key, long_key in alias_map.items():
        if long_key in diag:
            diag[short_key] = diag[long_key]  # type: ignore[index]

    return diag


def format_diagnostics(diag: Diagnostics) -> str:
    """Return a concise one-line summary of available booleans.

    Example: "facts_consistent=True, belief_base_consistent=True, belief_base_weakly_consistent=True, combination_consistent=False, combination_infinity_increase=False"
    Missing values are shown as None.
    """
    # Prefer short alias keys expected by tests; fall back to long names
    f_ok = diag.get("f_consistent", diag.get("facts_consistent"))
    bb_ok = diag.get("bb_consistent", diag.get("belief_base_consistent"))
    bbw_ok = diag.get("bb_w_consistent", diag.get("belief_base_weakly_consistent"))
    c_ok = diag.get("c_consistent", diag.get("combination_consistent"))
    inf_inc = diag.get("c_infinity_increase", diag.get("combination_infinity_increase"))
    return (
        f"facts={f_ok}, bb={bb_ok}, bb_w={bbw_ok}, "
        f"combined={c_ok}, inf_inc={inf_inc}"
    )


def format_diagnostics_verbose(diag: Diagnostics) -> str:
    """Return a verbose, explicit diagnostics string using long key names.

    Example: "facts_consistent=True, belief_base_consistent=True, belief_base_weakly_consistent=True, combination_consistent=False, combination_infinity_increase=False"
    Missing values are shown as None.
    """
    f_ok = diag.get("facts_consistent")
    bb_ok = diag.get("belief_base_consistent")
    bbw_ok = diag.get("belief_base_weakly_consistent")
    c_ok = diag.get("combination_consistent")
    inf_inc = diag.get("combination_infinity_increase")
    return (
        f"facts_consistent={f_ok}, belief_base_consistent={bb_ok}, "
        f"belief_base_weakly_consistent={bbw_ok}, combination_consistent={c_ok}, "
        f"combination_infinity_increase={inf_inc}"
    )
