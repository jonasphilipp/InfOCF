"""
Consistency diagnostics utilities for PreOCF-compatible belief bases.

Provides three-layer checks:
- Facts-only: whether all provided facts are jointly satisfiable
- Belief base only: consistency under standard and extended (weak) semantics
- Combined (BB + facts as weak constraints): consistency under standard and extended semantics

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


class PartitionStats(TypedDict):
    layers: List[int]
    calls: int
    levels: int


class ModeReport(TypedDict, total=False):
    ok: bool
    stats: PartitionStats


class LayerDiagnostics(TypedDict, total=False):
    present: bool
    standard: ModeReport
    extended: ModeReport


class Diagnostics(TypedDict, total=False):
    facts: Dict[str, Any]
    bb: LayerDiagnostics
    combined: LayerDiagnostics


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


def _to_report(part_or_false, stats_tuple) -> ModeReport:
    if part_or_false is False:
        return {
            "ok": False,
            "stats": {
                "layers": stats_tuple[0],
                "calls": stats_tuple[1],
                "levels": stats_tuple[2],
            },
        }
    return {
        "ok": True,
        "stats": {
            "layers": stats_tuple[0],
            "calls": stats_tuple[1],
            "levels": stats_tuple[2],
        },
    }


def consistency_diagnostics(
    belief_base: BeliefBase,
    *,
    facts: Optional[List[str | FNode]] = None,
    solver: str = "z3",
    reuse: Optional[Dict[str, Tuple[Any, Tuple[List[int], int, int]]]] = None,
    compute_bb: bool = True,
    compute_combined: bool = True,
    compute_facts: bool = True,
    semantics: Literal["standard", "extended", "both"] = "both",
    on_inconsistent: Literal["warn", "raise", "silent"] = "warn",
) -> Diagnostics:
    """Compute three-layer consistency diagnostics with minimal duplication.

    - facts-only satisfiability
    - belief base consistency (standard and extended)
    - combined belief base + facts as weak constraints (standard and extended)

    The `reuse` dict can contain any of the keys: 'base_standard', 'base_extended',
    'combined_standard', 'combined_extended' mapped to a tuple of (partition_or_false, stats_tuple)
    as returned by `consistency`.
    """
    reuse = reuse or {}
    diag: Diagnostics = {}

    # 1) Facts-only
    facts_present = bool(facts)
    if compute_facts:
        try:
            facts_ok = facts_jointly_satisfiable(belief_base.signature, facts or [])
        except Exception as e:
            # Variable validation failures etc. are hard errors
            raise
        diag["facts"] = {"present": facts_present, "consistent": facts_ok}
        if not facts_ok and on_inconsistent == "warn":
            logger.warning(
                "Facts are mutually inconsistent (no model satisfies all facts)"
            )
        if not facts_ok and on_inconsistent == "raise":
            raise ValueError("Facts are mutually inconsistent")

    # 2) BB-only
    if compute_bb:
        bb_layer: LayerDiagnostics = {"present": True}

        # Standard
        if semantics in ("standard", "both"):
            if "base_standard" in reuse:
                part_std, stats_std = reuse["base_standard"]
            else:
                part_std, stats_std = consistency(
                    belief_base, solver=solver, weakly=False
                )
            bb_layer["standard"] = _to_report(part_std, stats_std)
            if bb_layer["standard"]["ok"] is False and on_inconsistent == "warn":
                logger.warning("Belief base inconsistent under standard semantics")
            if bb_layer["standard"]["ok"] is False and on_inconsistent == "raise":
                raise ValueError("Belief base inconsistent under standard semantics")

        # Extended
        if semantics in ("extended", "both"):
            if "base_extended" in reuse:
                part_ext, stats_ext = reuse["base_extended"]
            else:
                part_ext, stats_ext = consistency(
                    belief_base, solver=solver, weakly=True
                )
            bb_layer["extended"] = _to_report(part_ext, stats_ext)

        diag["bb"] = bb_layer

    # 3) Combined
    if compute_combined and facts_present:
        combined_layer: LayerDiagnostics = {"present": True}
        augmented = augment_belief_base_with_facts(belief_base, facts or [])

        # Standard combined
        if semantics in ("standard", "both"):
            if "combined_standard" in reuse:
                c_part_std, c_stats_std = reuse["combined_standard"]
            else:
                c_part_std, c_stats_std = consistency(
                    augmented, solver=solver, weakly=False
                )
            combined_layer["standard"] = _to_report(c_part_std, c_stats_std)

        # Extended combined
        if semantics in ("extended", "both"):
            if "combined_extended" in reuse:
                c_part_ext, c_stats_ext = reuse["combined_extended"]
            else:
                c_part_ext, c_stats_ext = consistency(
                    augmented, solver=solver, weakly=True
                )
            combined_layer["extended"] = _to_report(c_part_ext, c_stats_ext)

        # Policy-based notification
        std_bad = (
            semantics in ("standard", "both")
            and combined_layer.get("standard", {}).get("ok") is False
        )
        ext_bad = (
            semantics in ("extended", "both")
            and combined_layer.get("extended", {}).get("ok") is False
        )
        if (std_bad or ext_bad) and on_inconsistent == "warn":
            logger.warning(
                "Augmented belief base (BB + facts) inconsistent under one or more selected semantics"
            )
        if on_inconsistent == "raise":
            if semantics == "both" and std_bad and ext_bad:
                raise ValueError(
                    "Augmented belief base inconsistent under both standard and extended semantics"
                )
            if semantics == "standard" and std_bad:
                raise ValueError(
                    "Augmented belief base inconsistent under standard semantics"
                )
            if semantics == "extended" and ext_bad:
                raise ValueError(
                    "Augmented belief base inconsistent under extended semantics"
                )

        diag["combined"] = combined_layer
    elif compute_combined:
        # No facts → combined layer not applicable
        diag["combined"] = {"present": False}

    return diag


def format_diagnostics(
    diag: Diagnostics, *, semantics: Literal["standard", "extended", "both"] = "both"
) -> str:
    """Return a concise one-line summary according to selected semantics.

    Examples (extended): "facts=True, bb=True, combined=False"
    """
    facts_ok = diag.get("facts", {}).get("consistent")
    if semantics == "standard":
        bb_ok = diag.get("bb", {}).get("standard", {}).get("ok")
        comb_ok = diag.get("combined", {}).get("standard", {}).get("ok")
        return f"facts={facts_ok}, bb={bb_ok}, combined={comb_ok}"
    if semantics == "extended":
        bb_ok = diag.get("bb", {}).get("extended", {}).get("ok")
        comb_ok = diag.get("combined", {}).get("extended", {}).get("ok")
        return f"facts={facts_ok}, bb={bb_ok}, combined={comb_ok}"
    # both
    bb_std = diag.get("bb", {}).get("standard", {}).get("ok")
    bb_ext = diag.get("bb", {}).get("extended", {}).get("ok")
    comb_std = diag.get("combined", {}).get("standard", {}).get("ok")
    comb_ext = diag.get("combined", {}).get("extended", {}).get("ok")
    return f"facts={facts_ok}, bb(std={bb_std}, ext={bb_ext}), combined(std={comb_std}, ext={comb_ext})"
