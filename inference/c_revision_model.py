from __future__ import annotations

from typing import Dict, Iterable, List, Optional, Set, Tuple

from pysmt.fnode import FNode

from inference.conditional import Conditional
from inference.preocf import PreOCF


def _literal_info(node: FNode) -> Optional[Tuple[str, int]]:
    """Return (var_name, required_val) if node is a literal, else None."""
    if node.is_symbol():
        return node.symbol_name(), 1
    if node.is_not() and node.arg(0).is_symbol():
        return node.arg(0).symbol_name(), 0
    return None


def _extract_cond_masks(
    cond: Conditional, sig_index: Dict[str, int]
) -> Optional[Tuple[int, int, int, int]]:
    """Return (a_idx, a_val, c_idx, c_val) if antecedence/consequence are literals; else None."""
    lit_a = _literal_info(cond.antecedence)
    lit_c = _literal_info(cond.consequence)
    if lit_a is None or lit_c is None:
        return None
    try:
        a_idx = sig_index[lit_a[0]]
        c_idx = sig_index[lit_c[0]]
    except KeyError:
        return None
    return a_idx, lit_a[1], c_idx, lit_c[1]


class CRevisionModel:
    """Stateful, incremental c-revision compilation model.

    Caches per-world classification (accepted/rejected) for the current set of
    revision conditionals and provides utilities to emit the minima structures
    and CSP without re-running expensive solver checks for unchanged items.
    """

    def __init__(
        self,
        ranking_function: PreOCF,
        revision_conditionals: Iterable[Conditional],
    ) -> None:
        self.ranking_function: PreOCF = ranking_function
        self.signature: List[str] = list(ranking_function.signature)
        self.sig_index: Dict[str, int] = {v: i for i, v in enumerate(self.signature)}

        # Deterministic world order
        self.worlds: List[str] = list(self.ranking_function.ranks.keys())
        self.world_bits: Dict[str, List[int]] = {
            w: [int(b) for b in w] for w in self.worlds
        }

        # Conditionals registry and fast-path masks
        self.conds: Dict[int, Conditional] = {}
        self.masks: Dict[int, Optional[Tuple[int, int, int, int]]] = {}

        # Per-world classification caches
        self.world_acc: Dict[str, Set[int]] = {w: set() for w in self.worlds}
        self.world_rej: Dict[str, Set[int]] = {w: set() for w in self.worlds}

        # Lazy world rank cache to avoid recomputation during to_compilation
        self._rank_cache: Dict[str, int] = {}

        # Initialize
        for cond in revision_conditionals:
            self.add_conditional(cond)

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------
    @classmethod
    def from_preocf_and_conditionals(
        cls, ranking_function: PreOCF, revision_conditionals: Iterable[Conditional]
    ) -> "CRevisionModel":
        return cls(ranking_function, revision_conditionals)

    def add_conditional(self, cond: Conditional) -> None:
        """Add a new conditional with a unique `cond.index` and classify worlds.

        Updates caches; minima are derived on demand via to_compilation().
        """
        if not hasattr(cond, "index"):
            raise ValueError("Conditional must have a unique 'index' attribute")
        idx = int(cond.index)
        if idx in self.conds:
            raise ValueError(f"Conditional index already present: {idx}")

        self.conds[idx] = cond
        self.masks[idx] = _extract_cond_masks(cond, self.sig_index)

        mask = self.masks[idx]
        if mask is None:
            # Fallback to solver-based checks per world
            for w in self.worlds:
                if self.ranking_function.world_satisfies_conditionalization(
                    w, cond.make_A_then_B()
                ):
                    self.world_acc[w].add(idx)
                elif self.ranking_function.world_satisfies_conditionalization(
                    w, cond.make_A_then_not_B()
                ):
                    self.world_rej[w].add(idx)
        else:
            a_idx, a_val, c_idx, c_val = mask
            for w, bits in self.world_bits.items():
                if bits[a_idx] == a_val:
                    if bits[c_idx] == c_val:
                        self.world_acc[w].add(idx)
                    else:
                        self.world_rej[w].add(idx)

    def remove_conditional(self, index: int) -> None:
        """Remove a conditional by index; updates world caches accordingly."""
        if index not in self.conds:
            return
        del self.conds[index]
        if index in self.masks:
            del self.masks[index]
        for w in self.worlds:
            self.world_acc[w].discard(index)
            self.world_rej[w].discard(index)

    # ------------------------------------------------------------------
    # Compilation / CSP emission
    # ------------------------------------------------------------------
    def to_compilation(
        self,
    ) -> Tuple[
        Dict[int, List[Tuple[int, List[int], List[int]]]],
        Dict[int, List[Tuple[int, List[int], List[int]]]],
    ]:
        """Produce (vMin, fMin) like compile_alt_fast, using cached world acc/rej sets.

        Each entry is a list of triples (rank, accepted_other_ids, rejected_other_ids).
        """
        vMin: Dict[int, List[Tuple[int, List[int], List[int]]]] = {
            idx: [] for idx in self.conds.keys()
        }
        fMin: Dict[int, List[Tuple[int, List[int], List[int]]]] = {
            idx: [] for idx in self.conds.keys()
        }

        for w in self.worlds:
            acc = self.world_acc[w]
            rej = self.world_rej[w]
            if not acc and not rej:
                continue
            # Compute rank lazily
            if w in self._rank_cache:
                rank_val = self._rank_cache[w]
            else:
                rank_val = self.ranking_function.rank_world(w)
                self._rank_cache[w] = rank_val

            acc_sorted_all = sorted(acc)
            rej_sorted_all = sorted(rej)

            # Distribute this world to vMin/fMin of the involved indices
            for idx in acc_sorted_all:
                # Filter out self index
                acc_filtered = [i for i in acc_sorted_all if i != idx]
                rej_filtered = rej_sorted_all[:]  # already excludes idx by definition
                vMin[idx].append((rank_val, acc_filtered, rej_filtered))
            for idx in rej_sorted_all:
                acc_filtered = acc_sorted_all[:]  # already excludes idx by definition
                rej_filtered = [i for i in rej_sorted_all if i != idx]
                fMin[idx].append((rank_val, acc_filtered, rej_filtered))

        return vMin, fMin

    def to_csp(
        self,
        *,
        gamma_plus_zero: bool = False,
        fixed_gamma_plus: Optional[Dict[int, int]] = None,
        fixed_gamma_minus: Optional[Dict[int, int]] = None,
    ) -> List[FNode]:
        """Build CSP using current caches via translate_to_csp from c_revision."""
        from inference.c_revision import (
            translate_to_csp,  # local import to avoid cycles
        )

        compilation = self.to_compilation()
        return translate_to_csp(
            compilation,
            gamma_plus_zero,
            fixed_gamma_plus=fixed_gamma_plus,
            fixed_gamma_minus=fixed_gamma_minus,
        )
