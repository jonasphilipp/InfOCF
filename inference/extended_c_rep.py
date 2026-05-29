"""
Extended c-representations for weakly consistent belief bases.

This module implements the machinery from

    Haldimann, Beierle, Kern-Isberner.
    "Extending c-Representations and c-Inference for Reasoning with
     Infeasible Worlds."
    NMR 2023, pp. 52-63.

and its journal version

    Haldimann, Beierle, Kern-Isberner.
    "Inductive Inference from Weakly Consistent Belief Bases."
    The Knowledge Engineering Review 40:e8, 2025.

In the extended setting, impacts live in ``N_0 ∪ {∞}`` (Def. 20 / Def. 6).
For a weakly consistent belief base ``Δ`` with extended Z-partition
``EZP(Δ) = (Δ_0, ..., Δ_k, Δ^∞)``, the simplified CSP ``CRS^ex_Σ(Δ)``
(Def. 45 / Def. 11) only carries finite impact variables for the
conditional indices in

    J_Δ  =  { j  |  (B_j|A_j) ∈ Δ \\ Δ^∞  and
                     A_j ∧ ¬B_j ∧ ⋀_{(D|C) ∈ Δ^∞}(¬C ∨ D)  is SAT }

Every other index of ``Δ`` is assigned ``η = ∞`` and contributes only
infeasibility (rank ``∞``) to the induced ranking function.  We
distinguish two reasons for an ``∞`` assignment:

- ``"strict"``:    the conditional lies in ``Δ^∞`` itself (Prop. 42 / 13);
- ``"triggered"``: the conditional can only be falsified by worlds that
                   also falsify some conditional in ``Δ^∞`` — i.e., its
                   falsification *necessarily triggers* a strict conflict.

This module deliberately exposes only the pieces of the construction
that are fully paper-faithful and independent of the concrete CSP
backend (c-inference / c-revision).  The integration into
``c_inference.py`` and ``c_revision.py`` is layered on top in later
phases.
"""

from __future__ import annotations

import math
from typing import Literal, Union

from pysmt.shortcuts import And, Not, Or, Solver

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from infocf.log_setup import get_logger

# Mirror the return type of ``consistency_sat.consistency(..., weakly=True)``:
# either a list-of-layers partition, or ``False`` when Δ is not weakly
# consistent (cf. Prop. 16 / 11 of KER 2024).
ExtendedZPartition = Union[list[list[Conditional]], Literal[False]]

logger = get_logger(__name__)


# ---------------------------------------------------------------------------
# Public sentinel for the ``∞`` impact value.
# ---------------------------------------------------------------------------
# We use ``math.inf`` (a plain float) rather than a custom class so that the
# natural sum formula ``κ(ω) = Σ η_i`` of Def. 20 / Def. 6 keeps working
# unchanged: ``int + math.inf`` yields ``math.inf``.  A single named constant
# makes every ``∞`` use-site greppable and gives us one place to swap the
# sentinel later if we ever need to.
INFINITY: float = math.inf

InfinityReason = Literal["strict", "triggered"]


__all__ = [
    "INFINITY",
    "ExtendedZPartition",
    "InfinityReason",
    "compute_j_delta",
    "delta_infinity_indices",
    "extended_c_inference_pareto_front",
    "extended_c_revision_pareto_front",
]


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def delta_infinity_indices(
    belief_base: BeliefBase,
    z_partition: ExtendedZPartition,
) -> set[int]:
    """Extract the index set of ``Δ^∞`` from an extended Z-partition.

    The extended Z-partition is the value returned by
    ``inference.consistency_sat.consistency(bb, weakly=True)``:

    - a list of layers whose trailing element is ``Δ^∞`` (possibly
      empty, meaning strong consistency), or
    - the literal ``False`` when ``Δ`` is *not* weakly consistent
      (cf. Prop. 16 / 11 of KER 2024).

    The conditional objects in ``z_partition`` are the very same objects
    stored in ``belief_base.conditionals`` — ``consistency(...)`` hands
    them through by reference — so we back-map by object identity rather
    than structural equality.

    Parameters
    ----------
    belief_base : BeliefBase
        Belief base whose indices we want to recover.
    z_partition : list of lists of Conditional, or ``False``
        Extended Z-partition as returned by
        ``consistency(belief_base, weakly=True)``.

    Returns
    -------
    set[int]
        Indices (keys in ``belief_base.conditionals``) of the
        conditionals that belong to ``Δ^∞``.  Empty set when the
        belief base is strongly consistent.

    Raises
    ------
    ValueError
        If ``z_partition is False``, i.e., ``Δ`` is not weakly
        consistent and ``Δ^∞`` is not well-defined in the extended
        c-representation framework.
    """
    if z_partition is False:
        raise ValueError(
            "Δ is not weakly consistent: consistency(..., weakly=True) "
            "returned False, so Δ^∞ is not well-defined and "
            "CRS^ex_Σ(Δ) is undefined (cf. KER 2024, Prop. 41)."
        )
    if not z_partition:
        return set()
    last_layer = z_partition[-1]
    if not last_layer:
        return set()

    id_to_idx = {id(c): idx for idx, c in belief_base.conditionals.items()}
    indices: set[int] = set()
    for c in last_layer:
        idx = id_to_idx.get(id(c))
        if idx is None:
            # This can only happen if the partition was produced from a
            # different belief base than the one we were given — which
            # would silently miscompute J_Δ.  Fail loudly.
            raise ValueError(
                "Δ^∞ contains a conditional that is not present in the "
                "belief base (identity mismatch).  Make sure the "
                "z_partition was computed from the very same belief base."
            )
        indices.add(idx)
    return indices


# ---------------------------------------------------------------------------
# Core: compute J_Δ and the infinity index set
# ---------------------------------------------------------------------------


def compute_j_delta(
    belief_base: BeliefBase,
    z_partition: ExtendedZPartition,
    *,
    solver: str = "z3",
) -> tuple[set[int], set[int], dict[int, InfinityReason]]:
    """Compute ``J_Δ`` and the ``∞``-index set for a weakly consistent BB.

    Implements Definition 45 (KER 2024) / Definition 11 (NMR 2023) of
    the finite-impact index set ``J_Δ``:

        J_Δ = { j | (B_j|A_j) ∈ Δ \\ Δ^∞  and
                    A_j ∧ ¬B_j ∧ ⋀_{(D|C) ∈ Δ^∞}(¬C ∨ D) is SAT }

    A conditional falls outside ``J_Δ`` — and thus receives ``η = ∞`` —
    in exactly two situations:

    - It lies in ``Δ^∞`` itself.  Reason ``"strict"`` (Prop. 42 / 13).
    - It lies in ``Δ \\ Δ^∞`` but every world falsifying it also
      falsifies some conditional in ``Δ^∞``.  Reason ``"triggered"``.

    For a strongly consistent belief base (``Δ^∞ = ∅``) the paper's
    ``CRS^ex_Σ(Δ)`` collapses to the classical ``CR_Σ(Δ)`` with
    ``J_Δ = {1, ..., n}`` — this function returns exactly that so that
    downstream code can use the extended pipeline uniformly without
    regressing the strongly consistent case.

    Parameters
    ----------
    belief_base : BeliefBase
        The belief base ``Δ``.  Must be weakly consistent; callers
        should decide this beforehand (e.g., via
        ``consistency_sat.consistency(..., weakly=True)`` combined with
        Proposition 11 / 16 of KER 2024).
    z_partition : list of lists of Conditional, or ``False``
        Extended Z-partition of ``Δ`` as returned by
        ``consistency(belief_base, weakly=True)``.  Its last layer is
        taken as ``Δ^∞``.  Passing ``False`` raises ``ValueError``
        (see below).
    solver : str, optional
        PySMT solver name used for the ``|Δ| − |Δ^∞|`` satisfiability
        checks (one per non-``Δ^∞`` conditional).  Defaults to
        ``"z3"``.

    Returns
    -------
    j_delta : set[int]
        Conditional indices with finite impact variables in
        ``CRS^ex_Σ(Δ)``.
    infinity_indices : set[int]
        Conditional indices assigned ``η = ∞``.  Disjoint from
        ``j_delta`` and complementary within ``belief_base.conditionals``.
    infinity_reasons : dict[int, {"strict", "triggered"}]
        For each ``i ∈ infinity_indices``, the reason why it is
        assigned ``∞``.

    Raises
    ------
    ValueError
        If ``z_partition is False`` (``Δ`` not weakly consistent —
        ``consistency(..., weakly=True)`` signals this directly), or if
        the material counterpart ``⋀_{(D|C) ∈ Δ^∞}(¬C ∨ D)`` happens
        to be unsatisfiable even though a partition was returned
        (a belt-and-braces check; by Lemma 9 / 10 this should not
        occur for a genuinely weakly consistent belief base).  In both
        cases ``CRS^ex_Σ(Δ)`` is undefined (Prop. 41).
    """
    delta_infty = delta_infinity_indices(belief_base, z_partition)

    infinity_reasons: dict[int, InfinityReason] = dict.fromkeys(delta_infty, "strict")
    infinity_set: set[int] = set(delta_infty)

    all_indices = set(belief_base.conditionals.keys())
    non_infty_candidates = all_indices - delta_infty

    # Strongly consistent fast path: Δ^∞ = ∅ ⇒ J_Δ = all indices, no
    # solver calls needed.  CRS^ex collapses to CR (classical c-rep CSP).
    if not delta_infty:
        return set(all_indices), set(), {}

    # Build the material counterpart of Δ^∞:  ⋀_{(D|C) ∈ Δ^∞} (¬C ∨ D).
    # Intuition: any world satisfying this formula is a world that does
    # not falsify any conditional in Δ^∞.
    material_infty_terms = [
        Or(
            Not(belief_base.conditionals[i].antecedence),
            belief_base.conditionals[i].consequence,
        )
        for i in delta_infty
    ]
    # ``And(*[])`` is ``Bool(True)`` in pysmt, but by construction
    # ``delta_infty`` is non-empty here so ``material_infty_terms`` is
    # non-empty too.
    material_infty = And(*material_infty_terms)

    j_delta: set[int] = set()

    with Solver(name=solver) as s:
        s.add_assertion(material_infty)

        # Proposition 11 / 16 sanity check: if even the material
        # counterpart of Δ^∞ alone is UNSAT, the belief base cannot
        # be weakly consistent (a world that does not falsify Δ^∞
        # would have to exist — see Lemmas 9/10).  Fail loudly rather
        # than silently return an all-infinity result.
        if not s.solve():
            raise ValueError(
                "Δ is not weakly consistent: the material counterpart "
                "of Δ^∞ is unsatisfiable, so no world avoids falsifying "
                "some strict conditional.  CRS^ex_Σ(Δ) is undefined in "
                "this case (cf. KER 2024, Prop. 41)."
            )

        # For each non-Δ^∞ conditional, check whether some world
        # falsifies it without falsifying any conditional in Δ^∞.
        for i in non_infty_candidates:
            cond = belief_base.conditionals[i]
            s.push()
            s.add_assertion(cond.antecedence)
            s.add_assertion(Not(cond.consequence))
            is_sat = s.solve()
            s.pop()

            if is_sat:
                j_delta.add(i)
            else:
                infinity_set.add(i)
                infinity_reasons[i] = "triggered"

    logger.debug(
        "compute_j_delta: |Δ|=%d, |Δ^∞|=%d (strict), |triggered|=%d, |J_Δ|=%d",
        len(all_indices),
        len(delta_infty),
        len(infinity_set) - len(delta_infty),
        len(j_delta),
    )

    assert j_delta.isdisjoint(infinity_set), (
        "internal invariant: J_Δ and infinity_indices must be disjoint"
    )
    assert j_delta | infinity_set == all_indices, (
        "internal invariant: J_Δ ∪ infinity_indices must cover Δ"
    )

    return j_delta, infinity_set, infinity_reasons


# ---------------------------------------------------------------------------
# Pareto-front enumeration for extended c-representations
# ---------------------------------------------------------------------------


def _pad_with_infinity(
    finite_vector: tuple[int, ...] | list[int],
    active_indices_sorted: list[int],
    all_indices_sorted: list[int],
    infinity_indices: set[int],
) -> tuple[int | float, ...]:
    """Widen a CSP solution defined on ``J_Δ`` to a full impact vector.

    Entries at positions corresponding to ``infinity_indices`` become
    :data:`INFINITY`; entries at positions in ``J_Δ`` copy the value
    from ``finite_vector`` (which is given in the order of
    ``active_indices_sorted``).
    """
    finite_by_idx = dict(zip(active_indices_sorted, finite_vector, strict=True))
    padded: list[int | float] = []
    for i in all_indices_sorted:
        if i in infinity_indices:
            padded.append(INFINITY)
        else:
            padded.append(int(finite_by_idx[i]))
    return tuple(padded)


def _dedup_and_pad(
    finite_solutions: list[dict[str, int]],
    *,
    variable_prefix: str,
    active_indices_sorted: list[int],
    all_indices_sorted: list[int],
    infinity_set: set[int],
    max_solutions: int | None,
) -> list[tuple[int | float, ...]]:
    """Deduplicate, cap and pad finite Pareto solutions.

    ``solve_pareto_front`` currently re-emits the same Pareto-optimal
    model on successive ``z3.Optimize.check()`` calls when the Pareto
    front has a single element (or a single free variable) — see
    ``infocfweb2.0/InfOCF/inference/c_revision.py::solve_pareto_front``.
    Until that is fixed upstream, we deduplicate padded vectors and
    honour ``max_solutions`` ourselves.  This is also semantically
    correct: two different internal ``z3`` models that induce the
    same impact vector should count as the same c-representation
    for the purposes of the Pareto front.
    """
    padded: list[tuple[int | float, ...]] = []
    seen: set[tuple[int | float, ...]] = set()
    for sol in finite_solutions:
        finite_vector = tuple(
            sol.get(f"{variable_prefix}{i}", 0) for i in active_indices_sorted
        )
        vec = _pad_with_infinity(
            finite_vector,
            active_indices_sorted,
            all_indices_sorted,
            infinity_set,
        )
        if vec in seen:
            continue
        seen.add(vec)
        padded.append(vec)
        if max_solutions is not None and len(padded) >= max_solutions:
            break
    return padded


def extended_c_inference_pareto_front(
    belief_base: BeliefBase,
    *,
    z_partition: "ExtendedZPartition | None" = None,
    max_solutions: int | None = None,
    solver: str = "z3",
    pmaxsat_solver: str = "rc2",
) -> list[tuple[int | float, ...]]:
    """Enumerate Pareto-minimal extended impact vectors via MaxSAT c-inference.

    This is the weakly-consistent counterpart of
    :func:`inference.c_revision.c_inference_pareto_front`.  For a
    strongly consistent belief base it produces exactly the same Pareto
    front (up to sorting); for a weakly consistent belief base it
    realises ``CRS^ex_Σ(Δ)`` (KER 2024, Def. 45 / NMR 2023, Def. 11) by
    running ``CInference.compile_constraint`` with
    ``active_indices = J_Δ`` and
    ``infinity_indices = Δ^∞ ∪ triggered``, then invoking the same
    pysmt / z3 Pareto optimisation as the classical path on the
    restricted eta space.

    The returned vectors have length ``|Δ|`` and are aligned with
    ``sorted(belief_base.conditionals.keys())``.  Positions
    corresponding to strict or triggered conditionals are
    :data:`INFINITY` (a ``float``); all other positions are ``int``.

    Parameters
    ----------
    belief_base : BeliefBase
        Belief base ``Δ``.  Must be weakly consistent.
    z_partition : ExtendedZPartition or None, optional
        Pre-computed extended Z-partition.  When ``None`` (default),
        the partition is computed internally via
        ``consistency(belief_base, solver=..., weakly=True)``.
    max_solutions : int or None, optional
        Cap on the number of Pareto-optimal vectors returned.
    solver : str, optional
        SMT solver name (default ``"z3"``).
    pmaxsat_solver : str, optional
        MaxSAT solver backend name (default ``"rc2"``).

    Returns
    -------
    list[tuple[int | float, ...]]
        Each tuple is one Pareto-optimal extended impact vector,
        ordered by conditional index.  Empty list when no feasible
        solution exists (should not occur for weakly consistent
        belief bases).

    Raises
    ------
    ValueError
        If ``belief_base`` is not weakly consistent.
    """
    # Lazy imports to avoid import cycles:
    #   extended_c_rep → c_inference would be fine in isolation, but
    #   c_inference is imported indirectly from many modules that also
    #   import extended_c_rep in Phase 3+.  Keeping the dependency
    #   here local makes the top-level import graph acyclic.
    from inference.c_inference import CInference  # noqa: PLC0415
    from inference.c_revision import solve_pareto_front  # noqa: PLC0415
    from inference.consistency_sat import consistency  # noqa: PLC0415
    from inference.inference_manager import (  # noqa: PLC0415
        create_epistemic_state,
    )
    from inference.tseitin_transformation import (  # noqa: PLC0415
        TseitinTransformation,
    )

    if z_partition is None:
        z_partition, _ = consistency(belief_base, solver=solver, weakly=True)
    if z_partition is False:
        raise ValueError(
            "belief_base is not weakly consistent: extended c-inference is undefined."
        )

    j_delta, infinity_set, _reasons = compute_j_delta(
        belief_base, z_partition, solver=solver
    )

    all_indices_sorted = sorted(belief_base.conditionals.keys())
    active_indices_sorted = sorted(j_delta)

    # Edge case: J_Δ = ∅ means every conditional is strict or triggered.
    # The unique extended c-representation has η = (∞, ..., ∞)
    # (Proposition 23 of KER 2024).
    if not active_indices_sorted:
        return [
            tuple(INFINITY for _ in all_indices_sorted),
        ]

    # Build the epistemic state and CNF encodings needed by the
    # MaxSAT compilation.  We deliberately bypass
    # ``Inference.preprocess_belief_base`` because that path asserts
    # strong consistency and does not accept the ``active_indices`` /
    # ``infinity_indices`` hooks.
    epistemic_state = create_epistemic_state(
        belief_base,
        inference_system="c-inference",
        smt_solver=solver,
        pmaxsat_solver=pmaxsat_solver,
        weakly=True,
    )
    c_inf = CInference(epistemic_state)
    TseitinTransformation(epistemic_state).belief_base_to_cnf(True, True, True)
    c_inf.compile_constraint(
        deadline=None,
        active_indices=j_delta,
        infinity_indices=infinity_set,
    )
    base_csp = c_inf.translate(active_indices=j_delta)

    minimize_vars = [f"eta_{i}" for i in active_indices_sorted]
    finite_solutions = solve_pareto_front(
        base_csp, minimize_vars, max_solutions=max_solutions
    )

    return _dedup_and_pad(
        finite_solutions,
        variable_prefix="eta_",
        active_indices_sorted=active_indices_sorted,
        all_indices_sorted=all_indices_sorted,
        infinity_set=infinity_set,
        max_solutions=max_solutions,
    )


def extended_c_revision_pareto_front(
    belief_base: BeliefBase,
    *,
    z_partition: "ExtendedZPartition | None" = None,
    max_solutions: int | None = None,
    solver: str = "z3",
) -> list[tuple[int | float, ...]]:
    """Enumerate Pareto-minimal extended impact vectors via world-based c-revision.

    This is the c-revision analogue of
    :func:`extended_c_inference_pareto_front`: for a strongly
    consistent belief base it reproduces
    :func:`inference.c_revision.c_revision_pareto_front_vectors`;
    for a weakly consistent belief base it feeds the extended
    ``active_indices`` / ``infinity_indices`` restriction to
    :func:`inference.c_revision.compile_alt_fast` and
    :func:`inference.c_revision.translate_to_csp`.

    Parameters
    ----------
    belief_base, z_partition, max_solutions, solver
        See :func:`extended_c_inference_pareto_front`.

    Returns
    -------
    list[tuple[int | float, ...]]
        Pareto-optimal extended impact vectors, each aligned with
        ``sorted(belief_base.conditionals.keys())``.

    Raises
    ------
    ValueError
        If ``belief_base`` is not weakly consistent.
    """
    from inference.c_revision import (  # noqa: PLC0415
        compile_alt_fast,
        solve_pareto_front,
        translate_to_csp,
    )
    from inference.consistency_sat import consistency  # noqa: PLC0415
    from inference.preocf import CustomPreOCF  # noqa: PLC0415

    if z_partition is None:
        z_partition, _ = consistency(belief_base, solver=solver, weakly=True)
    if z_partition is False:
        raise ValueError(
            "belief_base is not weakly consistent: extended c-revision is undefined."
        )

    j_delta, infinity_set, _reasons = compute_j_delta(
        belief_base, z_partition, solver=solver
    )

    all_indices_sorted = sorted(belief_base.conditionals.keys())
    active_indices_sorted = sorted(j_delta)

    if not active_indices_sorted:
        return [tuple(INFINITY for _ in all_indices_sorted)]

    # Build an all-zero baseline PreOCF over 2^|Σ| worlds.  The ranks
    # are only used by compile_alt_fast for the minima triples'
    # ``rank_val`` field; for the extended pareto front of a belief
    # base we start from a zero ranking (same convention as
    # c_revision_pareto_front_vectors).
    sig = belief_base.signature
    n = len(sig)
    ranks = {format(i, f"0{n}b"): 0 for i in range(2**n)}
    preocf = CustomPreOCF(ranks, belief_base, sig)

    # Clone the conditionals so compile_alt_fast can freely set their
    # ``index`` attribute (which ``Conditional`` leaves unset by default
    # after parsing).
    revision_conditionals: list[Conditional] = []
    for idx, cond in belief_base.conditionals.items():
        rc = Conditional(cond.consequence, cond.antecedence, cond.textRepresentation)
        rc.index = idx
        revision_conditionals.append(rc)

    compilation = compile_alt_fast(
        preocf,
        revision_conditionals,
        active_indices=j_delta,
        infinity_indices=infinity_set,
    )
    csp = translate_to_csp(
        compilation,
        gamma_plus_zero=True,
        active_indices=j_delta,
    )

    minimize_vars = [f"gamma-_{i}" for i in active_indices_sorted]
    finite_solutions = solve_pareto_front(
        csp, minimize_vars, max_solutions=max_solutions
    )

    return _dedup_and_pad(
        finite_solutions,
        variable_prefix="gamma-_",
        active_indices_sorted=active_indices_sorted,
        all_indices_sorted=all_indices_sorted,
        infinity_set=infinity_set,
        max_solutions=max_solutions,
    )
