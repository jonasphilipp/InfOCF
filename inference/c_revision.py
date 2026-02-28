from __future__ import annotations

import logging
from typing import TYPE_CHECKING, Any, Protocol, cast

if TYPE_CHECKING:
    from inference.belief_base import BeliefBase

import z3
from pysmt.fnode import FNode
from pysmt.shortcuts import GE, GT, Int, Plus, Solver, Symbol
from pysmt.typing import INT

from inference.c_inference import freshVars, minima_encoding
from inference.conditional import Conditional
from inference.preocf import PreOCF
from infocf.log_setup import get_logger

"""Avoid importing CRevisionModel at type-check time to prevent import cycles."""

# Configure module logger
logger = get_logger(__name__)

"""
ATTENTION: This file is not tested yet sufficiently, and the implementation is not complete.
"""

# Cache for gamma symbol objects (avoids recreating identical FNodes)
_gamma_sym_cache: dict[str, FNode] = {}


def _gamma(name: str) -> FNode:
    sym = _gamma_sym_cache.get(name)
    if sym is None:
        sym = Symbol(name, INT)
        _gamma_sym_cache[name] = sym
    return sym


WorldTriple = list[object]


def compile(
    ranking_function: PreOCF, revision_conditionals: list[Conditional]
) -> list[list[dict[str, WorldTriple]]]:
    outer_list: list[list[dict[str, WorldTriple]]] = []
    for rev_cond in revision_conditionals:
        inner_list: list[dict[str, WorldTriple]] = [dict(), dict()]
        for world in ranking_function.ranks.keys():
            if ranking_function.world_satisfies_conditionalization(
                world, rev_cond.make_A_then_B()
            ):
                branch_index = 0
            elif ranking_function.world_satisfies_conditionalization(
                world, rev_cond.make_A_then_not_B()
            ):
                branch_index = 1
            else:
                continue

            rank_val = ranking_function.rank_world(world)
            inner_list[branch_index][world] = [rank_val, [], []]

            for cond in revision_conditionals:
                if ranking_function.world_satisfies_conditionalization(
                    world, cond.make_A_then_B()
                ):
                    cast(list[int], inner_list[branch_index][world][1]).append(
                        cast(int, cond.index)
                    )
                elif ranking_function.world_satisfies_conditionalization(
                    world, cond.make_A_then_not_B()
                ):
                    cast(list[int], inner_list[branch_index][world][2]).append(
                        cast(int, cond.index)
                    )

        outer_list.append(inner_list)

    return outer_list


# Reference implementation (quadratic); kept for testing.
TripleMutable = list[object]


def compile_alt(
    ranking_function: PreOCF, revision_conditionals: list[Conditional]
) -> tuple[dict[int, list[TripleMutable]], dict[int, list[TripleMutable]]]:
    vMin: dict[int, list[TripleMutable]] = dict()
    fMin: dict[int, list[TripleMutable]] = dict()

    # Initialize dictionaries for all revision conditionals based on their index
    for rev_cond in revision_conditionals:
        if not hasattr(rev_cond, "index"):
            raise ValueError(
                f"Revision conditional '{rev_cond.textRepresentation}' is missing the 'index' attribute."
            )
        key = int(cast(int, rev_cond.index))
        vMin[key] = []
        fMin[key] = []

    for rev_cond in revision_conditionals:
        # The key is now the conditional's own index
        key_index = int(cast(int, rev_cond.index))

        for world in ranking_function.ranks.keys():
            v_dict = ranking_function.world_satisfies_conditionalization(
                world, rev_cond.make_A_then_B()
            )
            f_dict = ranking_function.world_satisfies_conditionalization(
                world, rev_cond.make_A_then_not_B()
            )

            if not v_dict and not f_dict:
                continue

            rank_val = ranking_function.rank_world(world)
            acc_list: list[int] = []
            rej_list: list[int] = []

            # Skip the leading conditional itself - only consider *other* conditionals
            for cond in revision_conditionals:
                if int(cast(int, cond.index)) == key_index:
                    continue

                if ranking_function.world_satisfies_conditionalization(
                    world, cond.make_A_then_B()
                ):
                    acc_list.append(cast(int, cond.index))
                elif ranking_function.world_satisfies_conditionalization(
                    world, cond.make_A_then_not_B()
                ):
                    rej_list.append(cast(int, cond.index))

            if v_dict:
                vMin[key_index].append([rank_val, acc_list, rej_list])
            elif f_dict:
                fMin[key_index].append([rank_val, acc_list, rej_list])

    return vMin, fMin


# Optimised implementation
MinimaTriple = tuple[int, list[int], list[int]]


def compile_alt_fast(
    ranking_function: PreOCF, revision_conditionals: list[Conditional]
) -> tuple[dict[int, list[MinimaTriple]], dict[int, list[MinimaTriple]]]:
    """Optimised variant of *compile_alt*.

    Instead of an outer loop over revision conditionals *and* an inner loop over
    *all* conditionals again, we:

    1. Iterate once over every world;
    2. Evaluate *all* conditionals for that world (both A→B and A→¬B) just once;
    3. Distribute the resulting triple to the respective vMin/fMin buckets.

    The number of expensive solver calls drops from O(|C|^2 * |W|) to
    O(|C| * |W|).
    """

    # Signature lookup for mask extraction
    sig_index = {v: i for i, v in enumerate(ranking_function.signature)}

    # Pre-extract masks for simple literals; complex ones will be None and fallback to solver.
    cond_masks: dict[int, tuple[int, int, int, int] | None] = {}
    for cond in revision_conditionals:
        if cond.index is None or not isinstance(cond.index, int):
            raise ValueError(
                f"Revision conditional '{cond.textRepresentation}' is missing a valid 'index' (int)."
            )
        cond_masks[cond.index] = _extract_cond_masks(cond, sig_index)

    vMin: dict[int, list[MinimaTriple]] = {
        cast(int, c.index): [] for c in revision_conditionals
    }
    fMin: dict[int, list[MinimaTriple]] = {
        cast(int, c.index): [] for c in revision_conditionals
    }

    # Evaluate each world once.
    for world in ranking_function.ranks.keys():
        # cache world bits as ints
        bits = [int(b) for b in world]

        accepted_list: list[int] = []
        rejected_list: list[int] = []

        for cond in revision_conditionals:
            mask = cond_masks[int(cast(int, cond.index))]
            if mask is None:
                # Fallback to solver evaluation for complex formula
                if ranking_function.world_satisfies_conditionalization(
                    world, cond.make_A_then_B()
                ):
                    accepted_list.append(cast(int, cond.index))
                elif ranking_function.world_satisfies_conditionalization(
                    world, cond.make_A_then_not_B()
                ):
                    rejected_list.append(cast(int, cond.index))
            else:
                a_idx, a_val, c_idx, c_val = mask
                if bits[a_idx] == a_val:
                    if bits[c_idx] == c_val:
                        accepted_list.append(cast(int, cond.index))
                    else:
                        rejected_list.append(cast(int, cond.index))

        # Skip rank computation entirely if this world contributes to no branch
        if not accepted_list and not rejected_list:
            continue

        # Compute rank only for contributing worlds (lazy evaluation)
        rank_val = ranking_function.rank_world(world)

        acc_set = set(accepted_list)
        rej_set = set(rejected_list)

        for cond in revision_conditionals:
            idx = cast(int, cond.index)
            if idx in acc_set or idx in rej_set:
                acc_filtered = [i for i in accepted_list if i != idx]
                rej_filtered = [i for i in rejected_list if i != idx]
                triple: MinimaTriple = (rank_val, acc_filtered, rej_filtered)
                if idx in acc_set:
                    vMin[idx].append(triple)
                else:
                    fMin[idx].append(triple)

    return vMin, fMin


def symbolize_minima_expression(
    minima: dict[int, list[MinimaTriple]], gamma_plus_zero: bool = False
) -> dict[int, list[FNode]]:
    """
    Convert minima expression to symbolic form.
    Input: dict mapping indices to lists of triples [rank, accepted_indices, rejected_indices]
    Output: dict mapping indices to lists of symbolic expressions
    """
    results: dict[int, list[FNode]] = dict()

    for index, triple_list in minima.items():
        results[index] = []

        for triple in triple_list:
            if len(triple) < 3:
                # Malformed entry, skip it silently.
                continue

            rank = triple[0]
            accepted_indices = triple[1]
            rejected_indices = triple[2]

            # ------------------------------------------------------------------
            # When gamma_plus are fixed to zero, terms that only depend on gamma_plus would reduce
            # to zero and thus dominate the minima undesirably. Furthermore, if a
            # world does not violate any conditional (no rejected indices) it will
            # again yield a rank-only cost of zero.  This special-case is handled
            # by *skipping* such triples altogether - except when gamma_plus are *not* all
            # fixed to zero, in which case the gamma_plus variables still have influence.
            # ------------------------------------------------------------------
            # NOTE: We no longer skip gamma_plus-only triples because, with gamma_plus fixed to 0, they
            #       translate to a *plain* rank cost of 0 - exactly what the original
            #       c-representation requires for some fMin sets.  Omitting them made
            #       gamma_minus vectors too small (e.g. gamma_minus_2=1 instead of 2).  The downstream
            #       logic already replaces gamma_plus-terms with the bare rank when
            #       gamma_plus_zero=True, so there is no risk of undervaluing costs.

            added = False

            # Build expression for rejected conditionals (gamma_minus part); this is the
            # essential component for our optimisation irrespective of gamma_plus.
            if rejected_indices:
                rejected_sum = Plus([_gamma(f"gamma-_{i}") for i in rejected_indices])
                results[index].append(Plus([rejected_sum, Int(rank)]))
                added = True

            # Include gamma_plus part only when they contribute (i.e. not fixed to zero).
            if accepted_indices and not gamma_plus_zero:
                accepted_sum = Plus([_gamma(f"gamma+_{i}") for i in accepted_indices])
                results[index].append(Plus([accepted_sum, Int(rank)]))
                added = True

            # If this triple yielded no expression (e.g. gamma_plus fixed to 0 AND no gamma_minus
            # violations), fall back to the plain rank so every triple influences
            # the minima calculation.
            if not added:
                results[index].append(Int(rank))

    return results


def encoding(
    gammas: dict[int, tuple[FNode, FNode]],
    vSums: dict[int, list[FNode]],
    fSums: dict[int, list[FNode]],
) -> list[FNode]:
    csp: list[FNode] = []
    for index, gamma in gammas.items():
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug("gamma %s", gamma)
            logger.debug("vSums %s", vSums[index])
            logger.debug("fSums %s", fSums[index])
        mv, mf = freshVars(index)
        vMin = minima_encoding(mv, vSums[index])
        fMin = minima_encoding(mf, fSums[index])
        csp.extend(vMin)
        csp.extend(fMin)
        csp.append(GT(gamma[1] - gamma[0], mv - mf))

    return csp


def translate_to_csp(
    compilation: tuple[
        dict[int, list[MinimaTriple]],
        dict[int, list[MinimaTriple]],
    ],
    gamma_plus_zero: bool = False,
    fixed_gamma_plus: dict[int, int] | None = None,
    fixed_gamma_minus: dict[int, int] | None = None,
) -> list[FNode]:
    gammas = {}
    for i in compilation[0].keys():
        # Determine gamma_plus variable/constant
        if fixed_gamma_plus and i in fixed_gamma_plus:
            plus_var = Int(int(fixed_gamma_plus[i]))
        elif gamma_plus_zero:
            plus_var = Int(0)
        else:
            plus_var = _gamma(f"gamma+_{i}")

        # Determine gamma_minus variable/constant
        if fixed_gamma_minus and i in fixed_gamma_minus:
            minus_var = Int(int(fixed_gamma_minus[i]))
        else:
            minus_var = _gamma(f"gamma-_{i}")

        gammas[i] = (plus_var, minus_var)
    # defeat= = checkTautologies(self.epistemic_state['belief_base'].conditionals)
    # if not defeat: return False
    gteZeros = []
    for gamma_plus, gamma_minus in gammas.values():
        # Add non-negativity constraints only for symbolic variables (not constants)
        if getattr(gamma_plus, "is_symbol", lambda: False)():
            gteZeros.append(GE(gamma_plus, Int(0)))
        if getattr(gamma_minus, "is_symbol", lambda: False)():
            gteZeros.append(GE(gamma_minus, Int(0)))
    vSums = symbolize_minima_expression(compilation[0], gamma_plus_zero)
    fSums = symbolize_minima_expression(compilation[1], gamma_plus_zero)
    csp = encoding(gammas, vSums, fSums)
    csp.extend(gteZeros)
    return csp


def _convert_csp_to_z3(csp: list[FNode]) -> list:
    """Convert pysmt expressions to native z3 expressions."""
    pysmt_solver = Solver(name="z3")
    converter = pysmt_solver.converter
    return [converter.convert(expr) for expr in csp]


def solve_and_get_model(
    csp: list[FNode], minimize_vars: list[str] | None = None
) -> dict[str, int] | None:
    """Return a model satisfying *csp* and Pareto-minimising *minimize_vars*.

    Arguments
    ---------
    csp : list[pysmt.FNode]
        Constraint set produced by ``translate_to_csp`` (pysmt expressions).
    minimize_vars : list[str] | None
        Variable names to be minimised in the Pareto sense.  If *None*, the
        first model found is returned without optimisation.
    """

    z3_csp = _convert_csp_to_z3(csp)

    # If no optimisation requested, fall back to a plain satisfiable model.
    if not minimize_vars:
        s = z3.Solver()
        s.add(*z3_csp)
        if s.check() == z3.sat:
            m = s.model()
            return {d.name(): cast(Any, m[d]).as_long() for d in m.decls()}
        return None

    # Otherwise build an optimiser.
    opt = z3.Optimize()
    opt.set(priority="pareto")
    opt.add(*z3_csp)

    # Register all variables to be minimised.
    for vname in minimize_vars:
        opt.minimize(z3.Int(vname))

    # Enumerate first Pareto-optimal model (suffices since *priority='pareto'*).
    if opt.check() == z3.sat:
        m = opt.model()
        return {d.name(): cast(Any, m[d]).as_long() for d in m.decls()}

    return None


def solve_pareto_front(
    csp: list[FNode],
    minimize_vars: list[str],
    *,
    max_solutions: int | None = None,
) -> list[dict[str, int]]:
    """Enumerate all Pareto-optimal solutions for *minimize_vars* subject to *csp*.

    Uses z3's built-in Pareto optimisation (``priority='pareto'``) which
    internally enumerates the full Pareto front via successive ``check()``
    calls.

    Arguments
    ---------
    csp : list[pysmt.FNode]
        Constraint set (pysmt expressions).
    minimize_vars : list[str]
        Variable names to be minimised in the Pareto sense.
    max_solutions : int | None
        Optional cap on the number of solutions returned.  ``None`` means
        enumerate the entire Pareto front.

    Returns
    -------
    list[dict[str, int]]
        Each dict maps variable names to their integer values in a
        Pareto-optimal solution.  Empty list when no feasible solution exists.
    """
    if not minimize_vars:
        single = solve_and_get_model(csp)
        return [single] if single is not None else []

    z3_csp = _convert_csp_to_z3(csp)

    opt = z3.Optimize()
    opt.set(priority="pareto")
    opt.add(*z3_csp)

    for vname in minimize_vars:
        opt.minimize(z3.Int(vname))

    results: list[dict[str, int]] = []
    while opt.check() == z3.sat:
        m = opt.model()
        results.append({d.name(): cast(Any, m[d]).as_long() for d in m.decls()})
        if max_solutions is not None and len(results) >= max_solutions:
            break

    return results


# Choose which compilation backend to use - fast by default.
_compile_backend = compile_alt_fast


class HasToCSP(Protocol):
    def to_csp(
        self,
        *,
        gamma_plus_zero: bool = False,
        fixed_gamma_plus: dict[int, int] | None = None,
        fixed_gamma_minus: dict[int, int] | None = None,
    ) -> list[FNode]: ...


def c_revision(
    ranking_function: PreOCF,
    revision_conditionals: list[Conditional],
    gamma_plus_zero: bool = False,
    fixed_gamma_minus: dict[int, int] | None = None,
    fixed_gamma_plus: dict[int, int] | None = None,
    *,
    model: HasToCSP | None = None,
) -> dict[str, int] | None:
    """Compute gamma_plus/gamma_minus parameters according to c-revision semantics.

    When *gamma_plus_zero* is *True*, gamma_plus variables are fixed to 0 and the
    optimiser will calculate a Pareto-minimal gamma_minus vector.  This should match the
    eta-vector of the c-representation given an all-zero initial ranking.
    """

    if model is None:
        compilation = _compile_backend(ranking_function, revision_conditionals)
        csp = translate_to_csp(
            compilation,
            gamma_plus_zero,
            fixed_gamma_plus=fixed_gamma_plus,
            fixed_gamma_minus=fixed_gamma_minus,
        )
    else:
        # Reuse incremental model caches
        csp = model.to_csp(
            gamma_plus_zero=gamma_plus_zero,
            fixed_gamma_plus=fixed_gamma_plus,
            fixed_gamma_minus=fixed_gamma_minus,
        )

    # Assemble the list of gamma_minus variables to be minimised.
    minimize_vars = [
        f"gamma-_{cond.index}"
        for cond in revision_conditionals
        if not (fixed_gamma_minus and cond.index in fixed_gamma_minus)
    ]

    model_dict = solve_and_get_model(csp, minimize_vars)

    # Ensure fixed gamma values appear in the returned model dictionary
    if model_dict is not None:
        if fixed_gamma_minus:
            for i, val in fixed_gamma_minus.items():
                model_dict[f"gamma-_{i}"] = int(val)
        if fixed_gamma_plus:
            for i, val in fixed_gamma_plus.items():
                model_dict[f"gamma+_{i}"] = int(val)
        if gamma_plus_zero:
            for cond in revision_conditionals:
                key = f"gamma+_{cond.index}"
                if key not in model_dict and not (
                    fixed_gamma_plus and cond.index in fixed_gamma_plus
                ):
                    model_dict[key] = 0

    return model_dict


def c_revision_pareto_front(
    ranking_function: PreOCF,
    revision_conditionals: list[Conditional],
    gamma_plus_zero: bool = False,
    fixed_gamma_minus: dict[int, int] | None = None,
    fixed_gamma_plus: dict[int, int] | None = None,
    *,
    model: HasToCSP | None = None,
    max_solutions: int | None = None,
) -> list[dict[str, int]]:
    """Enumerate all Pareto-optimal gamma_minus vectors for c-revision.

    Same interface as :func:`c_revision` with an additional *max_solutions*
    parameter.  Returns a list of Pareto-optimal model dicts (empty list if
    infeasible).

    When *gamma_plus_zero* is True the returned vectors are the Pareto front
    of the gamma_minus (impact) space, analogous to the set of all minimal
    eta-vectors from c-representation.
    """
    if model is None:
        compilation = _compile_backend(ranking_function, revision_conditionals)
        csp = translate_to_csp(
            compilation,
            gamma_plus_zero,
            fixed_gamma_plus=fixed_gamma_plus,
            fixed_gamma_minus=fixed_gamma_minus,
        )
    else:
        csp = model.to_csp(
            gamma_plus_zero=gamma_plus_zero,
            fixed_gamma_plus=fixed_gamma_plus,
            fixed_gamma_minus=fixed_gamma_minus,
        )

    minimize_vars = [
        f"gamma-_{cond.index}"
        for cond in revision_conditionals
        if not (fixed_gamma_minus and cond.index in fixed_gamma_minus)
    ]

    solutions = solve_pareto_front(csp, minimize_vars, max_solutions=max_solutions)

    # patch fixed / zero values into every solution
    for sol in solutions:
        if fixed_gamma_minus:
            for i, val in fixed_gamma_minus.items():
                sol[f"gamma-_{i}"] = int(val)
        if fixed_gamma_plus:
            for i, val in fixed_gamma_plus.items():
                sol[f"gamma+_{i}"] = int(val)
        if gamma_plus_zero:
            for cond in revision_conditionals:
                key = f"gamma+_{cond.index}"
                if key not in sol and not (
                    fixed_gamma_plus and cond.index in fixed_gamma_plus
                ):
                    sol[key] = 0

    return solutions


def c_inference_pareto_front(
    belief_base: "BeliefBase",
    *,
    max_solutions: int | None = None,
) -> list[tuple[int, ...]]:
    """Enumerate Pareto-optimal eta vectors via the c-inference CSP.

    Builds the c-inference constraint satisfaction problem for *belief_base*
    (using the MaxSAT-based compilation from :class:`CInference`) and
    enumerates all Pareto-minimal eta vectors.

    This is the library equivalent of the ``calculate_pareto_front`` helper
    that previously lived in ``run_c_revision_birds_custom.py``.

    Parameters
    ----------
    belief_base : BeliefBase
        Knowledge base whose c-representations are to be enumerated.
    max_solutions : int | None
        Optional cap on the number of Pareto-optimal vectors returned.

    Returns
    -------
    list[tuple[int, ...]]
        Each tuple contains the eta values ordered by conditional index
        (ascending).  Empty list when no c-representation exists
        (inconsistent KB).
    """
    # lazy imports to avoid circular dependency chains
    from inference.c_inference import CInference  # noqa: E402
    from inference.inference_manager import create_epistemic_state  # noqa: E402

    es = create_epistemic_state(belief_base, "c-inference", "z3", "rc2", weakly=False)
    c_inf = CInference(es)
    c_inf.preprocess_belief_base(0)
    csp = c_inf.base_csp

    n = len(belief_base.conditionals)
    minimize_vars = [f"eta_{i}" for i in range(1, n + 1)]

    solutions = solve_pareto_front(csp, minimize_vars, max_solutions=max_solutions)

    indices = sorted(belief_base.conditionals.keys())
    return [tuple(sol.get(f"eta_{i}", 0) for i in indices) for sol in solutions]


# ----------------------------------------------------------------------------
# Helper: quick literal extraction for simple conjunctions of two literals
# ----------------------------------------------------------------------------


def _literal_info(node):
    """Return (var_name, required_val) if *node* is a literal, else None."""
    # Symbol -> var must be True
    if node.is_symbol():
        return node.symbol_name(), 1
    # Not(Symbol) -> var must be False
    if node.is_not() and node.arg(0).is_symbol():
        return node.arg(0).symbol_name(), 0
    return None


def _extract_cond_masks(cond, sig_index):
    """Return (a_idx, a_val, c_idx, c_val) or None if complex."""
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
