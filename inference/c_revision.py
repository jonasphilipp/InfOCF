from inference.c_inference import freshVars, minima_encoding
from inference.preocf import PreOCF
from inference.conditional import Conditional
from pysmt.shortcuts import Symbol, Plus, GE, GT, Int, Solver, Equals
from pysmt.typing import INT
import z3


"""
ATTENTION: This file is not tested yet sufficiently, and the implementation is not complete.
"""

def compile(ranking_function: PreOCF, revision_conditionals: list[Conditional]) -> list[list[dict[str, list[int, list[int]]]]]:
    outer_list = []
    for rev_cond in revision_conditionals:
        inner_list = [dict(), dict()]
        for world in ranking_function.ranks.keys():
            if ranking_function.world_satisfies_conditionalization(world, rev_cond.make_A_then_B()):
                branch_index = 0
            elif ranking_function.world_satisfies_conditionalization(world, rev_cond.make_A_then_not_B()):
                branch_index = 1
            else:
                continue
            
            inner_list[branch_index][world] = [ranking_function.rank_world(world), [], []]
            
            for cond in revision_conditionals:
                if ranking_function.world_satisfies_conditionalization(world, cond.make_A_then_B()):
                    inner_list[branch_index][world][1].append(cond.index)
                elif ranking_function.world_satisfies_conditionalization(world, cond.make_A_then_not_B()):
                    inner_list[branch_index][world][2].append(cond.index)

        outer_list.append(inner_list)

    return outer_list

def compile_alt(ranking_function: PreOCF, revision_conditionals: list[Conditional]) -> tuple[dict[int, list[int]], dict[int, list[int]]]:
    vMin = dict()
    fMin = dict()

    # Initialize dictionaries for all revision conditionals based on their index
    for rev_cond in revision_conditionals:
        if not hasattr(rev_cond, 'index'):
            raise ValueError(f"Revision conditional '{rev_cond.textRepresentation}' is missing the 'index' attribute.")
        vMin[rev_cond.index] = []
        fMin[rev_cond.index] = []

    for rev_cond in revision_conditionals:
        # The key is now the conditional's own index
        key_index = rev_cond.index
        
        for world in ranking_function.ranks.keys():
            v_dict = ranking_function.world_satisfies_conditionalization(world, rev_cond.make_A_then_B())
            f_dict = ranking_function.world_satisfies_conditionalization(world, rev_cond.make_A_then_not_B())
            
            if not v_dict and not f_dict:
                continue

            triple = [ranking_function.rank_world(world), [], []]
            
            # Skip the leading conditional itself – only consider *other* conditionals
            for cond in revision_conditionals:
                if cond.index == key_index:
                    continue

                if ranking_function.world_satisfies_conditionalization(world, cond.make_A_then_B()):    
                    triple[1].append(cond.index)
                elif ranking_function.world_satisfies_conditionalization(world, cond.make_A_then_not_B()):
                    triple[2].append(cond.index)
            
            if v_dict:
                vMin[key_index].append(triple)
            elif f_dict:
                fMin[key_index].append(triple)

    return vMin, fMin

def compile_alt_fast(
    ranking_function: PreOCF, revision_conditionals: list[Conditional]
) -> tuple[dict[int, list], dict[int, list]]:
    """Optimised variant of *compile_alt*.

    Instead of an outer loop over revision conditionals *and* an inner loop over
    *all* conditionals again, we:

    1. Iterate once over every world;
    2. Evaluate *all* conditionals for that world (both A→B and A→¬B) just once;
    3. Distribute the resulting triple to the respective vMin/fMin buckets.

    The number of expensive solver calls drops from O(|C|²·|W|) to
    O(|C|·|W|).
    """

    # Prepare empty bucket lists keyed by conditional index.
    vMin: dict[int, list] = {cond.index: [] for cond in revision_conditionals}
    fMin: dict[int, list] = {cond.index: [] for cond in revision_conditionals}

    # Evaluate each world once.
    for world in ranking_function.ranks.keys():
        rank_val = ranking_function.rank_world(world)

        accepted: list[int] = []  # indices where world |= A→B
        rejected: list[int] = []  # indices where world |= A→¬B

        # First pass – compute acceptance/rejection sets for *all* conditionals.
        for cond in revision_conditionals:
            if ranking_function.world_satisfies_conditionalization(world, cond.make_A_then_B()):
                accepted.append(cond.index)
            elif ranking_function.world_satisfies_conditionalization(world, cond.make_A_then_not_B()):
                rejected.append(cond.index)

        acc_set = set(accepted)
        rej_set = set(rejected)

        # For each conditional, build a dedicated triple *without* its own index
        # in the accepted/rejected lists – in line with the semantics of the
        # original compile_alt implementation.
        for cond in revision_conditionals:
            idx = cond.index

            if idx in acc_set or idx in rej_set:
                # Create filtered copies (avoid mutating originals)
                acc_filtered = [i for i in accepted if i != idx]
                rej_filtered = [i for i in rejected if i != idx]
                triple = [rank_val, acc_filtered, rej_filtered]

                if idx in acc_set:
                    vMin[idx].append(triple)
                else:
                    fMin[idx].append(triple)

    return vMin, fMin

def symbolize_minima_expression(minima: dict[int, list], gamma_plus_zero: bool = False) -> dict[int, list]:
    """
    Convert minima expression to symbolic form.
    Input: dict mapping indices to lists of triples [rank, accepted_indices, rejected_indices]
    Output: dict mapping indices to lists of symbolic expressions
    """
    results = dict()
    
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
            # When γ⁺ are fixed to zero, terms that only depend on γ⁺ would reduce
            # to zero and thus dominate the minima undesirably. Furthermore, if a
            # world does not violate any conditional (no rejected indices) it will
            # again yield a rank-only cost of zero.  This special-case is handled
            # by *skipping* such triples altogether – except when γ⁺ are *not* all
            # fixed to zero, in which case the γ⁺ variables still have influence.
            # ------------------------------------------------------------------
            # NOTE: We no longer skip γ⁺-only triples because, with γ⁺ fixed to 0, they
            #       translate to a *plain* rank cost of 0 – exactly what the original
            #       c-representation requires for some fMin sets.  Omitting them made
            #       γ⁻ vectors too small (e.g. γ⁻₂=1 instead of 2).  The downstream
            #       logic already replaces γ⁺-terms with the bare rank when
            #       gamma_plus_zero=True, so there is no risk of undervaluing costs.

            added = False

            # Build expression for rejected conditionals (γ⁻ part); this is the
            # essential component for our optimisation irrespective of γ⁺.
            if rejected_indices:
                rejected_sum = Plus([Symbol(f'gamma-_{i}', INT) for i in rejected_indices])
                results[index].append(Plus([rejected_sum, Int(rank)]))
                added = True

            # Include γ⁺ part only when they contribute (i.e. not fixed to zero).
            if accepted_indices and not gamma_plus_zero:
                accepted_sum = Plus([Symbol(f'gamma+_{i}', INT) for i in accepted_indices])
                results[index].append(Plus([accepted_sum, Int(rank)]))
                added = True

            # If this triple yielded no expression (e.g. γ⁺ fixed to 0 AND no γ⁻
            # violations), fall back to the plain rank so every triple influences
            # the minima calculation.
            if not added:
                results[index].append(Int(rank))
    
    return results


def encoding(gammas: dict, vSums: dict, fSums: dict) -> list:
    csp = []
    for index, gamma in gammas.items():
        print(f"gamma {gamma}")
        print(f"vSums {vSums[index]}")
        print(f"fSums {fSums[index]}")
        mv, mf = freshVars(index)
        vMin = minima_encoding(mv, vSums[index])
        fMin = minima_encoding(mf, fSums[index])
        csp.extend(vMin)
        csp.extend(fMin)
        csp.append(GT(gamma[1] - gamma[0], mv - mf))

    return csp


def translate_to_csp(compilation: tuple[dict[int, list[int]], dict[int, list[int]]], gamma_plus_zero: bool = False) -> list:
    gammas = {i: (Symbol(f'gamma+_{i}', INT), Symbol(f'gamma-_{i}', INT)) for i in compilation[0].keys()}
    #defeat= = checkTautologies(self.epistemic_state['belief_base'].conditionals)
    #if not defeat: return False
    gteZeros = []
    for gamma_plus, gamma_minus in gammas.values():
        gteZeros.append(GE(gamma_plus, Int(0)))
        gteZeros.append(GE(gamma_minus, Int(0)))
        if gamma_plus_zero:
            gteZeros.append(Equals(gamma_plus, Int(0)))
    vSums = symbolize_minima_expression(compilation[0], gamma_plus_zero)
    fSums = symbolize_minima_expression(compilation[1], gamma_plus_zero)
    csp = encoding(gammas, vSums, fSums)
    csp.extend(gteZeros)
    return csp

def solve_and_get_model(csp, minimize_vars: list[str] | None = None):
    """Return a model satisfying *csp* and Pareto-minimising *minimize_vars*.

    Arguments
    ---------
    csp : list[pysmt.FNode]
        Constraint set produced by ``translate_to_csp`` (pysmt expressions).
    minimize_vars : list[str] | None
        Variable names to be minimised in the Pareto sense.  If *None*, the
        first model found is returned without optimisation.
    """

    # Convert pysmt expressions to native z3 expressions so we can leverage
    # z3's *Optimize* capabilities.
    pysmt_solver = Solver(name='z3')
    z3_csp = [pysmt_solver.converter.convert(expr) for expr in csp]

    # If no optimisation requested, fall back to a plain satisfiable model.
    if not minimize_vars:
        s = z3.Solver()
        s.add(*z3_csp)
        if s.check() == z3.sat:
            m = s.model()
            return {d.name(): m[d].as_long() for d in m.decls()}
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
        return {d.name(): m[d].as_long() for d in m.decls()}

    return None


# Choose which compilation backend to use – fast by default.
_compile_backend = compile_alt_fast


def c_revision(
    ranking_function: PreOCF,
    revision_conditionals: list[Conditional],
    gamma_plus_zero: bool = False,
):
    """Compute γ⁺/γ⁻ parameters according to c-revision semantics.

    When *gamma_plus_zero* is *True*, γ⁺ variables are fixed to 0 and the
    optimiser will calculate a Pareto-minimal γ⁻ vector.  This should match the
    η-vector of the c-representation given an all-zero initial ranking.
    """

    compilation = _compile_backend(ranking_function, revision_conditionals)
    csp = translate_to_csp(compilation, gamma_plus_zero)

    # Assemble the list of γ⁻ variables to be minimised.
    minimize_vars = [f"gamma-_{cond.index}" for cond in revision_conditionals]

    model = solve_and_get_model(csp, minimize_vars)
    return model