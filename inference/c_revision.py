from inference.c_inference import freshVars, minima_encoding
from inference.preocf import PreOCF
from inference.conditional import Conditional
from pysmt.shortcuts import Symbol, Plus, GE, GT, Int
from pysmt.typing import INT


def compile(ranking_function: PreOCF, revision_conditionals: list[Conditional]) -> list[list[dict[str, list[int, list[int]]]]]:
    outer_list = []
    for rev_cond in revision_conditionals:
        inner_list = [dict(), dict()]
        for world in ranking_function.ranks.keys():
            branch_index = 0 if ranking_function.world_satisfies_conditionalization(world, rev_cond.make_A_then_not_B()) else 1
            
            inner_list[branch_index][world] = [ranking_function.rank_world(world), [], []]
            
            for cond in revision_conditionals:
                if ranking_function.conditional_acceptance(cond):
                    inner_list[branch_index][world][1].append(cond.index)
                else:
                    inner_list[branch_index][world][2].append(cond.index)

        outer_list.append(inner_list)

    return outer_list

def compile_alt(ranking_function: PreOCF, revision_conditionals: list[Conditional]) -> tuple[dict[int, list[int]], dict[int, list[int]]]:
    vMin = dict()
    fMin = dict()
    for index, rev_cond in enumerate(revision_conditionals):
        vMin[index] = []  # Initialize outside the world loop
        fMin[index] = []  # Initialize outside the world loop
        
        for world in ranking_function.ranks.keys():
            v_dict = True if ranking_function.world_satisfies_conditionalization(world, rev_cond.make_A_then_not_B()) else False
            
            triple = [ranking_function.rank_world(world), [], []]
            
            for cond in revision_conditionals:
                if ranking_function.conditional_acceptance(cond):
                    triple[1].append(cond.index)
                else:
                    triple[2].append(cond.index)
            if v_dict:
                vMin[index].append(triple)
            else:
                fMin[index].append(triple)

    return vMin, fMin

def symbolize_minima_expression(minima: dict[int, list]) -> dict[int, list]:
    """
    Convert minima expression to symbolic form.
    Input: dict mapping indices to lists of triples [rank, accepted_indices, rejected_indices]
    Output: dict mapping indices to lists of symbolic expressions
    """
    results = dict()
    
    for index, triple_list in minima.items():
        results[index] = []
        
        for triple in triple_list:
            if len(triple) >= 3:
                rank = triple[0]
                accepted_indices = triple[1]
                rejected_indices = triple[2]
                
                # Create expressions for accepted conditionals
                if accepted_indices:
                    accepted_sum = Plus([Symbol(f'gamma+_{i}', INT) for i in accepted_indices])
                    results[index].append(Plus([accepted_sum, Int(rank)]))
                else:
                    results[index].append(Int(rank))
                
                # Create expressions for rejected conditionals  
                if rejected_indices:
                    rejected_sum = Plus([Symbol(f'gamma-_{i}', INT) for i in rejected_indices])
                    results[index].append(Plus([rejected_sum, Int(rank)]))
                else:
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


def translate_to_csp(compilation: tuple[dict[int, list[int]], dict[int, list[int]]]) -> list:
    gammas = {i: (Symbol(f'gamma+_{i}', INT), Symbol(f'gamma-_{i}', INT)) for i in compilation[0].keys()}
    #defeat= = checkTautologies(self.epistemic_state['belief_base'].conditionals)
    #if not defeat: return False
    gteZeros = []
    for gamma_plus, gamma_minus in gammas.values():
        gteZeros.append(GE(gamma_plus, Int(0)))
        gteZeros.append(GE(gamma_minus, Int(0)))
    vSums = symbolize_minima_expression(compilation[0])
    fSums = symbolize_minima_expression(compilation[1])
    csp = encoding(gammas, vSums, fSums)
    csp.extend(gteZeros)
    return csp