from inference.c_inference import freshVars, minima_encoding
from inference.preocf import PreOCF
from inference.conditional import Conditional
from pysmt.shortcuts import Symbol, Plus, GE, GT, Int, Solver
from pysmt.typing import INT


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
            
            # Here, we also use the cond.index
            for cond in revision_conditionals:
                if ranking_function.world_satisfies_conditionalization(world, cond.make_A_then_B()):    
                    triple[1].append(cond.index)
                elif ranking_function.world_satisfies_conditionalization(world, cond.make_A_then_not_B()):
                    triple[2].append(cond.index)
            
            if v_dict:
                vMin[key_index].append(triple)
            elif f_dict:
                fMin[key_index].append(triple)

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

def solve_and_get_model(csp):
    with Solver(name='z3') as solver:
        solver.add_assertions(csp)
        if solver.solve():
            model = {}
            for var_name, var_value in solver.get_model():
                model[var_name.symbol_name()] = var_value
            return model
        return None

def c_revision(ranking_function: PreOCF, revision_conditionals: list[Conditional]):
    compilation = compile_alt(ranking_function, revision_conditionals)
    csp = translate_to_csp(compilation)
    # get model of csp
    model = solve_and_get_model(csp)
    return model