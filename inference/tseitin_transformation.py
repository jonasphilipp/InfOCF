from pysat.card import IDPool
from z3 import z3
from time import time_ns
from pysmt.shortcuts import Solver
from inference.conditional import Conditional


class TseitinTransformation:
    epistemic_state: dict
    
    """
    Initializes TseitinTransformation object and creates needed dict entries if not present.

    Context:
        Called before transformation to CNFs of conditionals is performed

    Parameters:
        epistemic_state dict

    Side Effects:
        pool, v_cnf_dict, f_cnf_dict, nf_cnf_dict entries in epistemic_state
    """
    def __init__(self, epistemic_state: dict) -> None:
        if 'pool' not in epistemic_state:
            epistemic_state['pool'] = IDPool()
        if 'v_cnf_dict' not in epistemic_state:
            epistemic_state['v_cnf_dict'] = dict()
        if 'f_cnf_dict' not in epistemic_state:
            epistemic_state['f_cnf_dict'] = dict()
        if 'nf_cnf_dict' not in epistemic_state:
            epistemic_state['nf_cnf_dict'] = dict()
        
        self.epistemic_state = epistemic_state

        
    """
    Uses z3's logical operators, tseitin transformation and local helper methods to fill the dicts 
    self.ABs, self.AnotBs and self.notAorBs with int/id CNFs equivalent to the name-giving logical 
    operations applied to the conditionals in self.conditionals at the same dict index

    Context:
        This method has to be called before compile_constraint or compile_and_encode_query can be 
        called since both of these methods depend on the dicts of CNFs being filled

    Returns:
        Execution time in ms
    """
    def belief_base_to_cnf(self, v: bool, f: bool, nf: bool) -> float:
        start_time = time_ns()
        t = z3.Tactic('tseitin-cnf')
        
        for index, conditional in self.epistemic_state['belief_base'].conditionals.items():
            with Solver(name="z3") as solver:
                antecedence = solver.converter.convert(conditional.antecedence)
                consequence = solver.converter.convert(conditional.consequence)
            if v:
                g1 = t(z3.And(antecedence, consequence))
                self.epistemic_state['v_cnf_dict'][index] = self.goal2intcnf(g1[0])
            if f:
                g2 = t(z3.And(antecedence, z3.Not(consequence)))
                self.epistemic_state['f_cnf_dict'][index] = self.goal2intcnf(g2[0])
            if nf:
                g3 = t(z3.Or(z3.Not(antecedence), consequence))
                self.epistemic_state['nf_cnf_dict'][index] = self.goal2intcnf(g3[0])
        return (time_ns() - start_time) / (1e+6) 

    def layers_z_to_cnf(self, partition):
        """
        for (one implementation of) weakly system Z, we need for each layer in the tolerance partition 
        the conjunction of each conditional in non-falsifying form (self.notAorB) in that layer,
        in cnf form

        """
        t = z3.Tactic('tseitin-cnf')
        ### TODO
        cnf_layers = dict()
        ### we start counting at zero
        t = z3.Tactic('tseitin-cnf')
        for i,p in enumerate(partition):
            with Solver(name="z3") as solver:
                nf_conds = []
                for conditional in p:
                    antecedence = solver.converter.convert(conditional.antecedence)
                    consequence = solver.converter.convert(conditional.consequence)
                    nf = z3.Not(z3.And(antecedence, z3.Not(consequence)))
                    nf_conds.append(nf)
                g = t(z3.And(nf_conds))
                cnf_layers[i] = self.goal2intcnf(g[0])
        return cnf_layers


    """
    Transforms query conditional to CNF

    Context:
        Called before to create CNF forms of conditionals to create wcnf format files
        for pmaxsat_solver

    Parameters:
        query conditionals

    Returns:
        Verification and falsification of query in CNF format
    """
    def query_to_cnf(self, query: Conditional) -> list[list[list[int]]]:
        t = z3.Tactic('tseitin-cnf')
        with Solver(name="z3") as solver:
            antecedence = solver.converter.convert(query.antecedence)
            consequence = solver.converter.convert(query.consequence)
        AB = self.goal2intcnf(t(z3.And(antecedence, consequence))[0])
        AnotB = self.goal2intcnf(t(z3.And(antecedence, z3.Not(consequence)))[0])
        return [AB, AnotB]


    def query_to_implication(self, query: Conditional) -> list[list[list[int]]]:
        t = z3.Tactic('tseitin-cnf')
        with Solver(name="z3") as solver:
            antecedence = solver.converter.convert(query.antecedence)
            consequence = solver.converter.convert(query.consequence)
        AB = self.goal2intcnf(t(z3.Implies(antecedence, consequence))[0])
        return AB

    """
    Takes z3 goal in CNF and turns it to CNF of ints. The absolute values of those ints 
    function as unique IDs of the z3 expressions in the goal.

    Context:
        Helper function called by makeCNFs and compile_and_encode_query.

    Parameters: 
        z3 goal as CNF

    Returns:
        CNF of ints (which are signed IDs of z3 expressions in goal)
    """
    def goal2intcnf(self, goal: z3.Goal) -> list[list[int]]:
        cnf = []
        for expr in goal:
            if z3.is_or(expr):
                cnf.append([self.expr_to_signed_id(x) for x in expr.children()])
            else:
                cnf.append([self.expr_to_signed_id(expr)])
        return cnf
    

    """
    Takes z3 expression and creates or retrieves unique ID of expression using pysat.formula.IDPool
    and signs it (with a minus or nothing) depending on whether the expression is negated by being 
    wrappend in a "Not()"

    Context:
        Helper function called by goal2intcnf 

    Parameters: 
        z3 expression

    Returns:
        int serving as signed ID of input expression
    """
    def expr_to_signed_id(self, expr: z3.ExprRef) -> int:
        sign = 1
        if z3.is_not(expr):
            sign = -1
            expr = expr.children()[0]
        expr_id = self.epistemic_state['pool'].id(expr)
        return sign * expr_id
