from z3 import z3
from time import time_ns
from pysmt.shortcuts import Solver
from inference.conditional import Conditional
from inference.epistemic_state import EpistemicStateC


class TseitinTransformation:
    epistemic_state: EpistemicStateC

    def __init__(self, epistemic_state):
        self.epistemic_state = epistemic_state


    def transform(self):
        pass
        
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
    def belief_base_to_cnf(self, v, f, nf ) -> float:
        start_time = time_ns()
        t = z3.Tactic('tseitin-cnf')
        
        for index, conditional in self.epistemic_state._belief_base.conditionals.items():
            with Solver(name="z3") as solver:
                antecedence = solver.converter.convert(conditional.antecedence)
                consequence = solver.converter.convert(conditional.consequence)
            if v:
                g1 = t(z3.And(antecedence, consequence))
                self.epistemic_state._ABs[index] = self.goal2intcnf(g1[0])
            if f:
                g2 = t(z3.And(antecedence, z3.Not(consequence)))
                self.epistemic_state._AnotBs[index] = self.goal2intcnf(g2[0])
            if nf:
                g3 = t(z3.Or(z3.Not(antecedence), consequence))
                self.epistemic_state._notAorBs[index] = self.goal2intcnf(g3[0])
        return (time_ns() - start_time) / (1e+6) 

    def query_to_cnf(self, query: Conditional):
        t = z3.Tactic('tseitin-cnf')
        with Solver(name="z3") as solver:
            antecedence = solver.converter.convert(query.antecedence)
            consequence = solver.converter.convert(query.consequence)
        AB = self.goal2intcnf(t(z3.And(antecedence, consequence))[0])
        AnotB = self.goal2intcnf(t(z3.And(antecedence, z3.Not(consequence)))[0])
        return [AB, AnotB]
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
        expr_id = self.epistemic_state._pool.id(expr)
        return sign * expr_id
