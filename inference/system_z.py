from inference.inference import Inference
from inference.epistemic_state import EpistemicStateZ
from inference.consistency_sat import consistency
from warnings import warn
from pysmt.shortcuts import Solver, Not, is_unsat


class SystemZ(Inference):
    def _preprocess_belief_base(self) -> None:
            partition, _ = consistency(self.epistemic_state._belief_base, solver=self.epistemic_state.solver)
            if not partition: warn('belief base inconsistent')
            self.epistemic_state._partition = partition #type: ignore
    def _inference(self, query) -> bool:
         
        assert type(self.epistemic_state) == EpistemicStateZ, "Knowledge base is inconsistent."
        solver = Solver(name=self.epistemic_state.solver)
        if is_unsat(query.antecedence): 
            result = True
        else:
            result = self._rec_inference(solver, len(self.epistemic_state._partition) -1, query) # type: ignore
        return result

    def _rec_inference(self, solver, partition_index, query):
        assert type(self.epistemic_state._partition) == list
        part = self.epistemic_state._partition[partition_index]
        [solver.add_assertion(Not(c.make_A_then_not_B())) for c in part]
        solver.push()
        solver.add_assertion(query.make_A_then_B())
        v = solver.solve() 
        solver.pop()
        solver.push()
        solver.add_assertion(query.make_A_then_not_B())
        f = solver.solve() 
        solver.pop()

        if not v:
            return False



        if f:
            if partition_index == 0:
                return False
            return self._rec_inference(solver, partition_index -1, query)
        return True

