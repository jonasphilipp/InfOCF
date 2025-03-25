import unittest
import os
from inference import conditional
from inference.preocf import PreOCF
from inference.inference_operator import create_epistemic_state
from parser.Wrappers import parse_belief_base, parse_queries
from pysmt.shortcuts import Symbol, Equals, Bool, Solver, Iff, Not
from pysmt.typing import BOOL

class TestPreOCF(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Get the absolute path to the project root directory
        project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        # Construct the path to the example file
        filepath = os.path.join(project_root, "examples", "random_large", "randomTest_10_10_0.cl")
        
        # Verify the file exists before proceeding
        if not os.path.exists(filepath):
            raise FileNotFoundError(f"Test file not found at: {filepath}")
            
        bb = parse_belief_base(filepath)
        str_birds = "signature\nb,p,f,w\n\nconditionals\nbirds{\n(f|b),\n(!f|p),\n(b|p),(w|b)\n}"
        bb_birds = parse_belief_base(str_birds)
        smt_solver = 'z3'
        pmaxsat_solver = 'z3'
        cls.epistemic_state_z = create_epistemic_state(bb, inference_system= 'system-z', smt_solver=smt_solver, pmaxsat_solver=pmaxsat_solver)
        cls.epistemic_state_z['preocfs'] = dict()
        cls.preocf_z = PreOCF(cls.epistemic_state_z)
        cls.epistemic_state_z_birds = create_epistemic_state(bb_birds, inference_system= 'system-z', smt_solver=smt_solver, pmaxsat_solver=pmaxsat_solver)
        cls.epistemic_state_z_birds['preocfs'] = dict()
        cls.preocf_z_birds = PreOCF(cls.epistemic_state_z_birds)

    def test_bitvec_world_ranks(self):
        ranks = self.preocf_z.ranks
        worlds = ranks.keys()
        assert len(worlds) == 2 ** len(self.preocf_z.signature)
        for key in self.preocf_z.create_bitvec_world_dict().keys():
            assert key in worlds
            assert self.preocf_z.ranks[key] == None


    def test_ranks_and_conditionalization(self):
        conditionalization = {'xxvhqj': 1, 'mwmsty': 1, 'cqosod': 1, 'euhfwd': 1, 'gqymvz': 1, 'vlpxza': 1, 'wcqayf': 1, 'jwrubk': 1}
        assert self.preocf_z.conditionalization_permits_world('1111111000', conditionalization) == False
        assert self.preocf_z.conditionalization_permits_world('1111111100', conditionalization) == True
        assert self.preocf_z.is_ocf() == False
        assert len(self.preocf_z.ranks.keys()) == 1024
        conditionalized_worlds = self.preocf_z.filter_worlds_by_conditionalization(conditionalization)
        assert len(conditionalized_worlds) == 4
        self.preocf_z.compute_conditionalization(conditionalization)
        assert self.preocf_z.is_ocf() == False
        assert len({key for key in self.preocf_z.ranks.keys() if self.preocf_z.ranks[key] != None}) == 4
        self.preocf_z.compute_all_ranks()
        assert self.preocf_z.is_ocf() == True
        conditionalized_dict = self.preocf_z.conditionalize_ranks(conditionalization)
        assert len(conditionalized_dict.keys()) == 4
        assert list(conditionalized_dict.keys()) == conditionalized_worlds

        self.preocf_z_birds.compute_all_ranks()
        assert self.preocf_z_birds.ranks['1111'] == 2
        assert self.preocf_z_birds.ranks['0000'] == 0
        assert self.preocf_z_birds.ranks['1011'] == 0
        assert self.preocf_z_birds.ranks['1001'] == 1

    def test_signature_and_conditionals(self):
        signature = self.preocf_z.signature
        print(f'signature {signature}')
        print(f'signature[1] {signature[0]}')
        print(f'type(signature[1]) {type(signature[0])}')
        conditionals = self.epistemic_state_z['belief_base'].conditionals
        print(f'conditionals {conditionals}')
        print(f'conditionals[1].antecedence {conditionals[1].antecedence}')
        print(f'type(conditionals[1].antecedence) {type(conditionals[1].antecedence)}')
        print(f'type(conditionals[1].consequence) {type(conditionals[1].consequence)}')
        solver = Solver(name=self.epistemic_state_z['smt_solver'])
        sig_1 = Symbol(signature[0], BOOL)
        not_sig_1 = Not(sig_1)
        sig_7 = Symbol(signature[0], BOOL)
        print(f'sig_1 {sig_1}')
        print(f'type(sig_1) {type(sig_1)}')
        solver.add_assertion(conditionals[1].make_A_then_B())
        solver.add_assertion(sig_7)
        assert solver.solve() == True
        solver.push()
        solver.add_assertion(sig_1)
        assert solver.solve() == True
        solver.pop()
        solver.add_assertion(not_sig_1)
        assert solver.solve() == False
        print(f'not_sig_1 {not_sig_1}')



        

if __name__ == '__main__':
    unittest.main()
