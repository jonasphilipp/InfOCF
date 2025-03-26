from binascii import Error
import random
from BitVector import BitVector
import pysmt
from pysmt.shortcuts import Symbol, Not, Solver
from pysmt.typing import BOOL
from pysmt.fnode import FNode
from inference import c_inference, system_z
import inference
import logging
from inference.conditional import Conditional


# Create a logger object
logger = logging.getLogger(__name__)

class PreOCF():
    epistemic_state: dict
    signature: tuple

    @property 
    def ranks(self) -> dict[str, None | int]:
        return self.epistemic_state['preocfs'][self.signature]


    # probably not needed, not gonna throw away now
    '''
    @property
    def ranks_int(self) -> dict:
        return self.epistemic_state['preocfs'][self.signature]

    @property
    def ranks_bitvec(self) -> dict:
        ranks = self.epistemic_state['preocfs'][self.signature]
        return {str(self.int2bitvec(r)): ranks[r] for r in ranks}

    @property
    def ranks_strlist(self) -> dict:
        ranks = self.epistemic_state['preocfs'][self.signature]
        return {self.int2strlist(r): ranks[r] for r in ranks}
    '''

    def __init__(self, epistemic_state: dict, marginalization: set = set()):
        self.epistemic_state = epistemic_state
        self.signature = tuple([s for s in epistemic_state['belief_base'].signature if s not in marginalization])
        if self.signature not in self.epistemic_state['preocfs']:
            #ranks : dict[int, None | int] = {i: None for i in range(len(self.signature)**2)}  
            ranks = self.create_bitvec_world_dict()
            self.epistemic_state['preocfs'][self.signature] = ranks


    def create_bitvec_world_dict(self) -> dict[str, None]:
        worlds = {str(BitVector(intVal=i, size=len(self.signature))) for i in range(2 ** len(self.signature))}
        ranks = {w: None for w in worlds}
        return ranks


    # probably not needed, not gonna throw away now
    '''
    def int2bitvec(self, world: int):
        return BitVector(intVal = world, size=len(self.signature))

    def bitvec2strlist(self, bv: BitVector) -> list[str]:
        sig = self.signature
        ### not cool, use real negation
        strlist =[sig[i] if bv[i] == 1 else '!'+sig[i] for i in range(len(sig))]
        return strlist

    def int2strlist(self, world: int) -> list[str]:
        return self.bitvec2strlist(self.int2bitvec(world))
    '''


    def is_ocf(self) -> bool:
        for world in self.ranks.keys():
            if self.ranks[world] is None or self.ranks[world] < 0: # type: ignore
                return False
        return True
   

    def marginalize(self, marginalization: set):
        return PreOCF(self.epistemic_state, marginalization)


    def conditionalization_permits_world(self, world: str, conditionalization: dict[str, int]) -> bool:
        for key, value in conditionalization.items():
            if int(world[self.signature.index(key)]) != value:
                return False
        return True


    def filter_worlds_by_conditionalization(self, conditionalization: dict[str, int]) -> list[str]:
        return [w for w in self.ranks.keys() if self.conditionalization_permits_world(w, conditionalization)]


    def compute_conditionalization(self, conditionalization: dict[str, int]):
        worlds = self.filter_worlds_by_conditionalization(conditionalization)
        {self.rank_world(w) for w in worlds if self.ranks[w] is None}


    def conditionalize_ranks(self, conditionalization: dict[str, int]) -> dict[str, None | int]:
        worlds = self.filter_worlds_by_conditionalization(conditionalization)
        conditionalized_ranks = {w: self.ranks[w] for w in worlds}
        return conditionalized_ranks


    def compute_all_ranks(self):
        [self.rank_world(w) for w in self.ranks.keys() ]


    def rank_world(self, world: str, force_calculation: bool = False) -> int:
        if force_calculation or self.ranks[world] is None:
            if self.epistemic_state['inference_system'] == 'system-z':
                self.ranks[world] = self.z_part2ocf(world)
            elif self.epistemic_state['inference_system'] == 'c-inference':
                self.ranks[world] = self.c_vec2ocf(world)
            else:
                logger.error('pls select "system-z" or "c-inference" as inference system')
        rank = self.ranks[world]
        assert rank is not None
        return rank 
    

    def symbolize_bitvec(self, bitvec: str):
        sig = self.signature
        symbols =[Symbol(sig[i], BOOL) if int(bitvec[i]) else Not(Symbol(sig[i], BOOL)) for i in range(len(sig))]
        return symbols


    def z_part2ocf(self, world: str) -> int:
        assert not self.epistemic_state['preprocessing_timed_out']
        if not self.epistemic_state['preprocessing_done']:
            logger.info('calculating z partition') 
            inference = system_z.SystemZ(self.epistemic_state)
            inference.preprocess_belief_base(0)
        signature_symbols = self.symbolize_bitvec(world)
        solver = Solver(name=self.epistemic_state['smt_solver'])
        [solver.add_assertion(s) for s in signature_symbols]
        rank = self._rec_z_rank(solver, len(self.epistemic_state['partition']) - 1)
        return rank 


    def _rec_z_rank(self, solver, partition_index) -> int:
        assert type(self.epistemic_state['partition']) == list
        part = self.epistemic_state['partition'][partition_index]
        [solver.add_assertion(Not(c.make_A_then_not_B())) for c in part]
        if solver.solve():
            if partition_index ==0:
                return 0
            else:
                return self._rec_z_rank(solver, partition_index - 1)
        else:
            return partition_index + 1
        

    # smallest rank of any world that satisfies formula
    def formula_rank(self, formula: FNode) -> int | None:
        solver = Solver(name=self.epistemic_state['smt_solver'])
        min_rank = None
        
        # Check each world
        for world in self.ranks.keys():
            # Create a new solver instance for each world
            world_solver = Solver(name=self.epistemic_state['smt_solver'])
            
            # Add the world's constraints
            world_symbols = self.symbolize_bitvec(world)
            [world_solver.add_assertion(s) for s in world_symbols]
            
            # Add the formula to check
            world_solver.add_assertion(formula)
            
            # If this world satisfies the formula, check its rank
            if world_solver.solve():
                rank = self.rank_world(world)
                if min_rank is None or rank < min_rank:
                    min_rank = rank
        
        return min_rank
    

    # true if formula_rank of verification is smaller than formula_rank of negation
    def conditional_acceptance(self, conditional: Conditional) -> bool:
        v = conditional.make_A_then_B()
        n = conditional.make_A_then_not_B()
        v_rank = self.formula_rank(v)
        n_rank = self.formula_rank(n)
        
        if v_rank is None:
            return False
        
        if n_rank is None:
            return True
        
        return v_rank < n_rank
    

    # convert ranks to total preorder
    def ranks2tpo(self, ranks: dict[str, None | int]) -> list[list[str]]:
        # Group worlds by their rank
        rank_groups: dict[int, list[str]] = {}
        for world, rank in ranks.items():
            if rank is not None:
                if rank not in rank_groups:
                    rank_groups[rank] = []
                rank_groups[rank].append(world)
        
        # Sort groups by rank and return as list of lists
        return [rank_groups[rank] for rank in sorted(rank_groups.keys())]
    
    # convert total preorder to ranks
    # explanation: dict(layer num: diff to rank of next higher layer)
    def tpo2ranks(self, tpo: list[list[str]], multiplier: int, layer_diffs: dict[int, int]) -> dict[str, None | int]:
        ranks = {}
        for layer_num, layer in enumerate(tpo):
            for world in layer:
                if world not in ranks:
                    ranks[world] = 0
                if layer_num > 0:
                    ranks[world] += sum(layer_diffs[i] * multiplier for i in range(layer_num))
        return ranks
        


    def c_vec2ocf(self, world: str) -> None:
        self.ranks[world] = random.randint(0, 10)

