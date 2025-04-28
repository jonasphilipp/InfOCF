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
from inference.belief_base import BeliefBase
from inference.inference_operator import Inference
from inference.consistency_sat import consistency

# Create a logger object
logger = logging.getLogger(__name__)

# parms: bb, ranks

# signature, bb, systemz
# signature, bb, random_min_c_rep
class PreOCF():
    #epistemic_state: dict
    ranks: dict[str, None | int]
    signature: list[str]
    conditionals: dict[int, Conditional]
    ranking_system: str
    _z_partition: list[Conditional]

    # return ranks dict with verbose world names
    # str len == 5
    #         strlist =[sig[i] if bv[i] == 1 else '!'+sig[i] for i in range(len(sig))]
    # like above but 
    @property
    def ranks_verbose(self) -> dict[str, None | int]:
        return {self.bv2strtuple(r): self.ranks[r] for r in self.ranks.keys()}
    
    def bv2strtuple(self, bv: BitVector) -> tuple[str, ...]:
        return tuple([self.signature[i] if bv[i] == '1' else '!'+self.signature[i] for i in range(len(self.signature))])


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

    def __init__(self, ranks: dict[str, None | int], signature: list | None, conditionals: dict[int, Conditional] | None, ranking_system: str):
        self.ranks = ranks
        self.signature = signature
        self.conditionals = conditionals
        self.ranking_system = ranking_system


    @classmethod
    def init_system_z(cls, belief_base: BeliefBase, signature: list = None) -> 'PreOCF':
        if signature is None:
            signature = belief_base.signature
        else:
            signature = tuple(signature)
        ranks = cls.create_bitvec_world_dict(signature)
        conditionals = belief_base.conditionals
        cls = cls(ranks, signature, conditionals, 'system-z')
        cls._z_partition, _ = consistency(BeliefBase(signature, conditionals, 'z-partition'))
        return cls


    @classmethod
    def init_random_min_c_rep(cls, belief_base: BeliefBase, signature: list = None):
        if signature is None:
            signature = belief_base.signature
        else:
            signature = signature
        ranks = cls.create_bitvec_world_dict(signature)
        conditionals = belief_base.conditionals
        return cls(ranks, signature, conditionals, 'random_min_c_rep')
    
    @classmethod
    def init_custom(cls, ranks: dict[str, None | int], belief_base: BeliefBase = None, signature: list = None):
        """
        Create a custom PreOCF initialized with a ranks dict.
        - If belief_base is provided, use its signature and conditionals unless overridden by signature param.
        - If signature is provided but no belief_base, use that signature with no conditionals.
        - If neither is provided, both signature and conditionals will be None.
        """
        if belief_base is None and signature is None:
            sig = None
            conds = None
        else:
            sig = signature if signature is not None else (belief_base.signature if belief_base is not None else None)
            conds = belief_base.conditionals if belief_base is not None else None
        return cls(ranks, sig, conds, 'custom')
    
    
    @classmethod
    def create_bitvec_world_dict(cls, signature=None) -> dict[str, None]:
        if signature is None:
            # Called as instance method
            if not hasattr(cls, 'signature'):
                raise ValueError("Signature not provided and not available as instance attribute")
            signature = cls.signature
            
        worlds = [str(BitVector(intVal=i, size=len(signature))) for i in range(2 ** len(signature))]
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
   
    # returns new PreOCF with marginalized signature and ranks that are the minimum of the ranks of the worlds with the same marginalized signature
    def marginalize(self, marginalization: list[str]) -> 'PreOCF':
        ranks = {}
        for world in self.ranks.keys():
            # remove all bits whose index matches the one of the signature elements in marginalization
            new_world = ''.join([world[i] for i in range(len(world)) if self.signature[i] not in marginalization])
            if self.ranks[world] is not None:
                if ranks.get(new_world) is None:
                    ranks[new_world] = self.ranks[world]
                else:
                    ranks[new_world] = min(ranks[new_world], self.ranks[world])
        return PreOCF(ranks, list(set(self.signature) - set(marginalization)), self.conditionals, self.ranking_system)

    '''
    # not only sig elems
    def conditionalization_permits_world(self, world: str, conditionalization: dict[str, int]) -> bool:
        for key, value in conditionalization.items():
            if int(world[self.signature.index(key)]) != value:
                return False
        return True
    '''

    # world satisfies formula
    def world_satisfies_conditionalization(self, world: str, conditionalization: FNode) -> bool:
        solver = Solver(name='z3')
        world_symbols = self.symbolize_bitvec(world)
        [solver.add_assertion(s) for s in world_symbols]
        solver.add_assertion(conditionalization)
        return solver.solve()


    def filter_worlds_by_conditionalization(self, conditionalization: FNode) -> list[str]:
        return [w for w in self.ranks.keys() if self.world_satisfies_conditionalization(w, conditionalization)]


    def compute_conditionalization(self, conditionalization: FNode) -> dict[str, None | int]:
        worlds = self.filter_worlds_by_conditionalization(conditionalization)
        return {w: self.rank_world(w) for w in worlds}


    def conditionalize_existing_ranks(self, conditionalization: FNode) -> dict[str, None | int]:
        worlds = self.filter_worlds_by_conditionalization(conditionalization)
        conditionalized_ranks = {w: self.ranks[w] for w in worlds}
        return conditionalized_ranks


    def compute_all_ranks(self) -> dict[str, None | int]:
        return {w: self.rank_world(w) for w in self.ranks.keys()}


    def rank_world(self, world: str, force_calculation: bool = False) -> int:
        if force_calculation or self.ranks[world] is None:
            if self.ranking_system == 'system-z':
                self.ranks[world] = self.z_part2ocf(world)
            elif self.ranking_system == 'random_min_c_rep':
                self.ranks[world] = self.c_vec2ocf(world)
            elif self.ranking_system == 'custom':
                raise ValueError(f'provide custom ranking function for world: {world}')
            else:
                raise ValueError(f'pls select "system-z" or "random_min_c_rep" or "custom" as ranking system')
        rank = self.ranks[world]
        assert rank is not None
        return rank 
    

    def symbolize_bitvec(self, bitvec: str):
        sig = self.signature
        symbols = [Symbol(sig[i], BOOL) if int(bitvec[i]) else Not(Symbol(sig[i], BOOL)) for i in range(len(sig))]
        return symbols


    def z_part2ocf(self, world: str) -> int:
        signature_symbols = self.symbolize_bitvec(world)
        solver = Solver(name='z3')
        [solver.add_assertion(s) for s in signature_symbols]
        rank = self._rec_z_rank(solver, len(self._z_partition) - 1)
        return rank 


    def _rec_z_rank(self, solver, partition_index) -> int:
        part = self._z_partition[partition_index]
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
        min_rank = None
        solver = Solver(name='z3')
        
        # Check each world
        for world in self.ranks.keys():
            # Push a new scope
            solver.push()
            
            # Add the world's constraints
            world_symbols = self.symbolize_bitvec(world)
            [solver.add_assertion(s) for s in world_symbols]
            
            # Add the formula to check
            solver.add_assertion(formula)
            
            # If this world satisfies the formula, check its rank
            if solver.solve():
                rank = self.rank_world(world)
                if min_rank is None or rank < min_rank:
                    min_rank = rank
            
            # Pop the scope to remove world-specific constraints
            solver.pop()
        
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
    


        

    # vector: dict[int, int] -> index: conditional index (currently starts at 1)
    def impacts2ocf(self, world: str, vector: dict[int, int]) -> int:
        rank = 0
        signature_symbols = self.symbolize_bitvec(world)
        solver = Solver(name='z3')
        [solver.add_assertion(s) for s in signature_symbols]
        for index, conditional in self.conditionals.items():
            solver.add_assertion(Not(conditional.make_A_then_not_B()))
        if not solver.solve():
            rank += vector[index]
        return rank
        
        


# convert ranks to total preorder
def ranks2tpo(ranks: dict[str, None | int]) -> list[set[str]]:
    # Group worlds by their rank
    rank_groups: dict[int, set[str]] = {}
    for world, rank in ranks.items():
        if rank is not None:
            if rank not in rank_groups:
                rank_groups[rank] = set()
            rank_groups[rank].add(world)
    
    # Sort groups by rank and return as list of lists
    return [rank_groups[rank] for rank in sorted(rank_groups.keys())]


# func as input

# convert total preorder to ranks
# The rank_function takes a layer number and returns the rank for that layer
def tpo2ranks(tpo: list[set[str]], rank_function: callable) -> dict[str, None | int]:
    ranks = {}
    for layer_num, layer in enumerate(tpo):
        for world in layer:
            ranks[world] = rank_function(layer_num)
    return ranks
