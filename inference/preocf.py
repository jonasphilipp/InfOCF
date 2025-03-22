from binascii import Error
from inspect import signature
import random
from BitVector import BitVector
from random import randint
from frozenlist import FrozenList

from inference import inference 

class PreOCF():
    epistemic_state: dict
    signature: FrozenList

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

    def __init__(self, epistemic_state: dict, marginalization: set = set()):
        self.epistemic_state = epistemic_state
        self.signature = FrozenList([s for s in epistemic_state['belief_base'].signature if s not in marginalization])
        if self.signature not in self.epistemic_state['preocfs']:
            ranks : dict[int, None | int] = {i: None for i in range(len(self.signature)**2)}  
            self.epistemic_state['preocfs'][self.signature] = ranks



    def int2bitvec(self, world: int):
        return BitVector(intVal = world, size=len(self.signature))

    def bitvec2strlist(self, bv: BitVector) -> list[str]:
        sig = self.signature
        strlist =[sig[i] if bv[i] == 1 else '!'+sig[i] for i in range(len(sig))]
        return strlist

    def int2strlist(self, world: int) -> list[str]:
        return self.bitvec2strlist(self.int2bitvec(world))



    def is_ocf(self) -> bool:
        for world in self.ranks_int.keys():
            if self.ranks[world] is None or self.ranks[r] < 0: # type: ignore
                return False
        return True
   

    def marginalize(self, marginalization: set):
        return PreOCF(self.epistemic_state, marginalization)


    def conditionalization_accepts_world(self, world: BitVector, conditionalization: dict[str, int]) -> bool:
        for key, value in conditionalization.items():
            if world[self.signature.index(key)] != value:
                return False
        return True



    def compute_conditionalization(self, conditionalization: dict[str, int]):
        worlds = {w for w in self.ranks_int.keys() if self.conditionalization_accepts_world(self.int2bitvec(w), conditionalization)}
        {self.rank_world_int(w) for w in worlds if self.ranks_int[w] is None}

    def conditionalize_ranks(self, dict) -> dict:
        pass

    def rank_world_int(self, world: int, force_calculation: bool = False) -> int:
        #placeholder
        if force_calculation or self.ranks_int[world] is None:
            if self.epistemic_state['inference_system'] == 'system-z':
                pass
            elif self.epistemic_state['inference_system'] == 'c-inference':
                pass
            else:
                Error('pls select "system-z" or "c-inference" as inference system')
        return self.ranks[world] # type: ignore

    def z_part2ocf(self, world: int) -> None:
        self.ranks_int[world] = random.randint(0, 10)

    def c_vec2ocf(self, world: int) -> None:
        self.ranks_int[world] = random.randint(0, 10)

