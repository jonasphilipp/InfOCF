from binascii import Error
from BitVector import BitVector
from random import randint
from frozenlist import FrozenList

from inference import inference 

class PreOCF():
    epistemic_state: dict
    signature: FrozenList

    @property
    def ranks(self) -> dict[BitVector, None | int]:
        return self.epistemic_state['preocfs'][self.signature]

    @property
    def inference_system(self) -> str:
        return self.epistemic_state['inference_system']


    def __init__(self, epistemic_state: dict, marginalization: list = []):
        self.epistemic_state = epistemic_state
        self.signature = FrozenList([s for s in epistemic_state['belief_base'].signature if s not in marginalization])
        if self.signature not in self.epistemic_state['preocfs']:
            ranks =  dict[str, None | int]
            self.epistemic_state['preocfs'][self.signature] = ranks()
            self.bitvec_worlds()


    def bitvec_worlds(self):
        size = len(self.signature)
        for i in range(2**size):
            bv = BitVector(intVal = i, size=size)
            self.ranks[bv] = None


    def is_ocf(self) -> bool:
        for r in self.ranks:
            if self.ranks[r] is None or self.ranks[r] < 0: # type: ignore
                return False
        return True
   

    def marginalize(self, marginalization: list):
        return PreOCF(self.epistemic_state, marginalization)


    def conditionalization_accepts_world(self, world: BitVector, conditionalization: dict[str, int]) -> bool:
        for key, value in conditionalization.items():
            if world[self.signature.index(key)] != value:
                return False
        return True



    def conditionalize(self, conditionalization: dict[str, int]):
        bitvecs = [bv for bv in self.ranks.keys() if self.conditionalization_accepts_world(bv, conditionalization)]
        [self.rank_world(bv) for bv in bitvecs if self.ranks[bv] is None]




    def rank_world(self, bv: BitVector, force_calculation: bool = False) -> int:
        #placeholder
        if force_calculation or self.ranks[bv] is None:
            if self.inference_system == 'system-z':
                pass
            elif self.inference_system == 'c-inference':
                pass
            else:
                Error('pls select "system-z" or "c-inference" as inference system')
        return self.ranks[bv] # type: ignore

