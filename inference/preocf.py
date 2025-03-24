from binascii import Error
import random
from BitVector import BitVector

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


    def conditionalization_accepts_world(self, world: str, conditionalization: dict[str, int]) -> bool:
        for key, value in conditionalization.items():
            if int(world[self.signature.index(key)]) != value:
                return False
        return True


    def filter_worlds_by_conditionalization(self, conditionalization: dict[str, int]) -> list[str]:
        return [w for w in self.ranks.keys() if self.conditionalization_accepts_world(w, conditionalization)]


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
                self.z_part2ocf(world)
            elif self.epistemic_state['inference_system'] == 'c-inference':
                self.c_vec2ocf(world)
            else:
                Error('pls select "system-z" or "c-inference" as inference system')
        rank = self.ranks[world]
        assert rank is not None
        return rank 


    def z_part2ocf(self, world: str) -> None:
        self.ranks[world] = random.randint(0, 10)


    def c_vec2ocf(self, world: str) -> None:
        self.ranks[world] = random.randint(0, 10)

