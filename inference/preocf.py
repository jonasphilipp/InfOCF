from binascii import Error
import random
from BitVector import BitVector
import pysmt
from pysmt.shortcuts import Symbol, Not, Solver, And, is_sat, Plus, GE, GT, Int
from pysmt.typing import BOOL, INT
from pysmt.fnode import FNode
from inference import c_inference, system_z
import inference
import logging
from inference.conditional import Conditional
from inference.belief_base import BeliefBase
from inference.inference_operator import Inference
from inference.consistency_sat import consistency
from inference.inference_operator import create_epistemic_state
from z3 import Optimize, z3, And, sat
# std-lib imports for persistence helpers
import json, pickle, pathlib, warnings
from abc import ABC, abstractmethod
from infocf import get_logger

# Create a logger object
logger = get_logger(__name__)

# parms: bb, ranks

# signature, bb, systemz
# signature, bb, random_min_c_rep
class PreOCF(ABC):
    #epistemic_state: dict
    ranks: dict[str, None | int]
    signature: list[str]
    conditionals: dict[int, Conditional]
    ranking_system: str
    _z_partition: list[Conditional]
    _state: dict[str, object]
    _csp: list[FNode]
    _optimizer: Optimize
    _impacts: list[int]

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

    def __init__(self, ranks: dict[str, None | int], signature: list | None, conditionals: dict[int, Conditional] | None, ranking_system: str, metadata: dict[str, object] | None = None):
        self.ranks = ranks
        self.signature = signature
        self.conditionals = conditionals
        self.ranking_system = ranking_system
        # Initialise metadata storage
        if metadata is None:
            self._metadata = {}
        elif isinstance(metadata, dict):
            self._metadata = metadata
        else:
            raise TypeError("metadata must be a dict[str, object] or None")

    # ------------------------------------------------------------------
    # Metadata convenience API
    # ------------------------------------------------------------------
    def save_meta(self, key: str, value: object) -> None:
        """Store arbitrary metadata under the given key inside the OCF instance."""
        self._metadata[key] = value

    def load_meta(self, key: str, default: object = None) -> object:
        """Retrieve metadata previously stored with save_meta(); returns *default* if key absent."""
        return self._metadata.get(key, default)

    @property
    def metadata(self) -> dict[str, object]:
        """Direct access to the metadata store (read-write)."""
        return self._metadata

    # ------------------------------------------------------------------
    # Disk-level persistence helpers (JSON / pickle)
    # ------------------------------------------------------------------
    def save_metadata(self, path: str | pathlib.Path, fmt: str = "pickle") -> None:
        """Dump the internal metadata dict to *path*."""
        path = pathlib.Path(path)
        if fmt == "pickle":
            with path.open("wb") as fd:
                pickle.dump(self._metadata, fd)
        elif fmt == "json":
            try:
                with path.open("w") as fd:
                    json.dump(self._metadata, fd, indent=2, default=str)
            except TypeError as e:
                raise TypeError("Some metadata values are not JSON-serialisable") from e
        else:
            raise ValueError("fmt must be 'pickle' or 'json'")

    def load_metadata(self, path: str | pathlib.Path) -> None:
        """Load a metadata file (pickle or JSON). Existing keys are overwritten."""
        path = pathlib.Path(path)
        if not path.exists():
            warnings.warn(f"No metadata file at {path} – nothing loaded", RuntimeWarning)
            return

        if path.suffix == ".json":
            data = json.loads(path.read_text())
        else:  # assume pickle by default
            with path.open("rb") as fd:
                data = pickle.load(fd)

        if not isinstance(data, dict):
            raise ValueError("Metadata file did not contain a dict")

        self._metadata.update(data)

    # ------------------------------------------------------------------
    # Full-object persistence helpers (no manual key bookkeeping needed)
    # ------------------------------------------------------------------
    def __getstate__(self):
        """Return complete object state as dict. Useful for manual state inspection/manipulation."""
        return self.__dict__.copy()

    def __setstate__(self, state):
        """Restore object from state dict."""
        self.__dict__.update(state)

    def save_ocf(self, path: str | pathlib.Path, *, protocol: int = pickle.HIGHEST_PROTOCOL) -> None:
        """Serialize the entire PreOCF object to *path* via pickle so it can be restored later without manual bookkeeping."""
        path = pathlib.Path(path)
        
        # Temporarily remove non-picklable objects for serialization
        non_picklable_backups = {}
        non_picklable_attrs = ['_optimizer', '_csp']  # Add other non-picklable attributes as needed
        
        for attr in non_picklable_attrs:
            if hasattr(self, attr):
                non_picklable_backups[attr] = getattr(self, attr)
                setattr(self, attr, None)
        
        try:
            with path.open('wb') as fd:
                pickle.dump(self, fd, protocol=protocol)
        finally:
            # Restore all non-picklable objects
            for attr, value in non_picklable_backups.items():
                setattr(self, attr, value)

    @staticmethod
    def load_ocf(path: str | pathlib.Path) -> 'PreOCF':
        """Deserialize a PreOCF instance previously written by `save_ocf`."""
        path = pathlib.Path(path)
        with path.open('rb') as fd:
            obj = pickle.load(fd)
        if not isinstance(obj, PreOCF):
            raise TypeError('Pickle did not contain a PreOCF object')
        
        # Ensure non-picklable attributes exist (helps with objects saved without them)
        non_picklable_attrs = ['_optimizer', '_csp']
        for attr in non_picklable_attrs:
            if attr not in obj.__dict__:
                setattr(obj, attr, None)
        
        return obj

    @classmethod
    def init_system_z(cls, belief_base: BeliefBase, signature: list = None, metadata: dict[str, object] = None) -> 'PreOCF':
        return SystemZPreOCF(belief_base, signature, metadata)

    @classmethod
    def init_random_min_c_rep(cls, belief_base: BeliefBase, signature: list = None, metadata: dict[str, object] = None):
        return RandomMinCRepPreOCF(belief_base, signature, metadata)
    
    @classmethod
    def init_custom(cls, ranks: dict[str, None | int], belief_base: BeliefBase = None, signature: list = None, metadata: dict[str, object] = None):
        return CustomPreOCF(ranks, belief_base, signature, metadata)
    
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
        # Build new signature list by removing marginalized variables
        new_sig = [s for s in self.signature if s not in marginalization]
        # Return a custom OCF with the marginalized ranks
        return PreOCF.init_custom(ranks, None, new_sig, self._metadata)

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


    @abstractmethod
    def rank_world(self, world: str, force_calculation: bool = False) -> int:
        """Return the rank of a world; must be implemented by subclasses."""
        raise NotImplementedError
    

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
            if partition_index == 0:
                return 0
            else:
                return self._rec_z_rank(solver, partition_index - 1)
        else:
            return partition_index + 1
        
    def c_vec2ocf(self, world: str) -> int:
        # Compute rank by counting conditionals violated in the world using pysmt
        rank = 0
        # Convert world bitstring into pysmt boolean assertions
        world_symbols = self.symbolize_bitvec(world)
        # Check each conditional for violation: antecedence ∧ ¬consequence
        for idx, cond in self.conditionals.items():
            solver = Solver(name='z3')
            # Add world constraints
            for sym in world_symbols:
                solver.add_assertion(sym)
            # Add violation constraint
            solver.add_assertion(cond.make_A_then_not_B())
            if solver.solve():
                rank += self._impacts[idx-1]
        return rank
        

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

# PreOCF subclasses and factory
class SystemZPreOCF(PreOCF):
    def __init__(self, belief_base: BeliefBase, signature: list = None, metadata: dict[str, object] = None):
        if signature is None:
            signature = belief_base.signature
        else:
            signature = tuple(signature)
        ranks = PreOCF.create_bitvec_world_dict(signature)
        conditionals = belief_base.conditionals
        super().__init__(ranks, signature, conditionals, 'system-z', metadata)
        self._z_partition, _ = consistency(BeliefBase(signature, conditionals, 'z-partition'))

    def rank_world(self, world: str, force_calculation: bool = False) -> int:
        if force_calculation or self.ranks[world] is None:
            self.ranks[world] = self.z_part2ocf(world)
        return self.ranks[world]

    def z_part2ocf(self, world: str) -> int:
        signature_symbols = self.symbolize_bitvec(world)
        solver = Solver(name='z3')
        [solver.add_assertion(s) for s in signature_symbols]
        return self._rec_z_rank(solver, len(self._z_partition) - 1)

    def _rec_z_rank(self, solver, partition_index) -> int:
        part = self._z_partition[partition_index]
        [solver.add_assertion(Not(c.make_A_then_not_B())) for c in part]
        if solver.solve():
            if partition_index == 0:
                return 0
            return self._rec_z_rank(solver, partition_index - 1)
        return partition_index + 1

class RandomMinCRepPreOCF(PreOCF):
    def __init__(self, belief_base: BeliefBase, signature: list = None, metadata: dict[str, object] = None):
        if signature is None:
            signature = belief_base.signature
        else:
            signature = signature
        ranks = PreOCF.create_bitvec_world_dict(signature)
        conditionals = belief_base.conditionals
        super().__init__(ranks, signature, conditionals, 'random_min_c_rep', metadata)
        epistemic_state = create_epistemic_state(belief_base, 'c-inference', 'z3', 'rc2')
        c_inf = c_inference.CInference(epistemic_state)
        c_inf.preprocess_belief_base(0)
        self._csp = c_inf.base_csp
        pysmt_solver = Solver(name='z3')
        self._csp = [pysmt_solver.converter.convert(expr) for expr in self._csp]
        self._optimizer = Optimize()
        self._optimizer.set(priority='pareto')
        self._optimizer.add(*self._csp)
        [self._optimizer.minimize(z3.Int(f'eta_{i}')) for i in range(1, len(self.conditionals) + 1)]
        if self._optimizer.check() == sat:
            m = self._optimizer.model()
            self._impacts = [int(str(m.eval(z3.Int(f'eta_{i}')))) for i in range(1, len(self.conditionals) + 1)]
        else:
            raise ValueError('no solution found for random min c rep')

    def rank_world(self, world: str, force_calculation: bool = False) -> int:
        if force_calculation or self.ranks[world] is None:
            self.ranks[world] = self.c_vec2ocf(world)
        return self.ranks[world]

    def c_vec2ocf(self, world: str) -> int:
        rank = 0
        world_symbols = self.symbolize_bitvec(world)
        for idx, cond in self.conditionals.items():
            solver = Solver(name='z3')
            for sym in world_symbols:
                solver.add_assertion(sym)
            solver.add_assertion(cond.make_A_then_not_B())
            if solver.solve():
                rank += self._impacts[idx-1]
        return rank

    # ------------------------------------------------------------------
    # Impact vector persistence methods
    # ------------------------------------------------------------------
    def export_impacts(self, path: str | pathlib.Path, fmt: str = "json") -> None:
        """Export the computed impact vector to a file for later reuse."""
        if not hasattr(self, '_impacts') or self._impacts is None:
            raise ValueError("No impacts computed yet. Run the constructor or compute impacts first.")
        
        path = pathlib.Path(path)
        impact_data = {
            "impacts": self._impacts,
            "conditionals_count": len(self.conditionals),
            "ranking_system": self.ranking_system,
            "signature": self.signature
        }
        
        if fmt == "json":
            with path.open("w") as fd:
                json.dump(impact_data, fd, indent=2)
        elif fmt == "pickle":
            with path.open("wb") as fd:
                pickle.dump(impact_data, fd)
        else:
            raise ValueError("fmt must be 'json' or 'pickle'")

    def import_impacts(self, path: str | pathlib.Path) -> None:
        """Import a previously exported impact vector from a file."""
        path = pathlib.Path(path)
        if not path.exists():
            raise FileNotFoundError(f"Impact file not found: {path}")
        
        # Determine format from file extension
        if path.suffix == ".json":
            with path.open("r") as fd:
                impact_data = json.load(fd)
        else:  # assume pickle
            with path.open("rb") as fd:
                impact_data = pickle.load(fd)
        
        # Validate the imported data
        if not isinstance(impact_data, dict):
            raise ValueError("Impact file does not contain a valid data structure")
        
        required_keys = ["impacts", "conditionals_count", "ranking_system", "signature"]
        for key in required_keys:
            if key not in impact_data:
                raise ValueError(f"Impact file missing required key: {key}")
        
        # Validate compatibility
        if impact_data["conditionals_count"] != len(self.conditionals):
            raise ValueError(f"Impact vector size mismatch: file has {impact_data['conditionals_count']}, "
                           f"current PreOCF has {len(self.conditionals)} conditionals")
        
        if impact_data["ranking_system"] != self.ranking_system:
            warnings.warn(f"Ranking system mismatch: file has '{impact_data['ranking_system']}', "
                         f"current PreOCF has '{self.ranking_system}'", RuntimeWarning)
        
        if impact_data["signature"] != self.signature:
            warnings.warn(f"Signature mismatch: file has {impact_data['signature']}, "
                         f"current PreOCF has {self.signature}", RuntimeWarning)
        
        # Import the impacts
        self._impacts = impact_data["impacts"]
        
        # Store import metadata
        self.save_meta("impacts_imported_from", str(path))
        import time
        self.save_meta("impacts_import_timestamp", time.time())

    @classmethod
    def init_with_impacts(cls, belief_base: BeliefBase, impacts_path: str | pathlib.Path, 
                         signature: list = None, metadata: dict[str, object] = None) -> 'RandomMinCRepPreOCF':
        """Create a RandomMinCRepPreOCF instance using pre-computed impacts from a file."""
        # Create instance without computing impacts (we'll override them)
        instance = cls.__new__(cls)
        
        # Initialize parent class attributes
        if signature is None:
            signature = belief_base.signature
        ranks = PreOCF.create_bitvec_world_dict(signature)
        conditionals = belief_base.conditionals
        PreOCF.__init__(instance, ranks, signature, conditionals, 'random_min_c_rep', metadata)
        
        # Set placeholders for attributes that would normally be computed
        instance._csp = None
        instance._optimizer = None
        
        # Import the impacts
        instance.import_impacts(impacts_path)
        
        return instance

    # ------------------------------------------------------------------
    # Simple impact vector load/save methods (Python lists)
    # ------------------------------------------------------------------
    def save_impacts(self) -> list[int]:
        """Return the current impact vector as a Python list for easy storage/transfer."""
        if not hasattr(self, '_impacts') or self._impacts is None:
            raise ValueError("No impacts computed yet. Run the constructor or compute impacts first.")
        return self._impacts.copy()

    def load_impacts(self, impacts: list[int]) -> None:
        """Load impact vector from a Python list with basic validation."""
        if not isinstance(impacts, list):
            raise TypeError("Impacts must be a list of integers")
        
        if not all(isinstance(x, int) for x in impacts):
            raise TypeError("All impact values must be integers")
        
        if len(impacts) != len(self.conditionals):
            raise ValueError(f"Impact vector size mismatch: provided {len(impacts)}, "
                           f"expected {len(self.conditionals)} (number of conditionals)")
        
        if any(x < 0 for x in impacts):
            raise ValueError("Impact values must be non-negative")
        
        self._impacts = impacts.copy()
        
        # Store load metadata
        self.save_meta("impacts_loaded_from_list", True)
        import time
        self.save_meta("impacts_load_timestamp", time.time())

    @classmethod
    def init_with_impacts_list(cls, belief_base: BeliefBase, impacts: list[int], 
                              signature: list = None, metadata: dict[str, object] = None) -> 'RandomMinCRepPreOCF':
        """Create a RandomMinCRepPreOCF instance using a pre-computed impact vector list."""
        # Create instance without computing impacts (we'll override them)
        instance = cls.__new__(cls)
        
        # Initialize parent class attributes
        if signature is None:
            signature = belief_base.signature
        ranks = PreOCF.create_bitvec_world_dict(signature)
        conditionals = belief_base.conditionals
        PreOCF.__init__(instance, ranks, signature, conditionals, 'random_min_c_rep', metadata)
        
        # Set placeholders for attributes that would normally be computed
        instance._csp = None
        instance._optimizer = None
        
        # Load the impacts
        instance.load_impacts(impacts)
        
        return instance

class CustomPreOCF(PreOCF):
    def __init__(self, ranks: dict[str, None | int], belief_base: BeliefBase = None, signature: list = None, metadata: dict[str, object] = None):
        super().__init__(ranks, signature or (belief_base.signature if belief_base else None), belief_base.conditionals if belief_base else None, 'custom', metadata)

    def rank_world(self, world: str, force_calculation: bool = False) -> int:
        rank = self.ranks.get(world)
        if rank is None:
            raise ValueError(f'provide custom ranking function for world: {world}')
        return rank

def create_preocf(ranking_system: str, *args, **kwargs) -> PreOCF:
    if ranking_system == 'system-z':
        return SystemZPreOCF(*args, **kwargs)
    elif ranking_system == 'random_min_c_rep':
        return RandomMinCRepPreOCF(*args, **kwargs)
    elif ranking_system == 'custom':
        return CustomPreOCF(*args, **kwargs)
    else:
        raise ValueError(f"Unknown ranking system: {ranking_system}")
