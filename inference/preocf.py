"""(Pre-) Ordinal Conditional Functions (Pre-OCFs).

This module provides a common interface (``PreOCF``) and concrete
implementations for computing and querying ordinal conditional rankings
over possible worlds.

Worlds are represented as bitstrings over a boolean signature (e.g.,
"1010" for ``signature == ["b", "p", "f", "w"]``). Ranks are integers
greater-or-equal to 0 (lower is more plausible). Some methods compute
ranks lazily on demand.

Notes
-----
Security
    Saving and loading complete OCF objects uses Python's pickle format.
    Only call ``load_ocf`` with files from trusted sources. For safer
    persistence of ancillary data, prefer ``save_metadata`` / ``load_metadata``
    with JSON.
"""

# std-lib imports for persistence helpers
import json
import pathlib
import pickle
import warnings
from abc import ABC, abstractmethod
from collections.abc import Iterator, MutableMapping
from dataclasses import dataclass
from typing import Callable

from BitVector import BitVector
from pysmt.fnode import FNode
from pysmt.shortcuts import (
    FALSE,
    TRUE,
    And,
    Not,
    Or,
    Solver,
    Symbol,
    get_free_variables,
)
from pysmt.typing import BOOL
from z3 import Optimize, sat, z3

from inference.belief_base import BeliefBase
from inference.c_inference import CInference
from inference.conditional import Conditional
from inference.consistency_diagnostics import (
    Diagnostics,
    consistency_diagnostics,
    format_diagnostics_verbose,
)
from inference.consistency_sat import consistency
from inference.inference_manager import create_epistemic_state
from infocf.log_setup import get_logger
from parser.Wrappers import parse_formula

# Create a logger object
logger = get_logger(__name__)


@dataclass(frozen=True)
class SystemZSymbolicBucket:
    """Symbolic descriptor for one System Z rank bucket."""

    rank: int
    formula: FNode
    partition_index: int | None
    layer_size: int
    is_infinity: bool


class DenseWorldRankMapping(MutableMapping[str, int | None]):
    """Mapping view over a dense internal rank store indexed by world number."""

    def __init__(self, parent: "PreOCF"):
        self._parent = parent

    def __getitem__(self, world: str) -> int | None:
        return self._parent._get_rank_value(world)

    def __setitem__(self, world: str, rank: int | None) -> None:
        self._parent._set_rank_value(world, rank)

    def __delitem__(self, world: str) -> None:
        self._parent._set_rank_value(world, None)

    def __iter__(self) -> Iterator[str]:
        return self._parent.iter_worlds()

    def __len__(self) -> int:
        return self._parent.world_count

    def __eq__(self, other: object) -> bool:
        if isinstance(other, MutableMapping):
            return dict(self.items()) == dict(other.items())
        if isinstance(other, dict):
            return dict(self.items()) == other
        return NotImplemented  # type: ignore[return-value]

    def copy(self) -> dict[str, int | None]:
        return dict(self.items())


# parms: bb, ranks


# signature, bb, systemz
# signature, bb, random_min_c_rep
class PreOCF(ABC):
    """Abstract base class for ordinal conditional functions (Pre-OCFs).

    Parameters
    ----------
    ranks : dict[str, int | None]
        Mapping from world bitstrings to ranks; ``None`` indicates
        "not yet computed".
    signature : list[str] | None
        Variable names defining world bit positions.
    conditionals : dict[int, Conditional] | None
        Indexed conditionals used by concrete ranking systems.
    ranking_system : str
        Identifier of the ranking approach (e.g., ``"system-z"``,
        ``"random_min_c_rep"``).
    metadata : dict[str, object] | None, optional
        Free-form metadata store persisted with the instance.

    Attributes
    ----------
    ranks_verbose : dict[tuple[str, ...], int | None]
        Human-readable view (tuples of signed literals) mapped to ranks.
    metadata : dict[str, object]
        Read–write metadata store.
    """

    # epistemic_state: dict
    ranks: dict[str, None | int]
    signature: list[str]
    conditionals: dict[int, Conditional] | None
    ranking_system: str
    _z_partition: list[list[Conditional]]
    _state: dict[str, object]
    _csp: list[FNode] | None
    _optimizer: Optimize | None
    # Impacts are non-negative integers in the classical c-representation
    # setting (Def. 5), and ``int | float`` in the extended setting where
    # strict (``Δ^∞``) and "triggered" conditionals carry ``η = ∞`` —
    # the sentinel value is ``inference.extended_c_rep.INFINITY``.
    _impacts: list[int | float]

    # return ranks dict with verbose world names
    # str len == 5
    #         strlist =[sig[i] if bv[i] == 1 else '!'+sig[i] for i in range(len(sig))]
    # like above but
    @property
    def ranks_verbose(self) -> dict[tuple[str, ...], None | int]:
        return {self.bv2strtuple(r): self.ranks[r] for r in self.ranks.keys()}

    def bv2strtuple(self, bv: BitVector) -> tuple[str, ...]:
        if self.signature is None:
            raise ValueError("bv2strtuple requires a named signature")
        return tuple(
            [
                self.signature[i] if bv[i] == "1" else "!" + self.signature[i]
                for i in range(len(self.signature))
            ]
        )

    # probably not needed, not gonna throw away now
    """
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
    """

    def __init__(
        self,
        ranks: dict[str, None | int] | None,
        signature: list | None,
        conditionals: dict[int, Conditional] | None,
        ranking_system: str,
        metadata: dict[str, object] | None = None,
    ):
        self.signature = signature
        if signature is not None and ranks is None:
            self._world_count = 2 ** len(signature)
            self._rank_store: list[int | None] = [None] * self._world_count
            self.ranks = DenseWorldRankMapping(self)  # type: ignore[assignment]
            self._dense_ranks_enabled = True
        else:
            if ranks is None:
                raise ValueError("ranks may only be None when a signature is provided")
            self.ranks = ranks
            self._rank_store = []
            self._world_count = len(ranks)
            self._dense_ranks_enabled = False
        if signature is not None:
            self._signature_symbols = [Symbol(name, BOOL) for name in signature]
            self._neg_signature_symbols = [
                Not(symbol) for symbol in self._signature_symbols
            ]
        else:
            self._signature_symbols = []
            self._neg_signature_symbols = []
        # conditionals can be None for CustomPreOCF
        self.conditionals = conditionals
        self.ranking_system = ranking_system
        # Internal state store (not part of user metadata)
        self._state = {}
        # Initialise metadata storage
        if metadata is None:
            self._metadata = {}
        elif isinstance(metadata, dict):
            self._metadata = metadata
        else:
            raise TypeError("metadata must be a dict[str, object] or None")

    @property
    def world_count(self) -> int:
        return self._world_count

    def world_to_index(self, world: str) -> int:
        if self.signature is None:
            raise ValueError("world_to_index requires a named signature")
        if len(world) != len(self.signature) or any(bit not in "01" for bit in world):
            raise KeyError(f"invalid world bitstring: {world}")
        return int(world, 2)

    def index_to_world(self, index: int) -> str:
        if self.signature is None:
            raise ValueError("index_to_world requires a named signature")
        if index < 0 or index >= self.world_count:
            raise IndexError(f"world index out of bounds: {index}")
        return format(index, f"0{len(self.signature)}b")

    def iter_worlds(self) -> Iterator[str]:
        if self._dense_ranks_enabled:
            for index in range(self.world_count):
                yield self.index_to_world(index)
            return
        yield from self.ranks.keys()

    def iter_world_indices(self) -> Iterator[int]:
        if self._dense_ranks_enabled:
            yield from range(self.world_count)
            return
        for world in self.ranks.keys():
            yield self.world_to_index(world)

    def _get_rank_value(self, world: str) -> int | None:
        if self._dense_ranks_enabled:
            return self._rank_store[self.world_to_index(world)]
        return self.ranks[world]

    def _set_rank_value(self, world: str, rank: int | None) -> None:
        if self._dense_ranks_enabled:
            self._rank_store[self.world_to_index(world)] = rank
            return
        self.ranks[world] = rank

    def _get_rank_value_by_index(self, index: int) -> int | None:
        if self._dense_ranks_enabled:
            return self._rank_store[index]
        return self.ranks[self.index_to_world(index)]

    def _set_rank_value_by_index(self, index: int, rank: int | None) -> None:
        if self._dense_ranks_enabled:
            self._rank_store[index] = rank
            return
        self.ranks[self.index_to_world(index)] = rank

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
    # Security: Save methods default to JSON for safety, load methods support both
    # ------------------------------------------------------------------
    def save_metadata(self, path: str | pathlib.Path, fmt: str = "json") -> None:
        """Dump the internal metadata dict to *path*.

        Format selection:
        - If the file extension is ".json" or ".pkl"/".pickle", the extension determines the format.
        - Otherwise, the explicit fmt argument is used (defaults to JSON).
        """
        path = pathlib.Path(path)
        # Infer format from path suffix when possible
        if path.suffix.lower() == ".json":
            target_fmt = "json"
        elif path.suffix.lower() in {".pkl", ".pickle"}:
            target_fmt = "pickle"
        else:
            target_fmt = fmt

        if target_fmt == "pickle":
            with path.open("wb") as fd:
                pickle.dump(self._metadata, fd)
        elif target_fmt == "json":
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
            warnings.warn(
                f"No metadata file at {path} – nothing loaded", RuntimeWarning
            )
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
    def __getstate__(self) -> dict[str, object]:
        """Return complete object state as dict. Useful for manual state inspection/manipulation."""
        return self.__dict__.copy()

    def __setstate__(self, state: dict[str, object]) -> None:
        """Restore object from state dict."""
        self.__dict__.update(state)

    def save_ocf(
        self, path: str | pathlib.Path, *, protocol: int = pickle.HIGHEST_PROTOCOL
    ) -> None:
        """Serialize the entire PreOCF object to *path* via pickle so it can be restored later without manual bookkeeping.

        Security Note: Saved OCF files use pickle format for complete object preservation.
        Only share these files with trusted collaborators in your research environment.
        """
        path = pathlib.Path(path)

        # Temporarily remove non-picklable objects for serialization
        non_picklable_backups = {}
        non_picklable_attrs = [
            "_optimizer",
            "_csp",
        ]  # Add other non-picklable attributes as needed

        for attr in non_picklable_attrs:
            if hasattr(self, attr):
                non_picklable_backups[attr] = getattr(self, attr)
                setattr(self, attr, None)

        try:
            with path.open("wb") as fd:
                pickle.dump(self, fd, protocol=protocol)
        finally:
            # Restore all non-picklable objects
            for attr, value in non_picklable_backups.items():
                setattr(self, attr, value)

    @staticmethod
    def load_ocf(path: str | pathlib.Path, *, trusted: bool = False) -> "PreOCF":
        """Deserialize a PreOCF instance previously written by `save_ocf`.

        Security Note: Only load OCF files from trusted sources. This method uses
        pickle deserialization which can execute arbitrary code if the file is malicious.

        Args:
            path: Path to the pickled PreOCF file
            trusted: Set to True to acknowledge you trust the source of this file
        """
        if not trusted:
            import warnings

            warnings.warn(
                "Loading OCF files uses pickle deserialization which can be unsafe. "
                "Only load files from trusted sources. Set trusted=True to suppress this warning.",
                UserWarning,
                stacklevel=2,
            )

        path = pathlib.Path(path)
        with path.open("rb") as fd:
            obj = pickle.load(fd)
        if not isinstance(obj, PreOCF):
            raise TypeError("Pickle did not contain a PreOCF object")

        # Ensure non-picklable attributes exist (helps with objects saved without them)
        non_picklable_attrs = ["_optimizer", "_csp"]
        for attr in non_picklable_attrs:
            if attr not in obj.__dict__:
                setattr(obj, attr, None)

        return obj

    @classmethod
    def init_system_z(
        cls,
        belief_base: BeliefBase,
        signature: list | None = None,
        metadata: dict[str, object] | None = None,
        facts: list[str | FNode] | None = None,
        *,
        extended: bool | None = None,
    ) -> "SystemZPreOCF":
        return SystemZPreOCF(
            belief_base, signature, metadata, facts=facts, extended=extended
        )

    @classmethod
    def init_random_min_c_rep(
        cls,
        belief_base: BeliefBase,
        signature: list | None = None,
        metadata: dict[str, object] | None = None,
    ) -> "RandomMinCRepPreOCF":
        return RandomMinCRepPreOCF(belief_base, signature, metadata)

    @classmethod
    def init_custom(
        cls,
        ranks: dict[str, None | int],
        belief_base: BeliefBase | None = None,
        signature: list | None = None,
        metadata: dict[str, object] | None = None,
    ) -> "CustomPreOCF":
        return CustomPreOCF(ranks, belief_base, signature, metadata)

    @classmethod
    def create_bitvec_world_dict(
        cls, signature: list[str] | None = None
    ) -> dict[str, int | None]:
        if signature is None:
            # Called as instance method
            if not hasattr(cls, "signature"):
                raise ValueError(
                    "Signature not provided and not available as instance attribute"
                )
            signature = cls.signature

        worlds = [
            str(BitVector(intVal=i, size=len(signature)))
            for i in range(2 ** len(signature))
        ]
        ranks = dict.fromkeys(worlds, None)
        return ranks

    # probably not needed, not gonna throw away now
    """
    def int2bitvec(self, world: int):
        return BitVector(intVal = world, size=len(self.signature))

    def bitvec2strlist(self, bv: BitVector) -> list[str]:
        sig = self.signature
        ### not cool, use real negation
        strlist =[sig[i] if bv[i] == 1 else '!'+sig[i] for i in range(len(sig))]
        return strlist

    def int2strlist(self, world: int) -> list[str]:
        return self.bitvec2strlist(self.int2bitvec(world))
    """

    def is_ocf(self) -> bool:
        for world in self.iter_worlds():
            rank = self._get_rank_value(world)
            if rank is None or rank < 0:
                return False
        return True

    # returns new PreOCF with marginalized signature and ranks that are the minimum of the ranks of the worlds with the same marginalized signature
    def marginalize(self, marginalization: list[str]) -> "PreOCF":
        """Return a new PreOCF marginalized to a subset of variables.

        Parameters
        ----------
        marginalization : list[str]
            Variables to eliminate from the signature.

        Returns
        -------
        PreOCF
            A custom PreOCF over the reduced signature whose world ranks
            are the minimum over compatible original worlds.
        """
        if self.signature is None:
            raise ValueError("marginalize requires a named signature")
        ranks: dict[str, int | None] = {}
        for world in self.iter_worlds():
            # remove all bits whose index matches the one of the signature elements in marginalization
            new_world = "".join(
                [
                    world[i]
                    for i in range(len(world))
                    if self.signature[i] not in marginalization
                ]
            )
            world_rank = self._get_rank_value(world)
            if world_rank is not None:
                if ranks.get(new_world) is None:
                    ranks[new_world] = world_rank
                else:
                    # Both values are guaranteed to be int here due to the check above
                    curr_rank = ranks[new_world]
                    assert curr_rank is not None and world_rank is not None
                    ranks[new_world] = min(curr_rank, world_rank)
        # Build new signature list by removing marginalized variables
        new_sig = [s for s in self.signature if s not in marginalization]
        # Return a custom OCF with the marginalized ranks
        return PreOCF.init_custom(ranks, None, new_sig, self._metadata)

    """
    # not only sig elems
    def conditionalization_permits_world(self, world: str, conditionalization: dict[str, int]) -> bool:
        for key, value in conditionalization.items():
            if int(world[self.signature.index(key)]) != value:
                return False
        return True
    """

    # world satisfies formula
    def world_satisfies_conditionalization(
        self, world: str, conditionalization: FNode
    ) -> bool:
        solver = Solver(name="z3")
        self.add_world_assertions(solver, world)
        solver.add_assertion(conditionalization)
        result: bool = solver.solve()
        return result

    def filter_worlds_by_conditionalization(
        self, conditionalization: FNode
    ) -> list[str]:
        if self._dense_ranks_enabled:
            matching_worlds: list[str] = []
            solver = Solver(name="z3")
            for index in self.iter_world_indices():
                solver.push()
                self.add_world_index_assertions(solver, index)
                solver.add_assertion(conditionalization)
                if solver.solve():
                    matching_worlds.append(self.index_to_world(index))
                solver.pop()
            return matching_worlds

        return [
            w
            for w in self.iter_worlds()
            if self.world_satisfies_conditionalization(w, conditionalization)
        ]

    def compute_conditionalization(
        self, conditionalization: FNode
    ) -> dict[str, None | int]:
        worlds = self.filter_worlds_by_conditionalization(conditionalization)
        return {w: self.rank_world(w) for w in worlds}

    def conditionalize_existing_ranks(
        self, conditionalization: FNode
    ) -> dict[str, None | int]:
        worlds = self.filter_worlds_by_conditionalization(conditionalization)
        conditionalized_ranks = {w: self._get_rank_value(w) for w in worlds}
        return conditionalized_ranks

    def compute_all_ranks(self) -> dict[str, None | int]:
        return {w: self.rank_world(w) for w in self.iter_worlds()}

    @abstractmethod
    def rank_world(self, world: str, force_calculation: bool = False) -> int:
        """Return the rank of a world; must be implemented by subclasses."""
        raise NotImplementedError

    def _rank_world_index(self, index: int, force_calculation: bool = False) -> int:
        return self.rank_world(self.index_to_world(index), force_calculation)

    def symbolize_world_index(self, index: int) -> list[FNode]:
        if self.signature is None:
            raise ValueError("symbolize_world_index requires a named signature")
        literals: list[FNode] = []
        width = len(self.signature)
        for offset in range(width):
            bit_mask = 1 << (width - offset - 1)
            if index & bit_mask:
                literals.append(self._signature_symbols[offset])
            else:
                literals.append(self._neg_signature_symbols[offset])
        return literals

    def add_world_assertions(self, solver: Solver, world: str) -> None:
        for symbol in self.symbolize_bitvec(world):
            solver.add_assertion(symbol)

    def add_world_index_assertions(self, solver: Solver, index: int) -> None:
        for symbol in self.symbolize_world_index(index):
            solver.add_assertion(symbol)

    def symbolize_bitvec(self, bitvec: str) -> list[FNode]:
        return self.symbolize_world_index(self.world_to_index(bitvec))

    def z_part2ocf(self, world: str) -> int:
        signature_symbols = self.symbolize_bitvec(world)
        solver = Solver(name="z3")
        [solver.add_assertion(s) for s in signature_symbols]
        rank = self._rec_z_rank(solver, len(self._z_partition) - 1)
        return rank

    def _rec_z_rank(self, solver: Solver, partition_index: int) -> int:
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
        assert self.conditionals is not None, "conditionals required for c_vec2ocf"
        rank = 0
        # Convert world bitstring into pysmt boolean assertions
        world_symbols = self.symbolize_bitvec(world)
        # Check each conditional for violation: antecedence ∧ ¬consequence
        for idx, cond in self.conditionals.items():
            solver = Solver(name="z3")
            # Add world constraints
            for sym in world_symbols:
                solver.add_assertion(sym)
            # Add violation constraint
            solver.add_assertion(cond.make_A_then_not_B())
            if solver.solve():
                rank += self._impacts[idx - 1]
        return rank

    # smallest rank of any world that satisfies formula
    def formula_rank(self, formula: FNode) -> int | None:
        """Return the smallest rank among worlds satisfying ``formula``.

        Parameters
        ----------
        formula : FNode
            Boolean formula over the current signature.

        Returns
        -------
        int | None
            Minimum rank if any world satisfies ``formula``, otherwise ``None``.

        See Also
        --------
        conditional_acceptance
        """
        min_rank = None
        solver = Solver(name="z3")

        # Check each world
        for index in self.iter_world_indices():
            # Push a new scope
            solver.push()

            # Add the world's constraints
            self.add_world_index_assertions(solver, index)

            # Add the formula to check
            solver.add_assertion(formula)

            # If this world satisfies the formula, check its rank
            if solver.solve():
                rank = self._rank_world_index(index)
                if min_rank is None or rank < min_rank:
                    min_rank = rank

            # Pop the scope to remove world-specific constraints
            solver.pop()

        return min_rank

    # true if formula_rank of verification is smaller than formula_rank of negation
    def conditional_acceptance(self, conditional: Conditional) -> bool:
        """Return True iff ``(B|A)`` is accepted.

        The acceptance test is defined as ``rank(A ∧ B) < rank(A ∧ ¬B)``.
        """
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
        assert self.conditionals is not None, "conditionals required for impacts2ocf"
        rank = 0
        signature_symbols = self.symbolize_bitvec(world)
        solver = Solver(name="z3")
        [solver.add_assertion(s) for s in signature_symbols]
        for index, conditional in self.conditionals.items():
            solver.add_assertion(Not(conditional.make_A_then_not_B()))
        if not solver.solve():
            rank += vector[index]
        return rank


# convert ranks to total preorder
def ranks2tpo(ranks: dict[str, None | int]) -> list[set[str]]:
    """Convert a rank map to a total preorder (layers of worlds).

    Parameters
    ----------
    ranks : dict[str, int | None]
        World-to-rank mapping.

    Returns
    -------
    list[set[str]]
        Layers (ascending by rank), each a set of world bitstrings.
    """
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
def tpo2ranks(
    tpo: list[set[str]], rank_function: Callable[[int], int]
) -> dict[str, None | int]:
    """Convert a total preorder to ranks using a layer rank function.

    Parameters
    ----------
    tpo : list[set[str]]
        Layers of worlds (0 is most plausible).
    rank_function : Callable[[int], int]
        Function mapping layer index -> rank value.

    Returns
    -------
    dict[str, int | None]
        World-to-rank mapping.
    """
    ranks: dict[str, int | None] = {}
    for layer_num, layer in enumerate(tpo):
        for world in layer:
            ranks[world] = rank_function(layer_num)
    return ranks


# PreOCF subclasses and factory
class SystemZPreOCF(PreOCF):
    """System Z ranking via partition computation.

    Computes a System Z partition for the belief base; optionally uses
    extended semantics and weak facts, and stores diagnostics in metadata.
    Provides accessors for partition metadata such as layers and levels.
    """

    def __init__(
        self,
        belief_base: BeliefBase,
        signature: list | None = None,
        metadata: dict[str, object] | None = None,
        *,
        facts: list[str | FNode] | None = None,
        extended: bool | None = None,
    ):
        if signature is None:
            signature = belief_base.signature
        else:
            signature = list(signature)
        conditionals = belief_base.conditionals
        super().__init__(None, signature, conditionals, "system-z", metadata)

        # If facts provided, augment the belief base with (Bottom | ¬φ) as weakly-placed constraints,
        # where each φ is a formula asserted by the user (negate φ yourself to assert falsehood).
        if facts:
            # Determine extended mode: infer True when unspecified, otherwise use the explicit value
            computed_extended = extended if extended is not None else True
            self._state["z_extended_inferred_from_facts"] = extended is None
            self._state["z_extended_user_explicit"] = extended is not None
            self._state["z_facts_present"] = True
            # Persist the provided facts (stringified) for summaries/debugging
            facts_str_list: list[str] = []
            if extended is False:
                logger.warning(
                    "Facts are intended for extended semantics; proceeding with extended=False as requested"
                )
            # Validate variables and build additional fact conditionals
            fact_conditionals: dict[int, Conditional] = {}
            next_index = max(conditionals.keys(), default=0) + 1
            for entry in facts:
                # Parse entry to a pysmt formula (FNode)
                if isinstance(entry, FNode):
                    phi = entry
                    display = str(phi)
                elif isinstance(entry, str):
                    phi = parse_formula(entry)
                    display = entry
                else:
                    raise TypeError(
                        "facts entries must be formula strings or pysmt FNode objects"
                    )

                # Validate variables used in the formula against the signature
                free_vars = {v.symbol_name() for v in get_free_variables(phi)}
                unknown_vars = free_vars.difference(set(signature))
                if unknown_vars:
                    raise ValueError(
                        f"unknown variable(s) in facts formula: {sorted(unknown_vars)}"
                    )

                # Build (FALSE | ¬φ) to penalize ¬φ worlds, making φ preferred
                antecedent = Not(phi)

                # Pretty-print antecedent using project syntax: '|' -> ';', '&' -> ','
                antecedent_str = str(antecedent)
                antecedent_str = antecedent_str.replace(" | ", "; ")
                antecedent_str = antecedent_str.replace(" & ", ", ")

                fact_cond = Conditional(
                    consequence=FALSE(),
                    antecedence=antecedent,
                    textRepresentation=f"(Bottom|{antecedent_str})",
                )
                fact_cond.index = next_index  # type: ignore[attr-defined]
                fact_conditionals[next_index] = fact_cond
                next_index += 1
                facts_str_list.append(str(display))

            # Build an augmented belief base
            augmented_conditionals = dict(conditionals)
            augmented_conditionals.update(fact_conditionals)
            augmented_bb = BeliefBase(
                signature, augmented_conditionals, "z-partition-with-facts"
            )

            # Compute partition (may be inconsistent). Always compute diagnostics and save metadata,
            # so callers can inspect them even if we raise due to inconsistency.
            part, stats = consistency(augmented_bb, weakly=computed_extended)
            precomputed = {
                ("combined_extended" if computed_extended else "combined_standard"): (
                    part,
                    stats,
                )
            }
            diag = consistency_diagnostics(
                BeliefBase(signature, conditionals, "z-partition"),
                extended=bool(computed_extended),
                uses_facts=True,
                facts=facts,
                precomputed=precomputed,
                on_inconsistent="warn",
            )
            self.save_meta("consistency_diagnostics", diag)
            self.save_meta("input_facts", facts_str_list)
            self.save_meta("input_facts_count", len(facts_str_list))
            if part is False:
                # Include verbose diagnostics in the error message (operator + diagnostics only)
                from inference.consistency_diagnostics import (
                    format_diagnostics_verbose as _fmt_diag,
                )

                raise ValueError(f"system-z: {_fmt_diag(diag)}")
            self._z_partition = part
            # Record partition mode and stats for later consumers (internal state)
            self._state["z_partition_extended"] = bool(computed_extended)
            self._state["z_partition_stats"] = {
                "layers": stats[0],
                "calls": stats[1],
                "levels": stats[2],
            }
            self._state["z_partition_source"] = "augmented_with_facts"
        else:
            # Determine extended mode: default to False when unspecified and no facts
            computed_extended = extended if extended is not None else False
            self._state["z_extended_inferred_from_facts"] = False
            self._state["z_extended_user_explicit"] = extended is not None
            self._state["z_facts_present"] = False
            # Compute partition in base or extended mode depending on flag
            base_bb = BeliefBase(signature, conditionals, "z-partition")
            part, stats = consistency(base_bb, weakly=computed_extended)
            self._z_partition = part
            # Record partition mode and stats for later consumers (internal state)
            self._state["z_partition_extended"] = bool(computed_extended)
            self._state["z_partition_stats"] = {
                "layers": stats[0],
                "calls": stats[1],
                "levels": stats[2],
            }
            self._state["z_partition_source"] = "base"

            # Run diagnostics, reusing the already computed base partition
            precomputed = {
                ("base_extended" if computed_extended else "base_standard"): (
                    part,
                    stats,
                )
            }
            diag = consistency_diagnostics(
                base_bb,
                extended=bool(computed_extended),
                uses_facts=False,
                facts=None,
                precomputed=precomputed,
                on_inconsistent="warn",
            )
            self.save_meta("consistency_diagnostics", diag)

    def rank_world(self, world: str, force_calculation: bool = False) -> int:
        rank = self._get_rank_value(world)
        if force_calculation or rank is None:
            rank = self.z_part2ocf(world)
            self._set_rank_value(world, rank)
        assert rank is not None, (
            f"Rank should not be None after calculation for world {world}"
        )
        return rank

    def _rank_world_index(self, index: int, force_calculation: bool = False) -> int:
        rank = self._get_rank_value_by_index(index)
        if force_calculation or rank is None:
            rank = self.z_part2ocf_index(index)
            self._set_rank_value_by_index(index, rank)
        assert rank is not None, (
            f"Rank should not be None after calculation for world index {index}"
        )
        return rank

    def z_part2ocf(self, world: str) -> int:
        signature_symbols = self.symbolize_bitvec(world)
        solver = Solver(name="z3")
        [solver.add_assertion(s) for s in signature_symbols]
        return self._rec_z_rank(solver, len(self._z_partition) - 1)

    def z_part2ocf_index(self, index: int) -> int:
        solver = Solver(name="z3")
        self.add_world_index_assertions(solver, index)
        return self._rec_z_rank(solver, len(self._z_partition) - 1)

    def _rec_z_rank(self, solver: Solver, partition_index: int) -> int:
        part = self._z_partition[partition_index]
        [solver.add_assertion(Not(c.make_A_then_not_B())) for c in part]
        if solver.solve():
            if partition_index == 0:
                return 0
            return self._rec_z_rank(solver, partition_index - 1)
        return partition_index + 1

    # ------------------------------------------------------------------
    # Symbolic System Z helpers
    # ------------------------------------------------------------------
    def falsification_formula(self, conditional: Conditional) -> FNode:
        """Return the falsification formula ``A ∧ ¬B`` for ``(B|A)``."""

        return conditional.make_A_then_not_B()

    def layer_falsification_formula(self, partition_index: int) -> FNode:
        """Return a formula that is true iff the given layer is falsified."""

        layer = self._z_partition[partition_index]
        if not layer:
            return FALSE()
        return Or(*(self.falsification_formula(c) for c in layer))

    def higher_layers_clear_formula(self, partition_index: int) -> FNode:
        """Return a formula ensuring no higher partition layer is falsified."""

        constraints = [
            Not(self.falsification_formula(c))
            for layer in self._z_partition[partition_index + 1 :]
            for c in layer
        ]
        if not constraints:
            return TRUE()
        return And(*constraints)

    def rank_bucket_formula(self, rank: int) -> FNode:
        """Return a symbolic formula characterizing one System Z rank bucket."""

        max_rank = len(self._z_partition)
        if rank < 0 or rank > max_rank:
            raise ValueError(f"rank must be between 0 and {max_rank}, got {rank}")

        if rank == 0:
            constraints = [
                Not(self.falsification_formula(c))
                for layer in self._z_partition
                for c in layer
            ]
            if not constraints:
                return TRUE()
            return And(*constraints)

        partition_index = rank - 1
        return And(
            self.layer_falsification_formula(partition_index),
            self.higher_layers_clear_formula(partition_index),
        )

    def symbolic_rank_buckets(self) -> list[SystemZSymbolicBucket]:
        """Return symbolic rank-bucket descriptors for all possible ranks."""

        buckets: list[SystemZSymbolicBucket] = [
            SystemZSymbolicBucket(
                rank=0,
                formula=self.rank_bucket_formula(0),
                partition_index=None,
                layer_size=0,
                is_infinity=False,
            )
        ]

        last_index = len(self._z_partition) - 1
        for partition_index, layer in enumerate(self._z_partition):
            buckets.append(
                SystemZSymbolicBucket(
                    rank=partition_index + 1,
                    formula=self.rank_bucket_formula(partition_index + 1),
                    partition_index=partition_index,
                    layer_size=len(layer),
                    is_infinity=(
                        self.uses_extended_partition and partition_index == last_index
                    ),
                )
            )
        return buckets

    @staticmethod
    def _model_value_as_bool(model, symbol: FNode) -> bool:
        """Extract a Python bool from a PySMT model entry."""

        if hasattr(model, "get_py_value"):
            value = model.get_py_value(symbol)
            if isinstance(value, bool):
                return value

        if hasattr(model, "get_value"):
            value = model.get_value(symbol)
        else:
            value = model[symbol]

        if hasattr(value, "is_true"):
            return bool(value.is_true())

        return str(value).lower() == "true"

    def enumerate_formula_worlds(
        self, formula: FNode, max_worlds: int | None = None
    ) -> list[str]:
        """Enumerate worlds satisfying ``formula`` using model blocking."""

        symbols = [Symbol(name, BOOL) for name in self.signature]
        worlds: list[str] = []

        with Solver(name="z3") as solver:
            solver.add_assertion(formula)
            while solver.solve():
                model = solver.get_model()
                bits: list[str] = []
                block_literals: list[FNode] = []

                for symbol in symbols:
                    value = self._model_value_as_bool(model, symbol)
                    bits.append("1" if value else "0")
                    block_literals.append(Not(symbol) if value else symbol)

                worlds.append("".join(bits))
                if max_worlds is not None and len(worlds) >= max_worlds:
                    break

                if not block_literals:
                    break
                solver.add_assertion(Or(*block_literals))

        return worlds

    def enumerate_rank_bucket_worlds(
        self, rank: int, max_worlds: int | None = None
    ) -> list[str]:
        """Enumerate worlds belonging to the given symbolic rank bucket."""

        return self.enumerate_formula_worlds(
            self.rank_bucket_formula(rank), max_worlds=max_worlds
        )

    def materialize_ranks_from_buckets(
        self, overwrite: bool = False
    ) -> dict[str, None | int]:
        """Fill ``self.ranks`` by enumerating symbolic rank buckets."""

        assigned_worlds: set[str] = set()

        for bucket in self.symbolic_rank_buckets():
            for world in self.enumerate_formula_worlds(bucket.formula):
                if world in assigned_worlds and not overwrite:
                    raise ValueError(
                        f"world {world} was assigned by multiple symbolic buckets"
                    )
                self._set_rank_value(world, bucket.rank)
                assigned_worlds.add(world)

        missing_worlds = [
            world for world in self.iter_worlds() if self._get_rank_value(world) is None
        ]
        if missing_worlds:
            raise ValueError(
                "symbolic rank materialization left worlds unassigned: "
                f"{missing_worlds[:5]}"
            )

        return self.ranks

    # ------------------------------------------------------------------
    # Public accessors for partition metadata
    # ------------------------------------------------------------------
    @property
    def uses_extended_partition(self) -> bool:
        """True if the System Z partition was computed with weakly=True (extended)."""
        return bool(self._state.get("z_partition_extended", False))

    @property
    def z_partition_stats(self) -> dict[str, int] | None:
        """Return stats about the partitioning process (layers, calls, levels) if available."""
        return self._state.get("z_partition_stats", None)  # type: ignore[return-value]

    @property
    def has_infinity_partition(self) -> bool:
        """True if an infinity (last) partition exists (i.e., extended System Z)."""
        return self.uses_extended_partition

    @property
    def infinity_partition_index(self) -> int | None:
        """Index of the infinity partition if present, otherwise None."""
        if not self.has_infinity_partition:
            return None
        return len(self._z_partition) - 1

    @property
    def infinity_partition(self) -> list[Conditional] | None:
        """Return the infinity partition (possibly empty) when extended is used; otherwise None."""
        idx = self.infinity_partition_index
        if idx is None:
            return None
        result: list[Conditional] = self._z_partition[idx]
        return result

    # ------------------------------------------------------------------
    # Convenience formatting & diagnostics helpers
    # ------------------------------------------------------------------
    @property
    def diagnostics(self) -> dict[str, object] | None:
        """Return stored consistency diagnostics if available."""
        result = self.load_meta("consistency_diagnostics")
        if result is None or isinstance(result, dict):
            return result  # type: ignore[return-value]
        return None

    def partition_layer_sizes(self) -> list[int]:
        """Return the size of each partition layer (ascending by index)."""
        return [len(layer) for layer in self._z_partition]

    def format_partition_layers(self, short: bool = True) -> str:
        """Return a compact string for layers, marking the last as (∞) if extended.

        Example: "layers=[3,2,1(∞)]"
        """
        sizes = self.partition_layer_sizes()
        if not sizes:
            return "layers=[]"
        if self.uses_extended_partition and len(sizes) >= 1:
            items = [str(s) for s in sizes[:-1]] + [f"{sizes[-1]}(∞)"]
        else:
            items = [str(s) for s in sizes]
        return f"layers=[{','.join(items)}]"

    def format_diagnostics_line(self) -> str:
        """Return a single-line diagnostics summary (verbose keys), or 'diag: none' if absent."""
        diag = self.diagnostics
        if isinstance(diag, dict):
            # Cast to Diagnostics for type checker
            diag_typed: Diagnostics = diag  # type: ignore[assignment]
            return f"diag: {format_diagnostics_verbose(diag_typed)}"
        return "diag: none"

    def summary(self, brief: bool = True, include_facts: bool = True) -> str:
        """Return a compact one-line summary of this System Z PreOCF instance."""
        sig = ",".join(self.signature)
        ext = self.uses_extended_partition
        layers_str = self.format_partition_layers(short=True)
        # Facts info
        facts_part = ""
        if include_facts:
            if self._state.get("z_facts_present", False):
                cnt = self.load_meta("input_facts_count", None)
                facts_display = f"facts={cnt}" if isinstance(cnt, int) else "facts=yes"
            else:
                facts_display = "facts=None"
            facts_part = f"; {facts_display}"
        return (
            f"SystemZ(sig={sig}; extended={ext}{facts_part}; {layers_str}; "
            f"{self.format_diagnostics_line()})"
        )

    def format_layers_with_conditionals(self) -> str:
        """Return a multi-line string listing conditionals per partition layer.

        Example lines:
          Layer 0: (b|a), (!b|a)
          Layer 1(∞): (Bottom|!a)
        """
        part = self._z_partition
        if not isinstance(part, list):
            return "(no partition)"
        is_ext = self.uses_extended_partition
        last_idx = len(part) - 1
        lines: list[str] = []
        for i, layer in enumerate(part):
            label = " (∞)" if is_ext and i == last_idx else ""
            cond_str = ", ".join(str(c) for c in layer)
            lines.append(f"  Layer {i}{label}: {cond_str}")
        return "\n".join(lines)


class RandomMinCRepPreOCF(PreOCF):
    """Ranking via Pareto-minimized impact vector over conditionals.

    The constructor solves for an impact vector using Z3 Optimize. A world's
    rank is the sum of impacts for violated conditionals. Utility methods are
    provided to save/load impacts and to construct instances from precomputed
    impact vectors.
    """

    def __init__(
        self,
        belief_base: BeliefBase,
        signature: list | None = None,
        metadata: dict[str, object] | None = None,
    ):
        if signature is None:
            signature = belief_base.signature
        conditionals = belief_base.conditionals
        super().__init__(None, signature, conditionals, "random_min_c_rep", metadata)
        # RandomMinCRepPreOCF always needs conditionals
        assert self.conditionals is not None, (
            "RandomMinCRepPreOCF requires non-None conditionals"
        )

        # Lazy import to keep the preocf ←→ extended_c_rep graph acyclic.
        from inference.consistency_sat import consistency  # noqa: PLC0415
        from inference.extended_c_rep import (  # noqa: PLC0415
            INFINITY,
            compute_j_delta,
        )
        from inference.tseitin_transformation import (  # noqa: PLC0415
            TseitinTransformation,
        )

        z_partition, _ = consistency(belief_base, solver="z3", weakly=True)
        if z_partition is False:
            raise ValueError(
                "belief_base is not weakly consistent: "
                "no extended c-representation exists"
            )
        j_delta, infinity_set, _reasons = compute_j_delta(belief_base, z_partition)

        # Persist the partition information on the instance so downstream
        # consumers (serialisers, UI renderers, CSV exporters) can report
        # *why* each ∞-impact appeared without re-running the SAT checks.
        self.save_meta("infinity_indices", sorted(infinity_set))
        self.save_meta("infinity_reasons", dict(_reasons))
        self.save_meta("j_delta", sorted(j_delta))

        all_indices = sorted(self.conditionals.keys())
        active_indices_sorted = sorted(j_delta)

        # Edge case: every conditional is strict or triggered
        # (Proposition 23 of KER 2024).  The only extended c-rep is
        # η = (∞, …, ∞); no CSP is needed.
        if not active_indices_sorted:
            self._csp = []
            self._optimizer = None
            self._impacts = [INFINITY for _ in all_indices]
            return

        epistemic_state = create_epistemic_state(
            belief_base,
            inference_system="c-inference",
            smt_solver="z3",
            pmaxsat_solver="rc2",
            weakly=True,
        )
        c_inf = CInference(epistemic_state)
        TseitinTransformation(epistemic_state).belief_base_to_cnf(True, True, True)
        c_inf.compile_constraint(
            deadline=None,
            active_indices=j_delta,
            infinity_indices=infinity_set,
        )
        base_csp = c_inf.translate(active_indices=j_delta)

        pysmt_solver = Solver(name="z3")
        self._csp = [pysmt_solver.converter.convert(expr) for expr in base_csp]
        self._optimizer = Optimize()
        self._optimizer.set(priority="pareto")
        self._optimizer.add(*self._csp)
        for i in active_indices_sorted:
            self._optimizer.minimize(z3.Int(f"eta_{i}"))

        if self._optimizer.check() != sat:
            raise ValueError("no solution found for random min c rep")

        m = self._optimizer.model()
        finite_by_idx = {
            i: int(str(m.eval(z3.Int(f"eta_{i}")))) for i in active_indices_sorted
        }
        self._impacts = [
            INFINITY if i in infinity_set else finite_by_idx[i] for i in all_indices
        ]

    def rank_world(self, world: str, force_calculation: bool = False) -> int | float:
        rank = self._get_rank_value(world)
        if force_calculation or rank is None:
            rank = self.c_vec2ocf(world)
            self._set_rank_value(world, rank)
        assert rank is not None, (
            f"Rank should not be None after calculation for world {world}"
        )
        return rank

    def _rank_world_index(
        self, index: int, force_calculation: bool = False
    ) -> int | float:
        rank = self._get_rank_value_by_index(index)
        if force_calculation or rank is None:
            rank = self.c_vec2ocf(self.index_to_world(index))
            self._set_rank_value_by_index(index, rank)
        assert rank is not None, (
            f"Rank should not be None after calculation for world index {index}"
        )
        return rank

    def c_vec2ocf(self, world: str) -> int | float:
        """Compute ``κ_η(ω) = Σ_{ω ⊨ A_i ¬B_i} η_i`` (Def. 20 / Def. 6).

        Returns ``INFINITY`` (``math.inf``) as soon as any falsified
        conditional has ``η_i = ∞``: this is the extended
        c-representation semantics for infeasible worlds
        (Prop. 4 / 26).  For classical (all-finite) impact vectors the
        behaviour is identical to before.
        """
        from inference.extended_c_rep import INFINITY  # noqa: PLC0415

        assert self.conditionals is not None, "conditionals required for c_vec2ocf"
        rank: int | float = 0
        world_symbols = self.symbolize_bitvec(world)
        for idx, cond in self.conditionals.items():
            solver = Solver(name="z3")
            for sym in world_symbols:
                solver.add_assertion(sym)
            solver.add_assertion(cond.make_A_then_not_B())
            if solver.solve():
                impact = self._impacts[idx - 1]
                if impact == INFINITY:
                    return INFINITY
                rank += impact
        return rank

    # ------------------------------------------------------------------
    # Impact vector persistence methods
    # ------------------------------------------------------------------
    def export_impacts(self, path: str | pathlib.Path, fmt: str = "json") -> None:
        """Export the computed impact vector to a file for later reuse."""
        if not hasattr(self, "_impacts") or self._impacts is None:
            raise ValueError(
                "No impacts computed yet. Run the constructor or compute impacts first."
            )

        assert self.conditionals is not None, "conditionals required for save_impacts"
        path = pathlib.Path(path)
        impact_data = {
            "impacts": self._impacts,
            "conditionals_count": len(self.conditionals),
            "ranking_system": self.ranking_system,
            "signature": self.signature,
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

        assert self.conditionals is not None, "conditionals required for load_impacts"
        required_keys = ["impacts", "conditionals_count", "ranking_system", "signature"]
        for key in required_keys:
            if key not in impact_data:
                raise ValueError(f"Impact file missing required key: {key}")

        # Validate compatibility
        if impact_data["conditionals_count"] != len(self.conditionals):
            raise ValueError(
                f"Impact vector size mismatch: file has {impact_data['conditionals_count']}, "
                f"current PreOCF has {len(self.conditionals)} conditionals"
            )

        if impact_data["ranking_system"] != self.ranking_system:
            warnings.warn(
                f"Ranking system mismatch: file has '{impact_data['ranking_system']}', "
                f"current PreOCF has '{self.ranking_system}'",
                RuntimeWarning,
            )

        if impact_data["signature"] != self.signature:
            warnings.warn(
                f"Signature mismatch: file has {impact_data['signature']}, "
                f"current PreOCF has {self.signature}",
                RuntimeWarning,
            )

        # Import the impacts
        self._impacts = impact_data["impacts"]

        # Store import metadata
        self.save_meta("impacts_imported_from", str(path))
        import time

        self.save_meta("impacts_import_timestamp", time.time())

    @classmethod
    def init_with_impacts(
        cls,
        belief_base: BeliefBase,
        impacts_path: str | pathlib.Path,
        signature: list | None = None,
        metadata: dict[str, object] | None = None,
    ) -> "RandomMinCRepPreOCF":
        """Create a RandomMinCRepPreOCF instance using pre-computed impacts from a file."""
        # Create instance without computing impacts (we'll override them)
        instance = cls.__new__(cls)

        # Initialize parent class attributes
        if signature is None:
            signature = belief_base.signature
        conditionals = belief_base.conditionals
        PreOCF.__init__(
            instance, None, signature, conditionals, "random_min_c_rep", metadata
        )

        # Set placeholders for attributes that would normally be computed
        instance._csp = None
        instance._optimizer = None

        # Import the impacts
        instance.import_impacts(impacts_path)

        return instance

    # ------------------------------------------------------------------
    # Simple impact vector load/save methods (Python lists)
    # ------------------------------------------------------------------
    def save_impacts(self) -> list[int | float]:
        """Return the current impact vector as a Python list for easy storage/transfer.

        Entries may be ``INFINITY`` (``math.inf``) in the extended
        c-representation setting.
        """
        if not hasattr(self, "_impacts") or self._impacts is None:
            raise ValueError(
                "No impacts computed yet. Run the constructor or compute impacts first."
            )
        return self._impacts.copy()

    def load_impacts(self, impacts: list[int | float]) -> None:
        """Load impact vector from a Python list with basic validation.

        Accepts non-negative integers and the ``INFINITY`` sentinel
        (``math.inf``) for strict / triggered conditionals in the
        extended c-representation.
        """
        from inference.extended_c_rep import INFINITY  # noqa: PLC0415

        assert self.conditionals is not None, "conditionals required for import_impacts"
        if not isinstance(impacts, list):
            raise TypeError("Impacts must be a list of integers or INFINITY")

        def _is_valid(x: object) -> bool:
            if isinstance(x, bool):  # bool is a subclass of int; reject it.
                return False
            if isinstance(x, int):
                return True
            if isinstance(x, float) and x == INFINITY:
                return True
            return False

        if not all(_is_valid(x) for x in impacts):
            raise TypeError("All impact values must be integers or INFINITY (math.inf)")

        if len(impacts) != len(self.conditionals):
            raise ValueError(
                f"Impact vector size mismatch: provided {len(impacts)}, "
                f"expected {len(self.conditionals)} (number of conditionals)"
            )

        # Negative finite impacts are disallowed; INFINITY is fine.
        if any((isinstance(x, int) and x < 0) for x in impacts):
            raise ValueError("Finite impact values must be non-negative")

        self._impacts = list(impacts)

        # Store load metadata
        self.save_meta("impacts_loaded_from_list", True)
        import time

        self.save_meta("impacts_load_timestamp", time.time())

    @classmethod
    def init_with_impacts_list(
        cls,
        belief_base: BeliefBase,
        impacts: list[int | float],
        signature: list | None = None,
        metadata: dict[str, object] | None = None,
    ) -> "RandomMinCRepPreOCF":
        """Create a RandomMinCRepPreOCF instance using a pre-computed impact vector list.

        Accepts ``INFINITY`` entries for strict / triggered
        conditionals in the extended c-representation setting.
        """
        # Create instance without computing impacts (we'll override them)
        instance = cls.__new__(cls)

        # Initialize parent class attributes
        if signature is None:
            signature = belief_base.signature
        conditionals = belief_base.conditionals
        PreOCF.__init__(
            instance, None, signature, conditionals, "random_min_c_rep", metadata
        )

        # Set placeholders for attributes that would normally be computed
        instance._csp = None
        instance._optimizer = None

        # Load the impacts
        instance.load_impacts(impacts)

        return instance


class CustomPreOCF(PreOCF):
    """PreOCF with user-provided ranks.

    Notes
    -----
    ``rank_world`` raises a ``ValueError`` if a world is missing from
    the provided ``ranks`` mapping.
    """

    def __init__(
        self,
        ranks: dict[str, None | int],
        belief_base: BeliefBase | None = None,
        signature: list | None = None,
        metadata: dict[str, object] | None = None,
    ):
        super().__init__(
            ranks,
            signature or (belief_base.signature if belief_base else None),
            belief_base.conditionals if belief_base else None,
            "custom",
            metadata,
        )

    def rank_world(self, world: str, force_calculation: bool = False) -> int:
        rank = self.ranks.get(world)
        if rank is None:
            raise ValueError(f"provide custom ranking function for world: {world}")
        return rank


def create_preocf(ranking_system: str, *args, **kwargs) -> PreOCF:  # type: ignore[no-untyped-def]
    """Factory for PreOCF subclasses.

    Parameters
    ----------
    ranking_system : {"system-z", "random_min_c_rep", "custom"}
        Selects the concrete implementation.

    Returns
    -------
    PreOCF
        Instance of the requested ranking system.

    Raises
    ------
    ValueError
        If ``ranking_system`` is unknown.
    """
    if ranking_system == "system-z":
        return SystemZPreOCF(*args, **kwargs)
    elif ranking_system == "random_min_c_rep":
        return RandomMinCRepPreOCF(*args, **kwargs)
    elif ranking_system == "custom":
        return CustomPreOCF(*args, **kwargs)
    else:
        raise ValueError(f"Unknown ranking system: {ranking_system}")
