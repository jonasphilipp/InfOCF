"""weak system w and lex inf backend diagnostics."""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from itertools import product
from pathlib import Path
from typing import Any

from pysmt.shortcuts import Bool, simplify

from inference.belief_base import BeliefBase
from inference.inference_manager import InferenceManager, create_inference_instance
from inference.queries import Queries

World = dict[str, bool]


def _worlds(signature: list[str]) -> list[World]:
    return [
        dict(zip(signature, values, strict=False))
        for values in product((False, True), repeat=len(signature))
    ]


def _holds(formula: Any, world: World) -> bool:
    values = {
        symbol: Bool(world[symbol.symbol_name()])
        for symbol in formula.get_free_variables()
    }
    return simplify(formula.substitute(values)).is_true()


class FiniteWorldOracle:
    """small solver-independent reference for system w and lex inf."""

    def __init__(self, belief_base: BeliefBase) -> None:
        if len(belief_base.signature) > 8:
            raise ValueError("finite-world oracle supports at most 8 atoms")
        self.belief_base = belief_base
        self.worlds = _worlds(belief_base.signature)
        self.partition = self._partition()
        self.trace: list[dict[str, Any]] = []

    def _nf_holds(self, index: int, world: World) -> bool:
        return _holds(self.belief_base.conditionals[index].make_not_A_or_B(), world)

    def _f_holds(self, index: int, world: World) -> bool:
        return _holds(self.belief_base.conditionals[index].make_A_then_not_B(), world)

    def _partition(self) -> list[list[int]]:
        remaining = list(self.belief_base.conditionals)
        result: list[list[int]] = []
        while remaining:
            tolerated = [
                index
                for index in remaining
                if any(
                    all(self._nf_holds(other, world) for other in remaining)
                    and _holds(
                        self.belief_base.conditionals[index].make_A_then_B(), world
                    )
                    for world in self.worlds
                )
            ]
            if not tolerated:
                # remaining consistent rules form the final weak layer.
                if not any(
                    all(self._nf_holds(index, world) for index in remaining)
                    for world in self.worlds
                ):
                    raise ValueError("belief base is not weakly consistent")
                result.append(remaining)
                return result
            result.append(tolerated)
            remaining = [index for index in remaining if index not in tolerated]
        result.append([])
        return result

    def _mcs(self, worlds: list[World], part: list[int]) -> list[frozenset[int]]:
        candidates = {
            frozenset(index for index in part if self._f_holds(index, world))
            for world in worlds
        }
        return sorted(
            (
                candidate
                for candidate in candidates
                if not any(other < candidate for other in candidates)
            ),
            key=lambda value: (len(value), tuple(sorted(value))),
        )

    @staticmethod
    def _subset_of_all(left: list[frozenset[int]], right: list[frozenset[int]]) -> bool:
        return all(
            any(candidate.issubset(target) for candidate in left) for target in right
        )

    def _system_w(self, worlds: list[World], query: Any, level: int) -> bool:
        part = self.partition[level]
        verified = self._mcs(
            [world for world in worlds if _holds(query.make_A_then_B(), world)], part
        )
        falsified = self._mcs(
            [world for world in worlds if _holds(query.make_A_then_not_B(), world)],
            part,
        )
        self.trace.append(
            {
                "level": level,
                "verification_mcs": [sorted(v) for v in verified],
                "falsification_mcs": [sorted(v) for v in falsified],
            }
        )
        if not self._subset_of_all(verified, falsified):
            return False
        for correction in set(verified) & set(falsified):
            if level == 0:
                return False
            next_worlds = [
                world
                for world in worlds
                if all(self._f_holds(index, world) for index in correction)
                and all(
                    self._nf_holds(index, world) for index in set(part) - correction
                )
            ]
            if not self._system_w(next_worlds, query, level - 1):
                return False
        return True

    def _lex_inf(
        self, worlds_v: list[World], worlds_f: list[World], query: Any, level: int
    ) -> bool:
        part = self.partition[level]
        mcs_v = self._mcs(
            [world for world in worlds_v if _holds(query.make_A_then_B(), world)], part
        )
        mcs_f = self._mcs(
            [world for world in worlds_f if _holds(query.make_A_then_not_B(), world)],
            part,
        )
        self.trace.append(
            {
                "level": level,
                "verification_mcs": [sorted(v) for v in mcs_v],
                "falsification_mcs": [sorted(v) for v in mcs_f],
            }
        )
        if not mcs_v:
            return False
        if not mcs_f:
            return True
        size_v = len(mcs_v[0])
        size_f = len(mcs_f[0])
        if size_v < size_f:
            return True
        if size_f < size_v:
            return False
        for correction_v in (item for item in mcs_v if len(item) == size_v):
            for correction_f in (item for item in mcs_f if len(item) == size_f):
                if level == 0:
                    return False
                next_v = [
                    world
                    for world in worlds_v
                    if all(self._f_holds(index, world) for index in correction_v)
                    and all(
                        self._nf_holds(index, world)
                        for index in set(part) - correction_v
                    )
                ]
                next_f = [
                    world
                    for world in worlds_f
                    if all(self._f_holds(index, world) for index in correction_f)
                    and all(
                        self._nf_holds(index, world)
                        for index in set(part) - correction_f
                    )
                ]
                if not self._lex_inf(next_v, next_f, query, level - 1):
                    return False
        return True

    def infer(self, query: Any, operator: str) -> bool:
        """Evaluate a non-direct query under weak System W or LexInf semantics."""
        self.trace = []
        base_worlds = self.worlds
        for index in self.partition[-1]:
            base_worlds = [
                world for world in base_worlds if self._nf_holds(index, world)
            ]
        # the final weak layer is hard knowledge.
        if not any(_holds(query.antecedence, world) for world in base_worlds):
            result = True
        elif not any(_holds(query.make_A_then_not_B(), world) for world in base_worlds):
            result = True
        elif len(self.partition) == 1:
            result = False
        elif operator == "system-w":
            result = self._system_w(base_worlds, query, len(self.partition) - 2)
        elif operator == "lex_inf":
            result = self._lex_inf(
                base_worlds, base_worlds, query, len(self.partition) - 2
            )
        else:
            raise ValueError(f"unsupported operator: {operator}")
        for record in self.trace:
            record.update(
                {"backend": "oracle", "operator": operator, "query": str(query)}
            )
        return result


@dataclass(frozen=True)
class BackendRun:
    backend: str
    results: dict[int, bool]
    partition: list[list[int]]
    trace: list[dict[str, Any]]


@dataclass(frozen=True)
class BackendComparison:
    operator: str
    belief_base: str
    queries: dict[int, str]
    rc2: BackendRun
    z3: BackendRun

    @property
    def agrees(self) -> bool:
        return self.rc2.results == self.z3.results

    def save(self, directory: str | Path, *, seed: int | None = None) -> Path:
        """save a self-contained disagreement artifact."""
        destination = Path(directory)
        destination.mkdir(parents=True, exist_ok=True)
        stem = f"{self.operator}-seed-{seed}" if seed is not None else self.operator
        path = destination / f"{stem}.json"
        payload: dict[str, Any] = asdict(self)
        payload["agrees"] = self.agrees
        payload["seed"] = seed
        path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        return path


def normalize_mcs_trace(trace: list[dict[str, Any]]) -> list[tuple[Any, ...]]:
    """normalize mcs records for order-independent comparison."""

    def mcs_sets(record: dict[str, Any], field: str) -> tuple[tuple[int, ...], ...]:
        return tuple(sorted(tuple(sorted(mcs)) for mcs in record[field]))

    return sorted(
        (
            record["operator"],
            record["query"],
            record["level"],
            mcs_sets(record, "verification_mcs"),
            mcs_sets(record, "falsification_mcs"),
        )
        for record in trace
    )


def _normalize_partition(instance: Any, belief_base: BeliefBase) -> list[list[int]]:
    """Return partition layers as original belief-base indices for both backends."""
    partition = instance.epistemic_state["partition"]
    if not partition or not partition[0] or isinstance(partition[0][0], int):
        return [list(layer) for layer in partition]

    available: dict[str, list[int]] = {}
    for index, conditional in belief_base.conditionals.items():
        available.setdefault(str(conditional), []).append(index)
    return [
        [available[str(conditional)].pop(0) for conditional in layer]
        for layer in partition
    ]


def compare_weak_backends(
    belief_base: BeliefBase,
    queries: Queries,
    operator: str,
    *,
    bypass_direct_inference: bool = True,
    artifact_directory: str | Path | None = None,
    seed: int | None = None,
) -> BackendComparison:
    """Compare RC2 and Z3 for one weakly-consistent inference workload."""
    runs: dict[str, BackendRun] = {}
    for backend in ("rc2", "z3"):
        manager = InferenceManager(
            belief_base, operator, smt_solver="z3", pmaxsat_solver=backend, weakly=True
        )
        instance = create_inference_instance(manager.epistemic_state)
        instance.epistemic_state["bypass_direct_inference"] = bypass_direct_inference
        instance.epistemic_state["diagnostic_trace"] = []
        instance.preprocess_belief_base(0)
        results: dict[int, bool] = {}
        for index, query in queries.conditionals.items():
            instance.epistemic_state["diagnostic_query"] = str(query)
            results[index] = instance.general_inference(query)
        runs[backend] = BackendRun(
            backend=backend,
            results=results,
            partition=_normalize_partition(instance, belief_base),
            trace=instance.epistemic_state["diagnostic_trace"],
        )

    comparison = BackendComparison(
        operator=operator,
        belief_base=(
            "signature\n"
            + ",".join(belief_base.signature)
            + "\n\nconditionals\n"
            + belief_base.name
            + "{\n"
            + ",\n".join(str(c) for c in belief_base.conditionals.values())
            + "\n}"
        ),
        queries={index: str(query) for index, query in queries.conditionals.items()},
        rc2=runs["rc2"],
        z3=runs["z3"],
    )
    if artifact_directory is not None and not comparison.agrees:
        comparison.save(artifact_directory, seed=seed)
    return comparison
