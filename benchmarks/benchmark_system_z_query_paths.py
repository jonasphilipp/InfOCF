from __future__ import annotations

from pathlib import Path
from statistics import mean
from time import perf_counter

from pysmt.fnode import FNode
from pysmt.shortcuts import And, Not, Or, Solver, Symbol
from pysmt.typing import BOOL

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from inference.preocf import PreOCF
from parser.Wrappers import parse_belief_base

REPO_ROOT = Path(__file__).resolve().parent.parent
BENCHMARK_CASES = [
    REPO_ROOT / "examples" / "birds" / "kb_birds001.cl",
    REPO_ROOT / "examples" / "random_large" / "randomTest_10_10_0.cl",
    REPO_ROOT / "examples" / "random_large" / "randomTest_12_12_50.cl",
]
REPEATS = 3


def load_belief_base(path: Path) -> BeliefBase:
    parsed = parse_belief_base(str(path))
    return BeliefBase(parsed.signature, parsed.conditionals, path.stem)


def build_probe_formulas(signature: list[str]) -> tuple[FNode, FNode, Conditional]:
    symbols = [Symbol(name, BOOL) for name in signature[:3]]
    if len(symbols) == 1:
        cond_formula = symbols[0]
        rank_formula = symbols[0]
        conditional = Conditional(
            symbols[0], symbols[0], f"({signature[0]}|{signature[0]})"
        )
        return cond_formula, rank_formula, conditional
    if len(symbols) == 2:
        cond_formula = And(symbols[0], Not(symbols[1]))
        rank_formula = Or(symbols[0], symbols[1])
        conditional = Conditional(
            symbols[1], symbols[0], f"({signature[1]}|{signature[0]})"
        )
        return cond_formula, rank_formula, conditional

    cond_formula = And(symbols[0], Not(symbols[1]))
    rank_formula = Or(symbols[0], symbols[1], symbols[2])
    antecedence = And(symbols[0], symbols[1])
    conditional = Conditional(
        symbols[2],
        antecedence,
        f"({signature[2]}|{signature[0]},{signature[1]})",
    )
    return cond_formula, rank_formula, conditional


def legacy_symbolize_bitvec(signature: list[str], bitvec: str) -> list[FNode]:
    return [
        Symbol(signature[i], BOOL)
        if int(bitvec[i])
        else Not(Symbol(signature[i], BOOL))
        for i in range(len(signature))
    ]


def legacy_world_satisfies_conditionalization(
    preocf: PreOCF, world: str, conditionalization: FNode
) -> bool:
    solver = Solver(name="z3")
    for symbol in legacy_symbolize_bitvec(preocf.signature, world):
        solver.add_assertion(symbol)
    solver.add_assertion(conditionalization)
    return bool(solver.solve())


def legacy_filter_worlds_by_conditionalization(
    preocf: PreOCF, conditionalization: FNode
) -> list[str]:
    return [
        world
        for world in preocf.iter_worlds()
        if legacy_world_satisfies_conditionalization(preocf, world, conditionalization)
    ]


def legacy_compute_conditionalization(
    preocf: PreOCF, conditionalization: FNode
) -> dict[str, int | None]:
    worlds = legacy_filter_worlds_by_conditionalization(preocf, conditionalization)
    return {world: preocf.rank_world(world) for world in worlds}


def legacy_formula_rank(preocf: PreOCF, formula: FNode) -> int | None:
    min_rank = None
    solver = Solver(name="z3")
    for world in preocf.iter_worlds():
        solver.push()
        for symbol in legacy_symbolize_bitvec(preocf.signature, world):
            solver.add_assertion(symbol)
        solver.add_assertion(formula)
        if solver.solve():
            rank = preocf.rank_world(world)
            if min_rank is None or rank < min_rank:
                min_rank = rank
        solver.pop()
    return min_rank


def legacy_conditional_acceptance(preocf: PreOCF, conditional: Conditional) -> bool:
    v_rank = legacy_formula_rank(preocf, conditional.make_A_then_B())
    n_rank = legacy_formula_rank(preocf, conditional.make_A_then_not_B())
    if v_rank is None:
        return False
    if n_rank is None:
        return True
    return v_rank < n_rank


def time_average(label: str, func, *args) -> tuple[float, object]:
    result = None
    timings_ms: list[float] = []
    for _ in range(REPEATS):
        start = perf_counter()
        result = func(*args)
        timings_ms.append((perf_counter() - start) * 1000.0)
    return mean(timings_ms), result


def benchmark_case(path: Path) -> None:
    belief_base = load_belief_base(path)
    preocf = PreOCF.init_system_z(belief_base)
    preocf.compute_all_ranks()

    cond_formula, rank_formula, conditional = build_probe_formulas(
        belief_base.signature
    )

    curr_filter_ms, curr_filter = time_average(
        "current filter", preocf.filter_worlds_by_conditionalization, cond_formula
    )
    legacy_filter_ms, legacy_filter = time_average(
        "legacy filter",
        legacy_filter_worlds_by_conditionalization,
        preocf,
        cond_formula,
    )
    assert curr_filter == legacy_filter

    curr_compute_ms, curr_compute = time_average(
        "current compute", preocf.compute_conditionalization, cond_formula
    )
    legacy_compute_ms, legacy_compute = time_average(
        "legacy compute", legacy_compute_conditionalization, preocf, cond_formula
    )
    assert curr_compute == legacy_compute

    curr_formula_ms, curr_formula = time_average(
        "current formula", preocf.formula_rank, rank_formula
    )
    legacy_formula_ms, legacy_formula = time_average(
        "legacy formula", legacy_formula_rank, preocf, rank_formula
    )
    assert curr_formula == legacy_formula

    curr_accept_ms, curr_accept = time_average(
        "current acceptance", preocf.conditional_acceptance, conditional
    )
    legacy_accept_ms, legacy_accept = time_average(
        "legacy acceptance", legacy_conditional_acceptance, preocf, conditional
    )
    assert curr_accept == legacy_accept

    print(f"=== Query benchmark: {path.name} ===")
    print(
        f"Signature size: {len(belief_base.signature)} vars -> {2 ** len(belief_base.signature)} worlds"
    )
    print(f"Conditionals: {len(belief_base.conditionals)}")
    print(
        f"filter_worlds current/legacy: {curr_filter_ms:.2f} / {legacy_filter_ms:.2f} ms"
    )
    print(
        f"compute_conditionalization current/legacy: {curr_compute_ms:.2f} / {legacy_compute_ms:.2f} ms"
    )
    print(
        f"formula_rank current/legacy: {curr_formula_ms:.2f} / {legacy_formula_ms:.2f} ms"
    )
    print(
        f"conditional_acceptance current/legacy: {curr_accept_ms:.2f} / {legacy_accept_ms:.2f} ms"
    )
    print(
        f"matching worlds: {len(curr_filter)} formula_rank={curr_formula} accepted={curr_accept}"
    )
    print()


def main() -> None:
    for path in BENCHMARK_CASES:
        benchmark_case(path)


if __name__ == "__main__":
    main()
