import argparse
import csv
import os
import random
import string
from pathlib import Path
from random import choice

import z3
from pysmt.shortcuts import Solver

from inference.belief_base import BeliefBase
from inference.consistency_sat import consistency
from parser.Wrappers import parseQuery

LEXINF_ECSQARU_COMBINATIONS = [
    (6, 6),
    (8, 8),
    (10, 10),
    (12, 12),
    (14, 14),
    (16, 16),
    (18, 18),
    (20, 20),
    (30, 30),
    (40, 40),
    (50, 50),
    (60, 60),
    (60, 80),
    (60, 100),
    (60, 120),
    (80, 60),
    (80, 80),
    (80, 120),
    (80, 160),
    (100, 60),
    (100, 100),
    (100, 160),
    (100, 200),
    (120, 60),
    (120, 80),
    (120, 120),
    (120, 160),
]

DEFAULT_OUTPUT_DIR = Path("benchmarks/generated/lexinf_ecsqaru2025")
DEFAULT_REPEATED_VARS_OUTPUT_DIR = Path(
    "benchmarks/generated/lexinf_natural_repeated_vars"
)
DEFAULT_TARGETED_LITERAL_BOTTOM_OUTPUT_DIR = Path(
    "benchmarks/generated/lexinf_targeted_literal_bottom"
)
DEFAULT_NATURAL_READ_ONCE_OUTPUT_DIR = Path(
    "benchmarks/generated/lexinf_natural_read_once"
)
DEFAULT_SAMPLES_PER_COMBINATION = 100
DEFAULT_QUERIES_PER_BELIEF_BASE = 10
DEFAULT_MAX_ATTEMPTS = 10000
MANIFEST_HEADER = [
    "dataset",
    "consistency",
    "signature_size",
    "conditionals",
    "index",
    "belief_base_path",
    "queries_path",
]
REPEATED_VARS_MANIFEST_HEADER = [
    "dataset",
    "consistency",
    "signature_size",
    "conditionals",
    "index",
    "combo_total_index",
    "attempts_for_entry",
    "partition_lengths",
    "consistency_calls",
    "consistency_levels",
    "formula_max_depth",
    "belief_base_path",
    "queries_path",
]


def sample_operation():
    """
    returns a random operations that works on a list of formulas
    whether the operation is appropriate to do on the list,
    i.e. the list has enough entries, has to be checked by the caller
    """

    def NotFormula(l):
        f = l.pop()
        l.insert(0, "(!%s)" % f)

    def AndFormula(l):
        f1 = l.pop()
        f2 = l.pop()
        l.insert(0, "(%s,%s)" % (f1, f2))

    def OrFormula(l):
        f1 = l.pop()
        f2 = l.pop()
        l.insert(0, "(%s;%s)" % (f1, f2))

    return choice([OrFormula, AndFormula, NotFormula])


def sampleVars(variables):
    """
    returns two disjoints subsets of variables, provided variable list is long enough, i.e. at least 4
    """
    assert len(variables) >= 4
    V = random.choice(range(4, 11))
    V = min(len(variables), V)
    random.shuffle(variables)
    variables = variables[:V]
    random.shuffle(variables)
    a = random.choice(
        range(1, V)
    )  ### does not include upper limit, so  atleast one variable is in antecedence and one in consequence
    return variables[:a], variables[a:]


def sampleFormula(variables):
    properties = variables
    while len(properties) > 1:
        op = sample_operation()
        op(properties)
        random.shuffle(properties)
    return properties[0]


def sampleConditional(variables):
    a, b = sampleVars(variables)
    return "(%s | %s)" % (sampleFormula(a), sampleFormula(b))


def sampleBottomConditional(variables):
    """Legacy targeted weak stress-test helper.

    This explicitly injects a literal-bottom conditional. It should not be used
    for canonical weak/strong random comparisons.
    """
    antecedent = random.choice(variables)
    if random.choice([True, False]):
        antecedent = "!" + antecedent
    return "(Bottom | %s)" % antecedent


def accepts_partition(partition, consistency_mode):
    if partition == False:
        return False
    if consistency_mode == "weak":
        return len(partition[-1]) > 0
    if consistency_mode == "strong":
        return len(partition[-1]) == 0
    if consistency_mode == "weak_or_strong":
        return True
    raise ValueError("consistency_mode must be 'weak', 'strong', or 'weak_or_strong'")


def classify_partition(partition):
    if partition == False:
        return "inconsistent"
    if len(partition[-1]) == 0:
        return "strong"
    return "weak"


def classify_belief_base(belief_base):
    partition, _ = consistency(belief_base, weakly=True)
    return classify_partition(partition)


def makeCKB(allVars, conditionals, queries, filename):
    name = os.path.basename(filename).split(".")[0]
    dirname = os.path.dirname(filename)
    if dirname:
        os.makedirs(dirname, exist_ok=True)
    with open(filename, "w+") as f:
        print("signature", file=f)
        print(*allVars, sep=",", file=f)
        print("\n", file=f)
        print("conditionals", file=f)
        print(name + " {", file=f)
        print(*conditionals, sep=",\n", file=f)
        print("}", file=f)


def makeQueryfile(conditionals, filename):
    dirname = os.path.dirname(filename)
    if dirname:
        os.makedirs(dirname, exist_ok=True)
    with open(filename, "w+") as f:
        print(*conditionals, sep=",\n", file=f)


def createVariables(amount):
    v = set()
    while len(v) < amount:
        nv = "".join([random.choice(string.ascii_lowercase) for i in range(6)])
        v.add(nv)
    return list(v)


def sampling(variables, amountConditionals, amountQueries, filename):
    conditionals = [sampleConditional(variables) for i in range(amountConditionals)]
    queries = [sampleConditional(variables) for i in range(amountQueries)]
    makeCKB(variables, conditionals, queries, filename)


def samplingConsistentCKB(
    S,
    R,
    consistency_mode="weak",
    inject_bottom=False,
    max_attempts=None,
    verbose=False,
):
    c = 0
    while True:
        c += 1
        if max_attempts is not None and c > max_attempts:
            raise RuntimeError(
                "failed to sample a %s belief base after %s attempts"
                % (consistency_mode, max_attempts)
            )
        if verbose:
            print(c)
        VAR = createVariables(S)
        conditionals = []
        if inject_bottom:
            if R < 1:
                raise ValueError("inject_bottom=True requires R >= 1")
            conditionals.append(sampleBottomConditional(VAR))
        conditionals.extend(
            sampleConditional(VAR) for _ in range(R - len(conditionals))
        )
        COND = [parseQuery(c)[1] for c in conditionals]
        dummyCKB = BeliefBase(
            [(v) for v in VAR], {i: c for i, c in enumerate(COND, start=1)}, ""
        )
        part, _ = consistency(dummyCKB, weakly=True)
        if accepts_partition(part, consistency_mode):
            if verbose:
                print(c)
                print("Conditionals per level:")
                print([len(l) for l in part])
            break
    return VAR, COND, dummyCKB


def is_nontrivial_query(query):
    with Solver(name="z3") as solver:
        solver.add_assertion(query.make_A_then_B())
        verifies = solver.solve()

    with Solver(name="z3") as solver:
        solver.add_assertion(query.make_A_then_not_B())
        falsifies = solver.solve()

    return verifies and falsifies


def sampleQueries(
    variables,
    amount,
    existing_conditionals=None,
    max_attempts=DEFAULT_MAX_ATTEMPTS,
):
    existing = {c.textRepresentation for c in existing_conditionals or []}
    seen = set(existing)
    queries = []
    attempts = 0

    while len(queries) < amount:
        attempts += 1
        if max_attempts is not None and attempts > max_attempts:
            raise RuntimeError(
                "failed to sample %s non-trivial queries after %s attempts"
                % (amount, max_attempts)
            )

        query = parseQuery(sampleConditional(variables))[1]
        text = query.textRepresentation
        if text in seen:
            continue
        if not is_nontrivial_query(query):
            continue

        seen.add(text)
        queries.append(query)

    return queries


def sample_formula_repeated_vars(
    variables,
    max_depth=4,
    leaf_probability=0.35,
    negation_probability=0.25,
):
    if max_depth <= 0 or random.random() < leaf_probability:
        atom = random.choice(variables)
        if random.random() < negation_probability:
            return f"(!{atom})"
        return atom

    operation = random.choice(["and", "or", "not"])
    if operation == "not":
        inner = sample_formula_repeated_vars(
            variables,
            max_depth=max_depth - 1,
            leaf_probability=leaf_probability,
            negation_probability=negation_probability,
        )
        return f"(!{inner})"

    left = sample_formula_repeated_vars(
        variables,
        max_depth=max_depth - 1,
        leaf_probability=leaf_probability,
        negation_probability=negation_probability,
    )
    right = sample_formula_repeated_vars(
        variables,
        max_depth=max_depth - 1,
        leaf_probability=leaf_probability,
        negation_probability=negation_probability,
    )
    if operation == "and":
        return f"({left},{right})"
    return f"({left};{right})"


def sample_conditional_repeated_vars(
    variables,
    max_depth=4,
    leaf_probability=0.35,
    negation_probability=0.25,
):
    antecedent = sample_formula_repeated_vars(
        variables,
        max_depth=max_depth,
        leaf_probability=leaf_probability,
        negation_probability=negation_probability,
    )
    consequent = sample_formula_repeated_vars(
        variables,
        max_depth=max_depth,
        leaf_probability=leaf_probability,
        negation_probability=negation_probability,
    )
    return f"({consequent} | {antecedent})"


def sample_conditionals_repeated_vars(
    signature_size,
    conditionals_count,
    formula_max_depth=4,
    leaf_probability=0.35,
    negation_probability=0.25,
):
    variables = createVariables(signature_size)
    conditional_texts = [
        sample_conditional_repeated_vars(
            variables,
            max_depth=formula_max_depth,
            leaf_probability=leaf_probability,
            negation_probability=negation_probability,
        )
        for _ in range(conditionals_count)
    ]
    conditionals = [parseQuery(text)[1] for text in conditional_texts]
    return variables, conditionals


def classify_conditionals(variables, conditionals):
    belief_base = BeliefBase(
        variables,
        {i: conditional for i, conditional in enumerate(conditionals, start=1)},
        "",
    )
    partition, stats = consistency(belief_base, weakly=True)
    if partition is False:
        return "inconsistent", stats
    if len(partition[-1]) == 0:
        return "strong", stats
    return "weak", stats


def sample_queries_repeated_vars(
    variables,
    amount,
    existing_conditionals=None,
    formula_max_depth=4,
    leaf_probability=0.35,
    negation_probability=0.25,
    max_attempts=DEFAULT_MAX_ATTEMPTS,
):
    existing = {c.textRepresentation for c in existing_conditionals or []}
    seen = set(existing)
    queries = []
    attempts = 0

    while len(queries) < amount:
        attempts += 1
        if max_attempts is not None and attempts > max_attempts:
            raise RuntimeError(
                "failed to sample %s non-trivial repeated-vars queries after %s attempts"
                % (amount, max_attempts)
            )

        query = parseQuery(
            sample_conditional_repeated_vars(
                variables,
                max_depth=formula_max_depth,
                leaf_probability=leaf_probability,
                negation_probability=negation_probability,
            )
        )[1]
        text = query.textRepresentation
        if text in seen:
            continue
        if not is_nontrivial_query(query):
            continue

        seen.add(text)
        queries.append(query)

    return queries


def read_manifest(manifest_path, natural_dataset_names=("natural",)):
    completed = set()
    natural_counts = {}
    natural_totals = {}

    if not manifest_path.exists():
        return completed, natural_counts, natural_totals

    with manifest_path.open(newline="") as manifest:
        reader = csv.DictReader(manifest)
        for row in reader:
            try:
                dataset = row["dataset"]
                consistency_mode = row["consistency"]
                signature_size = int(row["signature_size"])
                conditionals_count = int(row["conditionals"])
                index = int(row["index"])
            except (KeyError, TypeError, ValueError):
                continue

            completed.add(
                (
                    dataset,
                    consistency_mode,
                    signature_size,
                    conditionals_count,
                    index,
                )
            )

            if dataset in natural_dataset_names:
                natural_key = (signature_size, conditionals_count, consistency_mode)
                natural_counts[natural_key] = max(
                    natural_counts.get(natural_key, 0), index + 1
                )
                total_key = (signature_size, conditionals_count)
                natural_totals[total_key] = natural_totals.get(total_key, 0) + 1

    return completed, natural_counts, natural_totals


def read_repeated_vars_manifest(manifest_path):
    completed = set()
    totals = {}
    consistency_counts = {}

    if not manifest_path.exists():
        return completed, totals, consistency_counts

    with manifest_path.open(newline="") as manifest:
        reader = csv.DictReader(manifest)
        for row in reader:
            try:
                consistency_mode = row["consistency"]
                signature_size = int(row["signature_size"])
                conditionals_count = int(row["conditionals"])
                index = int(row["index"])
                combo_total_index = int(row["combo_total_index"])
            except (KeyError, TypeError, ValueError):
                continue

            completed.add(
                (
                    consistency_mode,
                    signature_size,
                    conditionals_count,
                    index,
                )
            )
            total_key = (signature_size, conditionals_count)
            totals[total_key] = max(totals.get(total_key, 0), combo_total_index + 1)

            consistency_key = (signature_size, conditionals_count, consistency_mode)
            consistency_counts[consistency_key] = max(
                consistency_counts.get(consistency_key, 0), index + 1
            )

    return completed, totals, consistency_counts


def generate_belief_base_sets(
    combinations=LEXINF_ECSQARU_COMBINATIONS,
    samples_per_combination=DEFAULT_SAMPLES_PER_COMBINATION,
    queries_per_belief_base=DEFAULT_QUERIES_PER_BELIEF_BASE,
    output_dir=DEFAULT_OUTPUT_DIR,
    max_attempts=DEFAULT_MAX_ATTEMPTS,
    include_targeted=True,
    include_natural=True,
    targeted_dataset_name="targeted",
    targeted_dir_name="targeted",
    natural_dataset_name="natural",
    natural_dir_name="natural",
):
    output_dir = Path(output_dir)
    manifest_path = output_dir / "manifest.csv"
    output_dir.mkdir(parents=True, exist_ok=True)
    completed, natural_counts, natural_totals = read_manifest(
        manifest_path,
        natural_dataset_names=(natural_dataset_name,),
    )

    write_header = not manifest_path.exists() or manifest_path.stat().st_size == 0
    with manifest_path.open("a", newline="") as manifest:
        writer = csv.writer(manifest)
        if write_header:
            writer.writerow(MANIFEST_HEADER)
            manifest.flush()

        if include_targeted:
            for consistency_mode, inject_bottom in [
                ("strong", False),
                ("weak", True),
            ]:
                mode_dir = output_dir / targeted_dir_name / consistency_mode
                mode_dir.mkdir(parents=True, exist_ok=True)

                for signature_size, conditionals_count in combinations:
                    combo_dir = mode_dir / f"{signature_size}_{conditionals_count}"
                    combo_dir.mkdir(parents=True, exist_ok=True)

                    for index in range(samples_per_combination):
                        manifest_key = (
                            targeted_dataset_name,
                            consistency_mode,
                            signature_size,
                            conditionals_count,
                            index,
                        )
                        if manifest_key in completed:
                            continue

                        filename = (
                            combo_dir
                            / f"randomTest_{signature_size}_{conditionals_count}_{index}.cl"
                        )
                        query_filename = (
                            combo_dir
                            / f"randomQueries_{signature_size}_{conditionals_count}_{index}.cl"
                        )
                        print(
                            "sampling %s/%s %s/%s #%s -> %s, %s"
                            % (
                                targeted_dir_name,
                                consistency_mode,
                                signature_size,
                                conditionals_count,
                                index,
                                filename,
                                query_filename,
                            )
                        )
                        variables, conditionals, _ = samplingConsistentCKB(
                            signature_size,
                            conditionals_count,
                            consistency_mode=consistency_mode,
                            inject_bottom=inject_bottom,
                            max_attempts=max_attempts,
                            verbose=False,
                        )
                        queries = sampleQueries(
                            variables,
                            queries_per_belief_base,
                            existing_conditionals=conditionals,
                            max_attempts=max_attempts,
                        )
                        makeCKB(variables, conditionals, [], str(filename))
                        makeQueryfile(queries, str(query_filename))
                        writer.writerow(
                            [
                                targeted_dataset_name,
                                consistency_mode,
                                signature_size,
                                conditionals_count,
                                index,
                                filename,
                                query_filename,
                            ]
                        )
                        manifest.flush()
                        completed.add(manifest_key)

        if include_natural:
            for signature_size, conditionals_count in combinations:
                total_key = (signature_size, conditionals_count)
                while natural_totals.get(total_key, 0) < samples_per_combination:
                    variables, conditionals, belief_base = samplingConsistentCKB(
                        signature_size,
                        conditionals_count,
                        consistency_mode="weak_or_strong",
                        inject_bottom=False,
                        max_attempts=max_attempts,
                        verbose=False,
                    )
                    actual_consistency = classify_belief_base(belief_base)
                    key = (signature_size, conditionals_count, actual_consistency)
                    natural_index = natural_counts.get(key, 0)
                    natural_counts[key] = natural_index + 1
                    natural_totals[total_key] = natural_totals.get(total_key, 0) + 1

                    combo_dir = (
                        output_dir
                        / natural_dir_name
                        / actual_consistency
                        / f"{signature_size}_{conditionals_count}"
                    )
                    filename = (
                        combo_dir
                        / f"randomTest_{signature_size}_{conditionals_count}_{natural_index}.cl"
                    )
                    query_filename = (
                        combo_dir
                        / f"randomQueries_{signature_size}_{conditionals_count}_{natural_index}.cl"
                    )
                    print(
                        "sampling %s/%s %s/%s #%s -> %s, %s"
                        % (
                            natural_dir_name,
                            actual_consistency,
                            signature_size,
                            conditionals_count,
                            natural_index,
                            filename,
                            query_filename,
                        )
                    )
                    queries = sampleQueries(
                        variables,
                        queries_per_belief_base,
                        existing_conditionals=conditionals,
                        max_attempts=max_attempts,
                    )
                    makeCKB(variables, conditionals, [], str(filename))
                    makeQueryfile(queries, str(query_filename))
                    manifest_key = (
                        natural_dataset_name,
                        actual_consistency,
                        signature_size,
                        conditionals_count,
                        natural_index,
                    )
                    writer.writerow(
                        [
                            natural_dataset_name,
                            actual_consistency,
                            signature_size,
                            conditionals_count,
                            natural_index,
                            filename,
                            query_filename,
                        ]
                    )
                    manifest.flush()
                    completed.add(manifest_key)


def generate_natural_repeated_vars_sets(
    combinations=LEXINF_ECSQARU_COMBINATIONS,
    samples_per_combination=DEFAULT_SAMPLES_PER_COMBINATION,
    queries_per_belief_base=DEFAULT_QUERIES_PER_BELIEF_BASE,
    output_dir=DEFAULT_REPEATED_VARS_OUTPUT_DIR,
    dataset_name="natural-repeated-vars",
    dir_name="natural-repeated-vars",
    formula_max_depth=4,
    leaf_probability=0.35,
    negation_probability=0.25,
    max_attempts=DEFAULT_MAX_ATTEMPTS,
):
    """Generate natural bases with repeated variables and classify afterward."""
    output_dir = Path(output_dir)
    manifest_path = output_dir / "manifest.csv"
    output_dir.mkdir(parents=True, exist_ok=True)
    completed, totals, consistency_counts = read_repeated_vars_manifest(manifest_path)

    write_header = not manifest_path.exists() or manifest_path.stat().st_size == 0
    with manifest_path.open("a", newline="") as manifest:
        writer = csv.writer(manifest)
        if write_header:
            writer.writerow(REPEATED_VARS_MANIFEST_HEADER)
            manifest.flush()

        for signature_size, conditionals_count in combinations:
            total_key = (signature_size, conditionals_count)
            attempts_for_combo = 0
            while totals.get(total_key, 0) < samples_per_combination:
                attempts_for_entry = 0
                while True:
                    attempts_for_entry += 1
                    attempts_for_combo += 1
                    if max_attempts is not None and attempts_for_entry > max_attempts:
                        raise RuntimeError(
                            "failed to sample a weak-or-strong natural-repeated-vars "
                            "belief base after %s attempts" % max_attempts
                        )
                    variables, conditionals = sample_conditionals_repeated_vars(
                        signature_size,
                        conditionals_count,
                        formula_max_depth=formula_max_depth,
                        leaf_probability=leaf_probability,
                        negation_probability=negation_probability,
                    )
                    actual_consistency, stats = classify_conditionals(
                        variables, conditionals
                    )
                    if actual_consistency != "inconsistent":
                        break

                combo_total_index = totals.get(total_key, 0)
                consistency_key = (
                    signature_size,
                    conditionals_count,
                    actual_consistency,
                )
                index = consistency_counts.get(consistency_key, 0)
                manifest_key = (
                    actual_consistency,
                    signature_size,
                    conditionals_count,
                    index,
                )
                if manifest_key in completed:
                    consistency_counts[consistency_key] = index + 1
                    totals[total_key] = combo_total_index + 1
                    continue

                combo_dir = (
                    output_dir
                    / dir_name
                    / actual_consistency
                    / f"{signature_size}_{conditionals_count}"
                )
                filename = (
                    combo_dir
                    / f"randomTest_{signature_size}_{conditionals_count}_{index}.cl"
                )
                query_filename = (
                    combo_dir
                    / f"randomQueries_{signature_size}_{conditionals_count}_{index}.cl"
                )
                print(
                    "sampling %s/%s %s/%s #%s "
                    "(combo total %s/%s, attempts entry=%s combo=%s) -> %s, %s"
                    % (
                        dir_name,
                        actual_consistency,
                        signature_size,
                        conditionals_count,
                        index,
                        combo_total_index + 1,
                        samples_per_combination,
                        attempts_for_entry,
                        attempts_for_combo,
                        filename,
                        query_filename,
                    ),
                    flush=True,
                )
                queries = sample_queries_repeated_vars(
                    variables,
                    queries_per_belief_base,
                    existing_conditionals=conditionals,
                    formula_max_depth=formula_max_depth,
                    leaf_probability=leaf_probability,
                    negation_probability=negation_probability,
                    max_attempts=max_attempts,
                )
                makeCKB(variables, conditionals, [], str(filename))
                makeQueryfile(queries, str(query_filename))
                partition_lengths, consistency_calls, consistency_levels = stats
                writer.writerow(
                    [
                        dataset_name,
                        actual_consistency,
                        signature_size,
                        conditionals_count,
                        index,
                        combo_total_index,
                        attempts_for_entry,
                        ";".join(str(value) for value in partition_lengths),
                        consistency_calls,
                        consistency_levels,
                        formula_max_depth,
                        filename,
                        query_filename,
                    ]
                )
                manifest.flush()
                completed.add(manifest_key)
                consistency_counts[consistency_key] = index + 1
                totals[total_key] = combo_total_index + 1


def canonical(tMin):
    # tMin = sorted(tMin, key=len)
    tMin = {tuple(sorted(t)) for t in tMin}
    return tMin


def filterQueries(ckb, index, query, valid):
    q = query
    vMin, fMin = ckb.compile_query(query)
    ### we consider any constraint of the form x >= 0 as trivial
    ### as x can trivially be lower bounded by 0, given the CKB is consistent
    # if vMin ==[[]] or fMin == [[]]:
    # if vMin ==[[]] or fMin == [[]]:
    if fMin == [[]]:
        return
    s = z3.Solver()
    ### check that query is not a tautology of any conditional
    c1 = [
        z3.sat == s.check(q.antecedence != c.antecedence)
        for _, c in ckb.conditionals.items()
    ]
    c2 = [
        z3.sat == s.check(q.consequence != c.consequence)
        for _, c in ckb.conditionals.items()
    ]
    c3 = [
        z3.sat == s.check(q.consequence != z3.Not(c.consequence))
        for _, c in ckb.conditionals.items()
    ]
    C = all([any([a, b, c]) for a, b, c in zip(c1, c2, c3, strict=False)])
    ### check that vMin and fMin are valid at least once
    c5 = (z3.sat == s.check(q.make_A_then_B())) and (
        z3.sat == s.check(q.make_A_then_not_B())
    )
    # if c1 and c2 and c3  and c5:
    if C and c5:
        vMin, fMin = canonical(vMin), canonical(fMin)
        if fMin == vMin:
            return
        ### check that such a constraint isnt already sampled
        if (vMin, fMin) not in valid.values():
            valid[index] = (vMin, fMin)
            # print(index)


def rejectionSampling(S, R, Q, L):
    attempt = 0
    while True:
        attempt += 1
        # print(attempt)
        VAR, COND, CKB = samplingConsistentCKB(S, R)
        queries = ",".join([sampleConditional(VAR) for _ in range(Q)])
        queries = parseQuery(queries)
        print("query sampled")
        valid = dict()
        for i, q in queries.items():
            filterQueries(CKB, i, q, valid)
            print(i, "th query checked")
            print(len(valid), "found")
            if len(valid) >= L:
                break
        if len(valid) >= L:
            # print(len(valid))
            # print([i for i in valid.keys()])
            Q = [queries[i] for i in valid.keys()]
            # print([v[1] for v in valid.values()])
            # print("Valid: ",sum([inferenceP(CKB, q) for q in Q]))
            return VAR, COND, CKB, Q


def sumlist(ll, amount):
    for l in ll:
        if (g := sum(i == 0 for i in l)) >= amount:
            print(l)
            # print(ll)
            return True
        print(l)
    return False


def parse_combination(value):
    parts = value.replace("/", ",").split(",")
    if len(parts) != 2:
        raise argparse.ArgumentTypeError(
            f"expected combination as S/R or S,R, got: {value}"
        )
    try:
        return (int(parts[0]), int(parts[1]))
    except ValueError as exc:
        raise argparse.ArgumentTypeError(
            f"expected integer combination as S/R or S,R, got: {value}"
        ) from exc


def parse_args():
    parser = argparse.ArgumentParser(
        description="Generate random conditional belief-base benchmark datasets."
    )
    parser.add_argument(
        "--mode",
        choices=[
            "natural-repeated-vars",
            "natural-read-once",
            "targeted-literal-bottom",
            "legacy-all",
        ],
        default="natural-repeated-vars",
        help=(
            "Generation mode. natural-repeated-vars is the canonical mode for "
            "future weak/strong comparisons. targeted-literal-bottom preserves "
            "the legacy explicit Bottom injection stress test."
        ),
    )
    parser.add_argument("--output-dir", default=None)
    parser.add_argument(
        "--combination",
        action="append",
        type=parse_combination,
        default=[],
        metavar="S/R",
        help="Combination to generate. Can be passed multiple times.",
    )
    parser.add_argument(
        "--samples-per-combination",
        type=int,
        default=DEFAULT_SAMPLES_PER_COMBINATION,
    )
    parser.add_argument(
        "--queries-per-belief-base",
        type=int,
        default=DEFAULT_QUERIES_PER_BELIEF_BASE,
    )
    parser.add_argument("--max-attempts", type=int, default=DEFAULT_MAX_ATTEMPTS)
    parser.add_argument("--formula-max-depth", type=int, default=4)
    parser.add_argument("--leaf-probability", type=float, default=0.35)
    parser.add_argument("--negation-probability", type=float, default=0.25)
    parser.add_argument("--seed", type=int, default=None)
    return parser.parse_args()


def main():
    args = parse_args()
    if args.seed is not None:
        random.seed(args.seed)

    combinations = args.combination or LEXINF_ECSQARU_COMBINATIONS

    if args.mode == "natural-repeated-vars":
        output_dir = args.output_dir or DEFAULT_REPEATED_VARS_OUTPUT_DIR
        generate_natural_repeated_vars_sets(
            combinations=combinations,
            samples_per_combination=args.samples_per_combination,
            queries_per_belief_base=args.queries_per_belief_base,
            output_dir=output_dir,
            formula_max_depth=args.formula_max_depth,
            leaf_probability=args.leaf_probability,
            negation_probability=args.negation_probability,
            max_attempts=args.max_attempts,
        )
        return

    if args.mode == "natural-read-once":
        output_dir = args.output_dir or DEFAULT_NATURAL_READ_ONCE_OUTPUT_DIR
        generate_belief_base_sets(
            combinations=combinations,
            samples_per_combination=args.samples_per_combination,
            queries_per_belief_base=args.queries_per_belief_base,
            output_dir=output_dir,
            max_attempts=args.max_attempts,
            include_targeted=False,
            include_natural=True,
            natural_dataset_name="natural-read-once",
            natural_dir_name="natural-read-once",
        )
        return

    if args.mode == "targeted-literal-bottom":
        output_dir = args.output_dir or DEFAULT_TARGETED_LITERAL_BOTTOM_OUTPUT_DIR
        generate_belief_base_sets(
            combinations=combinations,
            samples_per_combination=args.samples_per_combination,
            queries_per_belief_base=args.queries_per_belief_base,
            output_dir=output_dir,
            max_attempts=args.max_attempts,
            include_targeted=True,
            include_natural=False,
            targeted_dataset_name="targeted-literal-bottom",
            targeted_dir_name="targeted-literal-bottom",
        )
        return

    output_dir = args.output_dir or DEFAULT_OUTPUT_DIR
    generate_belief_base_sets(
        combinations=combinations,
        samples_per_combination=args.samples_per_combination,
        queries_per_belief_base=args.queries_per_belief_base,
        output_dir=output_dir,
        max_attempts=args.max_attempts,
        include_targeted=True,
        include_natural=True,
    )


if __name__ == "__main__":
    main()
