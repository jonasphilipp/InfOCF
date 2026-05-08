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


def read_manifest(manifest_path):
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

            if dataset == "natural":
                natural_key = (signature_size, conditionals_count, consistency_mode)
                natural_counts[natural_key] = max(
                    natural_counts.get(natural_key, 0), index + 1
                )
                total_key = (signature_size, conditionals_count)
                natural_totals[total_key] = natural_totals.get(total_key, 0) + 1

    return completed, natural_counts, natural_totals


def generate_belief_base_sets(
    combinations=LEXINF_ECSQARU_COMBINATIONS,
    samples_per_combination=DEFAULT_SAMPLES_PER_COMBINATION,
    queries_per_belief_base=DEFAULT_QUERIES_PER_BELIEF_BASE,
    output_dir=DEFAULT_OUTPUT_DIR,
    max_attempts=DEFAULT_MAX_ATTEMPTS,
    include_targeted=True,
    include_natural=True,
):
    output_dir = Path(output_dir)
    manifest_path = output_dir / "manifest.csv"
    output_dir.mkdir(parents=True, exist_ok=True)
    completed, natural_counts, natural_totals = read_manifest(manifest_path)

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
                mode_dir = output_dir / "targeted" / consistency_mode
                mode_dir.mkdir(parents=True, exist_ok=True)

                for signature_size, conditionals_count in combinations:
                    combo_dir = mode_dir / f"{signature_size}_{conditionals_count}"
                    combo_dir.mkdir(parents=True, exist_ok=True)

                    for index in range(samples_per_combination):
                        manifest_key = (
                            "targeted",
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
                            "sampling targeted/%s %s/%s #%s -> %s, %s"
                            % (
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
                                "targeted",
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
                        / "natural"
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
                        "sampling natural/%s %s/%s #%s -> %s, %s"
                        % (
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
                        "natural",
                        actual_consistency,
                        signature_size,
                        conditionals_count,
                        natural_index,
                    )
                    writer.writerow(
                        [
                            "natural",
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


if __name__ == "__main__":
    generate_belief_base_sets()
