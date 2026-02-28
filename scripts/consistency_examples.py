"""Compact consistency examples for signature a,b.

This script iterates a small set of belief bases and fact combinations
and prints a one-line summary for each using System Z PreOCF.

Notation:
- Use plain Latin: "Bottom" for the false consequent.
- Conjunction in antecedents uses commas, disjunction uses semicolons, negation uses '!'.
"""

from __future__ import annotations

from typing import Iterable, List, Optional

from inference.preocf import PreOCF, SystemZPreOCF
from parser.Wrappers import parse_belief_base


def build_kb_string(
    conditions: Iterable[str], *, signature: str = "a,b", name: str = "kb"
) -> str:
    conds_body = ",\n".join(conditions)
    return f"signature\n{signature}\n\nconditionals\n{name}{{\n{conds_body}\n}}"


def main() -> None:
    # Define test cases. Each case specifies conditionals and optional facts.
    # The examples mirror common weak-consistency scenarios.
    cases = [
        {
            "id": 1,
            "conds": ["(Bottom|a)"],
            "facts": [],
        },
        {
            "id": 2,
            "conds": [],
            "facts": ["a"],
        },
        {
            "id": 3,
            "conds": [],
            "facts": [],
        },
        {
            "id": 4,
            "conds": ["(b|a)", "(!b|a)"],
            "facts": [],
        },
        {
            "id": 5,
            "conds": ["(b|a)", "(!b|a)", "(Bottom|a,!b)"],
            "facts": [],
        },
        {
            "id": 6,
            "conds": ["(Bottom|!a)"],
            "facts": ["!a"],
        },
    ]

    for case in cases:
        kb_str = build_kb_string(case["conds"], name=f"case{case['id']}")
        bb = parse_belief_base(kb_str)
        facts: Optional[List[str]] = case.get("facts") or None

        # Reprint conditionals and facts for this case
        print(f"Case {case['id']}: conditionals={bb.conditionals}, facts={facts}")

        try:
            # Use extended mode to surface weak-consistency diagnostics across all cases
            ocf: SystemZPreOCF = PreOCF.init_system_z(bb, facts=facts, extended=True)
            print(f"Case {case['id']}: {ocf.summary()}")
            # Also print layers with conditionals for clarity
            print(ocf.format_layers_with_conditionals())
        except ValueError as e:
            # Some combinations (facts + conditionals) may be outright inconsistent
            # Reverse order: operator first (already produced), keep prefix as requested
            print(
                f"Case {case['id']}: inconsistent input: {bb.conditionals}, {facts}; {e}"
            )


if __name__ == "__main__":
    main()
