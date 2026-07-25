#!/usr/bin/env python3
"""Build a materials manuscript argument outline."""

from __future__ import annotations

import argparse
from pathlib import Path


# ---------------------------------------------------------------------------
# Minimal YAML-subset parser for claims file (stdlib only, no PyYAML)
# ---------------------------------------------------------------------------

def _parse_claims_yaml(text: str) -> list[dict[str, str]]:
    """Parse the simple claims YAML format.

    Expected structure::

        claims:
          - claim: "Some claim"
            evidence: "What evidence"
            boundary: "What boundary"
          - claim: "Another claim"
            ...

    Returns a list of dicts with keys *claim*, *evidence*, *boundary*.
    """
    claims: list[dict[str, str]] = []
    current: dict[str, str] = {}
    in_claims = False

    for raw_line in text.splitlines():
        stripped = raw_line.strip()
        if not stripped or stripped.startswith("#"):
            continue

        # Detect the top-level "claims:" key
        if stripped.rstrip(":").lower() == "claims":
            in_claims = True
            continue

        if not in_claims:
            continue

        # New list item starts with "- "
        if stripped.startswith("- "):
            if current:
                claims.append(current)
            current = {}
            rest = stripped[2:].strip()
            if ":" in rest:
                key, _, val = rest.partition(":")
                current[key.strip().lower()] = val.strip().strip("\"'")
        elif ":" in stripped:
            key, _, val = stripped.partition(":")
            current[key.strip().lower()] = val.strip().strip("\"'")

    if current:
        claims.append(current)

    return claims


# ---------------------------------------------------------------------------
# Outline builder
# ---------------------------------------------------------------------------

def _one_sentence_argument(topic: str, paper_type: str) -> str:
    """Return the one-sentence argument text, branched by *paper_type*."""
    if paper_type == "review-paper":
        return (
            f"This review organizes the current understanding of {topic}, "
            f"identifies key gaps, and proposes a research agenda."
        )
    if paper_type == "methods-paper":
        return (
            f"This paper presents and validates a protocol for {topic}, "
            f"establishing reproducibility boundaries."
        )
    # default: experimental-manuscript
    return (
        f"This manuscript connects material design, measured performance, "
        f"and mechanism evidence into one evidence chain for {topic}."
    )


def _section_guidance() -> dict[str, str]:
    """Return generic, topic-independent section guidance."""
    return {
        "Abstract": (
            "Use background-gap-method-result-implication structure."
        ),
        "Introduction": (
            "Build the gap chain: what is known \u2192 what is unknown "
            "\u2192 why this study addresses it."
        ),
        "Methods": (
            "Report materials, preparation, test standards, "
            "replicate count, and statistics."
        ),
        "Results and Discussion": (
            "Move from observation to comparison to mechanism to limitation."
        ),
    }


def _missing_evidence(paper_type: str) -> list[str]:
    """Return missing-evidence bullets branched by *paper_type*."""
    if paper_type == "review-paper":
        return [
            "literature coverage completeness and search strategy,",
            "bias assessment and inclusion/exclusion criteria,",
            "temporal coverage and field evolution,",
            "gap identification and proposed research agenda,",
            "target-journal formatting and current author instructions.",
        ]
    if paper_type == "methods-paper":
        return [
            "validation dataset and benchmark comparisons,",
            "reproducibility data across laboratories or conditions,",
            "comparison with existing protocols and standards,",
            "method sensitivity and detection limits,",
            "target-journal formatting and current author instructions.",
        ]
    # default: experimental-manuscript
    return [
        "exact material specifications,",
        "replicate count and statistics,",
        "mechanism evidence beyond a single technique,",
        "conditioning and aging data,",
        "target-journal formatting and current author instructions.",
    ]


def _claim_table(claims: list[dict[str, str]] | None) -> str:
    """Return the claim-evidence-boundary markdown table."""
    if not claims:
        claims = [
            {"claim": "[Claim 1]", "evidence": "[Evidence 1]", "boundary": "[Boundary 1]"},
            {"claim": "[Claim 2]", "evidence": "[Evidence 2]", "boundary": "[Boundary 2]"},
            {"claim": "[Claim 3]", "evidence": "[Evidence 3]", "boundary": "[Boundary 3]"},
        ]

    rows = []
    for c in claims:
        claim = c.get("claim", "")
        evidence = c.get("evidence", "")
        boundary = c.get("boundary", "")
        rows.append(f"| {claim} | {evidence} | {boundary} |")

    header = "| Claim | Evidence needed | Boundary |\n|---|---|---|"
    return header + "\n" + "\n".join(rows)


def build_outline(
    topic: str,
    paper_type: str,
    journal_family: str,
    claims_path: str | None = None,
) -> str:
    """Build the full outline text."""
    # -- claims table -------------------------------------------------------
    claims: list[dict[str, str]] | None = None
    if claims_path:
        p = Path(claims_path)
        if p.exists():
            claims = _parse_claims_yaml(p.read_text(encoding="utf-8"))

    claim_table = _claim_table(claims)

    # -- one-sentence argument ----------------------------------------------
    argument = _one_sentence_argument(topic, paper_type)

    # -- section guidance ---------------------------------------------------
    guidance = _section_guidance()

    # -- missing evidence ---------------------------------------------------
    missing = _missing_evidence(paper_type)
    missing_lines = "\n".join(f"- {m}" for m in missing)

    return f"""# Materials Science Manuscript Outline

Topic: {topic}
Paper type: {paper_type}
Journal family: {journal_family}

## One-sentence argument

{argument}

## Claim-evidence-boundary table

{claim_table}

## Abstract

{guidance["Abstract"]}

## Introduction

{guidance["Introduction"]}

## Methods

{guidance["Methods"]}

## Results and Discussion

{guidance["Results and Discussion"]}

## Missing evidence to confirm

{missing_lines}
"""


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--topic", required=True)
    parser.add_argument("--paper-type", default="experimental-manuscript")
    parser.add_argument("--journal-family", default="CBM")
    parser.add_argument("--claims", default=None,
                        help="Path to a YAML file defining claim-evidence-boundary triples")
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        build_outline(args.topic, args.paper_type, args.journal_family, args.claims),
        encoding="utf-8",
    )
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
