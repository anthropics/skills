#!/usr/bin/env python3
"""Audit materials-science manuscript drafts for evidence-bounded writing."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


CHARACTERIZATION_TERMS = re.compile(
    r"\b(FTIR|XRD|SEM|TEM|EDS|DSC|TGA|DTG|DMA|XPS|AFM|MIP|micro-CT|"
    r"rheolog(?:y|ical)|spectroscop|microscop|fractograph|calorimetr)\b",
    re.IGNORECASE,
)
MECHANISM_TERMS = re.compile(
    r"\b(mechanism|curing|crosslink|interfacial|interface|pore structure|"
    r"fiber orientation|fracture|demulsification|interfacial energy|load transfer|"
    r"chemical reaction|hydration|crystallization|network formation)\b",
    re.IGNORECASE,
)
CAUSAL_OVERCLAIM_TERMS = re.compile(
    r"\b(proves?|confirms?|demonstrates?|causes?|is caused by|leads to|"
    r"results in|due to)\b",
    re.IGNORECASE,
)
STANDARD_TERMS = re.compile(r"\b(ASTM|ISO|GB/T?|JTG|AASHTO|EN|DIN|BS|standard)\b", re.IGNORECASE)
SAMPLE_PREP_TERMS = re.compile(
    r"\b(sample preparation|specimen|mix(?:ing|ed)|conditioning|"
    r"dosage|ratio|temperature|humidity|aging protocol|prepared|"
    r"curing (?:time|temperature|condition|protocol)|curing at)\b",
    re.IGNORECASE,
)
DURABILITY_BOUNDARY_TERMS = re.compile(
    r"\b(durability|aging|hygrothermal|freeze-thaw|UV|fatigue|service|field|"
    r"application boundary|engineering application|long-term|moisture|fire)\b",
    re.IGNORECASE,
)
FIGURE_REF_TERMS = re.compile(r"\b(Fig(?:ure)?\.?\s*\d+|Figure\s+\d+)\b", re.IGNORECASE)
CAPTION_TERMS = re.compile(r"\b(caption|Figure\s+\d+[:.]|Fig\.\s*\d+[:.])\b", re.IGNORECASE)


def issue(issue_id: str, message: str, severity: str = "error") -> dict[str, str]:
    return {"id": issue_id, "severity": severity, "message": message}


def audit_text(text: str) -> list[dict[str, str]]:
    issues: list[dict[str, str]] = []

    has_mechanism = bool(MECHANISM_TERMS.search(text))
    has_characterization = bool(CHARACTERIZATION_TERMS.search(text))
    has_causal_language = bool(CAUSAL_OVERCLAIM_TERMS.search(text))

    if has_mechanism and not has_characterization:
        issues.append(
            issue(
                "mechanism_without_characterization",
                "Mechanism language appears without characterization support such as FTIR, XRD, SEM, DSC, TGA, rheology, or microscopy.",
            )
        )

    if has_causal_language and not has_characterization:
        issues.append(
            issue(
                "causality_overclaim",
                "Causal verbs such as proves, confirms, demonstrates, causes, or due to need direct evidence or softer association language.",
            )
        )

    if not STANDARD_TERMS.search(text):
        issues.append(
            issue(
                "missing_test_standard",
                "No test standard or standard family was detected; report ASTM, ISO, GB, JTG, AASHTO, EN, or an equivalent protocol.",
            )
        )

    if not SAMPLE_PREP_TERMS.search(text):
        issues.append(
            issue(
                "missing_sample_preparation",
                "No sample preparation, specimen, mixing, curing, conditioning, dosage, or test-condition detail was detected.",
            )
        )

    if not DURABILITY_BOUNDARY_TERMS.search(text):
        issues.append(
            issue(
                "missing_durability_or_application_boundary",
                "The draft does not discuss durability, aging, service condition, field relevance, or engineering application boundary.",
            )
        )

    if FIGURE_REF_TERMS.search(text) and not CAPTION_TERMS.search(text):
        issues.append(
            issue(
                "figure_caption_text_mismatch",
                "The text cites figures but no caption-like statement was detected; check figure/caption/text claim consistency.",
            )
        )

    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, help="Draft manuscript text or Markdown file.")
    parser.add_argument("--json", action="store_true", help="Emit JSON.")
    args = parser.parse_args()

    text = Path(args.input).read_text(encoding="utf-8")
    issues = audit_text(text)
    payload = {"status": "pass" if not issues else "fail", "issues": issues}

    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        if issues:
            for item in issues:
                print(f"[{item['severity']}] {item['id']}: {item['message']}")
        else:
            print("PASS: no materials writing audit issues detected")

    return 0 if not issues else 1


if __name__ == "__main__":
    raise SystemExit(main())
