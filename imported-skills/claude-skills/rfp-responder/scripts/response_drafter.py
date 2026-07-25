#!/usr/bin/env python3
"""response_drafter.py - Build a Shipley-method proof-point matrix + GAP audit + win-theme injection.

Stdlib only. Deterministic logic. NEVER invents claims to fill GAP requirements.

Inputs (JSON):
  {
    "rfp_requirements": [...]   OR   "rfp_requirements_path": "parsed.json"
    "proof_points_library": [
       {
         "name": "...",
         "type": "case_study|cert|customer_quote|technical_attestation|benchmark",
         "requirement_match_tags": ["soc2", "saml", "aws", ...],
         "verifiable_source": "..."
       }, ...
    ],
    "win_themes": ["operational simplicity", "financial-services depth", ...]
  }

For each requirement:
  - Tokenize the requirement text (lowercase, strip punctuation, dedupe, drop stopwords).
  - For each proof point, intersect proof.requirement_match_tags with requirement tokens.
  - If 2+ tag matches AND proof.type in {case_study, cert, technical_attestation, benchmark}
       -> STRONG
  - If 1 tag match OR proof.type in {customer_quote}
       -> PARTIAL
  - If 0 matches
       -> GAP

For each win-theme: count how many requirements it threads through.
  Theme appearing in <2 requirements -> flag as "DECORATIVE", not strategic.

Output: response-draft markdown (or JSON) with:
  - Compliance matrix (every requirement -> proof + match level)
  - GAP audit (explicit, no inventing)
  - Win-theme coverage report

Usage:
    python response_drafter.py --sample
    python response_drafter.py --input draft_input.json --output markdown
    python response_drafter.py --input draft_input.json --output json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any


STOPWORDS = {
    "the", "a", "an", "is", "are", "was", "were", "be", "been", "being",
    "and", "or", "but", "of", "to", "in", "on", "at", "for", "with", "by",
    "must", "shall", "should", "may", "will", "would", "could",
    "vendor", "vendors", "platform", "provide", "provides", "support", "supports",
    "this", "that", "these", "those", "it", "its", "our", "your",
    "required", "mandatory", "optional", "preferred", "desired",
    "from", "as", "if", "than", "then", "do", "does", "did",
    "have", "has", "had",
}

STRONG_PROOF_TYPES = {"case_study", "cert", "technical_attestation", "benchmark"}
PARTIAL_PROOF_TYPES = {"customer_quote"}


SAMPLE_INPUT = {
    "rfp_requirements": [
        {"id": "R001", "section": "Mandatory", "tag": "MANDATORY",
         "text": "Vendor must hold SOC 2 Type II certification.", "evidence": {}},
        {"id": "R002", "section": "Mandatory", "tag": "MANDATORY",
         "text": "Vendor shall provide 24/7 SOC coverage with named on-call rotation.", "evidence": {}},
        {"id": "R003", "section": "Mandatory", "tag": "MANDATORY",
         "text": "Vendor is required to support SAML 2.0 and SCIM provisioning.", "evidence": {}},
        {"id": "R004", "section": "Mandatory", "tag": "MANDATORY",
         "text": "The platform must integrate with AWS, GCP, and Azure native logging.", "evidence": {}},
        {"id": "R005", "section": "Weighted", "tag": "WEIGHTED",
         "text": "Mean Time to Detect benchmarks vs peers.", "evidence": {"points": 25}},
        {"id": "R006", "section": "Weighted", "tag": "WEIGHTED",
         "text": "Customer references in financial services.", "evidence": {"points": 20}},
        {"id": "R007", "section": "Nice-to-Have", "tag": "NICE-TO-HAVE",
         "text": "FedRAMP authorization is preferred but not required.", "evidence": {}},
    ],
    "proof_points_library": [
        {"name": "SOC 2 Type II report (2026)", "type": "cert",
         "requirement_match_tags": ["soc", "2", "type", "ii", "certification"],
         "verifiable_source": "https://trust.example.com/soc2-2026.pdf"},
        {"name": "24/7 SOC staffing attestation", "type": "technical_attestation",
         "requirement_match_tags": ["soc", "24/7", "coverage", "on-call", "rotation"],
         "verifiable_source": "internal SecOps runbook v3.2"},
        {"name": "SAML/SCIM integration guide", "type": "technical_attestation",
         "requirement_match_tags": ["saml", "scim", "provisioning"],
         "verifiable_source": "docs.example.com/saml-scim"},
        {"name": "AWS/GCP/Azure logging case study (Globex)", "type": "case_study",
         "requirement_match_tags": ["aws", "gcp", "azure", "logging", "integrate", "native"],
         "verifiable_source": "globex-cs-2025.pdf"},
        {"name": "MTTD benchmark vs Gartner peer cohort", "type": "benchmark",
         "requirement_match_tags": ["mttd", "mean", "time", "detect", "benchmarks", "peers"],
         "verifiable_source": "Gartner MQ supplement 2026"},
        {"name": "Financial services customer quote (FNB)", "type": "customer_quote",
         "requirement_match_tags": ["financial", "services", "customer", "references"],
         "verifiable_source": "FNB CISO quote, approved 2026-03"},
    ],
    "win_themes": [
        "operational simplicity at scale",
        "financial-services regulatory depth",
        "MTTD leadership vs Gartner peer cohort",
        "AWS/GCP/Azure native logging without bolt-ons",
    ],
}


def tokenize(text: str) -> set[str]:
    tokens = re.findall(r"[a-zA-Z0-9./]+", text.lower())
    return {t for t in tokens if t not in STOPWORDS and len(t) > 1}


def score_match(requirement: dict[str, Any], proof: dict[str, Any]) -> tuple[int, list[str]]:
    """Return (match_count, matched_tags)."""
    req_tokens = tokenize(requirement["text"])
    matched = [tag for tag in proof.get("requirement_match_tags", []) if tag.lower() in req_tokens]
    return len(matched), matched


def assign_proof(requirement: dict[str, Any], library: list[dict[str, Any]]) -> dict[str, Any]:
    best_count = 0
    best_proof: dict[str, Any] | None = None
    best_matched: list[str] = []
    for proof in library:
        count, matched = score_match(requirement, proof)
        if count > best_count:
            best_count = count
            best_proof = proof
            best_matched = matched
    if best_proof is None or best_count == 0:
        return {"level": "GAP", "proof": None, "matched_tags": []}
    if best_count >= 2 and best_proof["type"] in STRONG_PROOF_TYPES:
        level = "STRONG"
    elif best_count >= 1 and best_proof["type"] in STRONG_PROOF_TYPES:
        level = "PARTIAL"
    elif best_count >= 1 and best_proof["type"] in PARTIAL_PROOF_TYPES:
        level = "PARTIAL"
    else:
        level = "PARTIAL"
    return {"level": level, "proof": best_proof, "matched_tags": best_matched}


def thread_themes(requirements: list[dict[str, Any]], themes: list[str]) -> dict[str, dict[str, Any]]:
    """For each theme, list requirements whose text overlaps theme tokens."""
    report: dict[str, dict[str, Any]] = {}
    for theme in themes:
        theme_tokens = tokenize(theme)
        threaded: list[str] = []
        for req in requirements:
            req_tokens = tokenize(req["text"])
            if theme_tokens & req_tokens:
                threaded.append(req["id"])
        verdict = "STRATEGIC" if len(threaded) >= 2 else "DECORATIVE"
        report[theme] = {
            "requirement_ids": threaded,
            "count": len(threaded),
            "verdict": verdict,
        }
    return report


def build_matrix(payload: dict[str, Any]) -> dict[str, Any]:
    if "rfp_requirements_path" in payload and "rfp_requirements" not in payload:
        p = Path(payload["rfp_requirements_path"])
        loaded = json.loads(p.read_text(encoding="utf-8"))
        requirements = loaded.get("requirements", loaded if isinstance(loaded, list) else [])
    else:
        requirements = payload.get("rfp_requirements", [])
    library = payload.get("proof_points_library", [])
    themes = payload.get("win_themes", [])

    matrix: list[dict[str, Any]] = []
    for req in requirements:
        assignment = assign_proof(req, library)
        matrix.append({
            "requirement_id": req["id"],
            "tag": req["tag"],
            "section": req.get("section", ""),
            "text": req["text"],
            "match_level": assignment["level"],
            "proof_name": assignment["proof"]["name"] if assignment["proof"] else None,
            "proof_type": assignment["proof"]["type"] if assignment["proof"] else None,
            "verifiable_source": assignment["proof"]["verifiable_source"] if assignment["proof"] else None,
            "matched_tags": assignment["matched_tags"],
        })

    level_counts = Counter(row["match_level"] for row in matrix)
    mandatory_gaps = [row for row in matrix if row["tag"] == "MANDATORY" and row["match_level"] == "GAP"]
    theme_report = thread_themes(requirements, themes)

    return {
        "matrix": matrix,
        "level_counts": dict(level_counts),
        "mandatory_gap_count": len(mandatory_gaps),
        "mandatory_gaps": mandatory_gaps,
        "win_theme_report": theme_report,
        "requirement_total": len(requirements),
    }


def render_markdown(result: dict[str, Any]) -> str:
    out: list[str] = []
    out.append("# RFP Response Draft — Proof-Point Matrix\n")
    total = result["requirement_total"]
    counts = result["level_counts"]
    out.append(f"**Requirements:** {total}")
    if total > 0:
        strong = counts.get("STRONG", 0)
        partial = counts.get("PARTIAL", 0)
        gap = counts.get("GAP", 0)
        out.append(f"**STRONG:** {strong} ({100*strong/total:.0f}%) | "
                   f"**PARTIAL:** {partial} ({100*partial/total:.0f}%) | "
                   f"**GAP:** {gap} ({100*gap/total:.0f}%)")
    out.append(f"\n**MANDATORY GAPs:** {result['mandatory_gap_count']} "
               "(LEADERSHIP DECISION REQUIRED — close gap, partner-bid, or no-bid)\n")

    out.append("## Compliance matrix\n")
    out.append("| Req | Tag | Match | Proof | Source |")
    out.append("|---|---|---|---|---|")
    for row in result["matrix"]:
        proof = row["proof_name"] or "**(NO PROOF — GAP)**"
        source = row["verifiable_source"] or "—"
        out.append(f"| {row['requirement_id']} | {row['tag']} | {row['match_level']} | {proof} | {source} |")
    out.append("")

    if result["mandatory_gaps"]:
        out.append("## GAP audit (MANDATORY requirements without proof)\n")
        out.append("> HARD RULE: do NOT invent claims for these. Leadership decides: "
                   "close the gap pre-submission, partner-bid, or no-bid.\n")
        for row in result["mandatory_gaps"]:
            out.append(f"- **{row['requirement_id']}** ({row['section']}): {row['text']}")
        out.append("")

    out.append("## Win-theme coverage\n")
    for theme, info in result["win_theme_report"].items():
        ids = ", ".join(info["requirement_ids"]) or "(none)"
        out.append(f"- **{theme}** — threads through {info['count']} req(s): {ids} → **{info['verdict']}**")
    out.append("")

    decorative = [t for t, info in result["win_theme_report"].items() if info["verdict"] == "DECORATIVE"]
    if decorative:
        out.append("### Decorative themes (flagged)\n")
        out.append("These themes appear in <2 requirements and are decorative, not strategic. "
                   "Either remove or strengthen so they thread across multiple sections.\n")
        for t in decorative:
            out.append(f"- {t}")
        out.append("")

    return "\n".join(out) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build proof-point matrix + GAP audit + win-theme report.")
    parser.add_argument("--input", help="Path to draft-input JSON.")
    parser.add_argument("--output", choices=["json", "markdown"], default="markdown")
    parser.add_argument("--sample", action="store_true", help="Use built-in synthetic input.")
    args = parser.parse_args(argv)

    if args.sample:
        payload = SAMPLE_INPUT
    elif args.input:
        path = Path(args.input)
        if not path.exists():
            print(f"ERROR: input file not found: {args.input}", file=sys.stderr)
            return 1
        payload = json.loads(path.read_text(encoding="utf-8"))
    else:
        parser.print_help()
        return 0

    result = build_matrix(payload)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_markdown(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
