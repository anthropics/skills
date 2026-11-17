#!/usr/bin/env python3
"""rules_matrix_skeleton.py

Creates a source-backed *skeleton* for jurisdiction rule capture.

This script intentionally does NOT fetch rules, does NOT guess, and does NOT change any
existing evidence/UID systems.

Use it to create a repeatable structure that can later be populated from cited sources
(local rules, FRAP/FRCP, standing orders) by an agent or manual process.

Output:
- JSON skeleton with explicit placeholders for sources + extracted requirements

Example:
  python rules_matrix_skeleton.py --jurisdiction ninth --out ../rules/ninth.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List


@dataclass
class RuleSource:
    label: str
    url: str
    retrieved_at: str
    notes: str = ""


@dataclass
class DocumentRequirements:
    required_sections: List[str] = field(default_factory=list)
    certificates_required: List[str] = field(default_factory=list)
    word_limits: Dict[str, str] = field(default_factory=dict)
    formatting: Dict[str, str] = field(default_factory=dict)
    local_rule_deltas: List[str] = field(default_factory=list)


@dataclass
class JurisdictionRuleMatrix:
    jurisdiction_key: str
    created_at: str
    sources: List[RuleSource] = field(default_factory=list)
    documents: Dict[str, DocumentRequirements] = field(default_factory=dict)
    extraction_todo: List[str] = field(default_factory=list)


def now_iso_utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def build_skeleton(jurisdiction_key: str) -> JurisdictionRuleMatrix:
    matrix = JurisdictionRuleMatrix(
        jurisdiction_key=jurisdiction_key,
        created_at=now_iso_utc(),
        sources=[],
        documents={
            "declaration": DocumentRequirements(
                required_sections=[
                    "caption_or_cover (if required)",
                    "declarant_identity",
                    "fact_blocks",
                    "signature_block",
                ],
                certificates_required=[],
            ),
            "motion": DocumentRequirements(
                required_sections=[
                    "caption_or_cover (if required)",
                    "relief_requested",
                    "legal_standard",
                    "argument",
                    "conclusion",
                ],
                certificates_required=[],
            ),
            "sanctions": DocumentRequirements(
                required_sections=[
                    "caption_or_cover (if required)",
                    "basis_for_sanctions",
                    "requested_sanction",
                    "legal_authority",
                ],
                certificates_required=[],
            ),
            "appellate_opening_brief": DocumentRequirements(
                required_sections=[
                    "cover_page",
                    "toc",
                    "toa",
                    "frap_28_sections (see skill templates)",
                    "certificate_of_compliance",
                    "certificate_of_service",
                ],
                certificates_required=[
                    "certificate_of_compliance",
                    "certificate_of_service",
                ],
                word_limits={},
            ),
        },
        extraction_todo=[
            "Add authoritative sources (local rules / FRAP / FRCP / standing orders) with URLs",
            "Extract word limits and certificate requirements from sources",
            "Extract formatting deltas (fonts, margins, covers) ONLY if source-backed",
            "Record every extracted requirement with a source pointer in notes",
        ],
    )
    return matrix


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jurisdiction", required=True, help="Machine key, e.g. ninth, first, dc")
    parser.add_argument("--out", required=True, help="Output JSON file path")
    args = parser.parse_args()

    out_path = Path(args.out).expanduser().resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)

    skeleton = build_skeleton(args.jurisdiction.strip())
    out_path.write_text(json.dumps(asdict(skeleton), indent=2, sort_keys=False), encoding="utf-8")

    print(f"Wrote skeleton: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
