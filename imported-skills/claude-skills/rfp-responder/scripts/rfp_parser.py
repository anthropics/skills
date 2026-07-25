#!/usr/bin/env python3
"""rfp_parser.py - Parse an RFP / RFI / RFQ / security questionnaire into structured requirements.

Stdlib only. Regex + cue-word heuristics. No NLP libraries, no LLM calls.

The parser:
  1. Splits the document into sections (executive summary, technical requirements,
     security questionnaire, commercial terms, timeline, etc.) using common heading
     patterns.
  2. Extracts requirements as discrete numbered / bulleted / "must/shall/should" lines.
  3. Tags each requirement MANDATORY / WEIGHTED / NICE-TO-HAVE based on cue words:
       MANDATORY    - must, shall, required, mandatory, "is required to"
       WEIGHTED     - should, weighted scoring numbers present (e.g., "[20 points]"),
                      "evaluation criteria", "scored"
       NICE-TO-HAVE - may, preferred, desired, nice-to-have, optional
  4. Captures disclosed scoring criteria (lines that look like "X points" / "X%" weights).
  5. Captures submission deadline + format requirements (regex on common date patterns
     + "format" / "submission" cue words).

Usage:
    python rfp_parser.py --sample
    python rfp_parser.py --input rfp.md --output json
    python rfp_parser.py --input rfp.md --output markdown
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any


SAMPLE_RFP = """\
# RFP-2026-CLOUD-SECURITY-007

## 1. Executive Summary

Acme Holdings is seeking a cloud security platform vendor.
Total contract value: $1.5M over 3 years.
Submission deadline: 2026-06-14.
Format: PDF, max 80 pages, 11pt font minimum.

## 2. Mandatory Requirements

2.1 Vendor must hold SOC 2 Type II certification.
2.2 Vendor shall provide 24/7 SOC coverage with named on-call rotation.
2.3 Vendor is required to support SAML 2.0 and SCIM provisioning.
2.4 The platform must integrate with AWS, GCP, and Azure native logging.
2.5 Vendor shall meet a 99.9% platform uptime SLA.

## 3. Weighted Requirements (100 points total)

3.1 Threat detection coverage breadth [30 points]
3.2 Mean Time to Detect (MTTD) benchmarks vs peers [25 points]
3.3 Customer references in financial services [20 points]
3.4 Implementation timeline shorter than 90 days [15 points]
3.5 Quality of executive briefing materials [10 points]

The platform should support custom detection rule authoring.
Vendor should provide quarterly threat intelligence reports.

## 4. Nice-to-Have Capabilities

4.1 FedRAMP authorization is preferred but not required.
4.2 ISO 27001 certification is desired.
4.3 The platform may offer AI-assisted triage capabilities.
4.4 Vendor support for on-premises deployment is optional.

## 5. Commercial Terms

Multi-year discount expected. Payment terms NET-45.

## 6. Submission Format

Responses must be submitted via the procurement portal by 2026-06-14 17:00 ET.
Late submissions will not be accepted.
"""


MANDATORY_CUES = re.compile(
    r"\b(must|shall|required|mandatory|is required to|are required to|will be required)\b",
    re.IGNORECASE,
)
WEIGHTED_CUES = re.compile(
    r"\b(should|evaluation criteria|scored|weighted|preferred)\b",
    re.IGNORECASE,
)
NICE_CUES = re.compile(
    r"\b(may|preferred but not required|desired|nice[- ]to[- ]have|optional|is desired)\b",
    re.IGNORECASE,
)
POINTS_PATTERN = re.compile(r"\[(\d+)\s*(?:points?|pts?|%)\]", re.IGNORECASE)
DEADLINE_PATTERN = re.compile(
    r"(deadline|due|submission|submit by|responses? (?:are )?due)\s*[:\-]?\s*"
    r"(\d{4}[-/]\d{1,2}[-/]\d{1,2}|\d{1,2}[-/]\d{1,2}[-/]\d{2,4})",
    re.IGNORECASE,
)
FORMAT_PATTERN = re.compile(
    r"\b(format|page limit|max(?:imum)? \d+ pages?|font|portal|pdf|word|submitted via)\b",
    re.IGNORECASE,
)
HEADING_PATTERN = re.compile(r"^(#{1,3})\s+(.+?)\s*$")
REQ_LINE_PATTERN = re.compile(r"^\s*(\d+\.\d+|\d+\)|-|\*)\s+(.+?)\s*$")


def classify_requirement(text: str) -> tuple[str, dict[str, Any]]:
    """Return (tag, evidence_dict). Precedence: NICE > MANDATORY > WEIGHTED.

    NICE-TO-HAVE is checked first because phrases like "preferred but not required"
    contain the word "required" but are NOT mandatory.
    """
    evidence: dict[str, Any] = {"matched_cues": []}

    nice_match = NICE_CUES.search(text)
    if nice_match:
        evidence["matched_cues"].append(nice_match.group(0).lower())
        return "NICE-TO-HAVE", evidence

    mand_match = MANDATORY_CUES.search(text)
    if mand_match:
        evidence["matched_cues"].append(mand_match.group(0).lower())
        return "MANDATORY", evidence

    points_match = POINTS_PATTERN.search(text)
    if points_match:
        evidence["points"] = int(points_match.group(1))
        evidence["matched_cues"].append(f"[{points_match.group(1)} points]")
        return "WEIGHTED", evidence

    weight_match = WEIGHTED_CUES.search(text)
    if weight_match:
        evidence["matched_cues"].append(weight_match.group(0).lower())
        return "WEIGHTED", evidence

    return "UNCLASSIFIED", evidence


def split_sections(text: str) -> list[dict[str, Any]]:
    """Split document into sections by markdown headings."""
    sections: list[dict[str, Any]] = []
    current = {"heading": "(preamble)", "level": 0, "body": []}
    for line in text.splitlines():
        m = HEADING_PATTERN.match(line)
        if m:
            if current["body"] or current["heading"] != "(preamble)":
                sections.append(current)
            current = {
                "heading": m.group(2).strip(),
                "level": len(m.group(1)),
                "body": [],
            }
        else:
            current["body"].append(line)
    sections.append(current)
    return [s for s in sections if s["body"] or s["heading"] != "(preamble)"]


def extract_requirements(sections: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Extract individual requirements from sections."""
    reqs: list[dict[str, Any]] = []
    req_counter = 0
    for sec in sections:
        section_label = sec["heading"]
        for raw_line in sec["body"]:
            line = raw_line.strip()
            if not line or line.startswith("#"):
                continue
            m = REQ_LINE_PATTERN.match(raw_line)
            text = m.group(2).strip() if m else line
            # Only count lines that contain at least one classification cue or a points tag.
            if not (
                MANDATORY_CUES.search(text)
                or WEIGHTED_CUES.search(text)
                or NICE_CUES.search(text)
                or POINTS_PATTERN.search(text)
            ):
                continue
            tag, evidence = classify_requirement(text)
            req_counter += 1
            reqs.append({
                "id": f"R{req_counter:03d}",
                "section": section_label,
                "text": text,
                "tag": tag,
                "evidence": evidence,
            })
    return reqs


def extract_scoring(text: str) -> list[dict[str, Any]]:
    """Find lines with explicit point weights."""
    scoring: list[dict[str, Any]] = []
    for line in text.splitlines():
        m = POINTS_PATTERN.search(line)
        if m:
            scoring.append({"weight": int(m.group(1)), "line": line.strip()})
    return scoring


def extract_deadline(text: str) -> str | None:
    m = DEADLINE_PATTERN.search(text)
    return m.group(2) if m else None


def extract_format_notes(text: str) -> list[str]:
    notes: list[str] = []
    for line in text.splitlines():
        if FORMAT_PATTERN.search(line) and len(line.strip()) < 200:
            notes.append(line.strip())
    # Dedupe while preserving order.
    seen: set[str] = set()
    out: list[str] = []
    for n in notes:
        if n not in seen:
            seen.add(n)
            out.append(n)
    return out


def parse(text: str) -> dict[str, Any]:
    sections = split_sections(text)
    reqs = extract_requirements(sections)
    tag_counts = Counter(r["tag"] for r in reqs)
    return {
        "section_count": len(sections),
        "sections": [{"heading": s["heading"], "level": s["level"]} for s in sections],
        "requirement_count": len(reqs),
        "tag_breakdown": dict(tag_counts),
        "requirements": reqs,
        "scoring_criteria": extract_scoring(text),
        "deadline": extract_deadline(text),
        "format_notes": extract_format_notes(text),
    }


def render_markdown(parsed: dict[str, Any]) -> str:
    out: list[str] = []
    out.append("# RFP Parse Report\n")
    out.append(f"**Sections detected:** {parsed['section_count']}")
    out.append(f"**Requirements detected:** {parsed['requirement_count']}")
    out.append(f"**Deadline:** {parsed['deadline'] or '(not detected)'}\n")
    out.append("## Requirement breakdown\n")
    for tag, count in parsed["tag_breakdown"].items():
        out.append(f"- {tag}: {count}")
    out.append("\n## Requirements\n")
    for r in parsed["requirements"]:
        out.append(f"### {r['id']} — [{r['tag']}]")
        out.append(f"**Section:** {r['section']}")
        out.append(f"**Text:** {r['text']}")
        if r["evidence"].get("points"):
            out.append(f"**Points:** {r['evidence']['points']}")
        out.append(f"**Matched cues:** {', '.join(r['evidence']['matched_cues']) or '(none)'}")
        out.append("")
    out.append("## Scoring criteria detected\n")
    if parsed["scoring_criteria"]:
        for s in parsed["scoring_criteria"]:
            out.append(f"- [{s['weight']} pts] {s['line']}")
    else:
        out.append("(none disclosed)")
    out.append("\n## Format notes\n")
    if parsed["format_notes"]:
        for n in parsed["format_notes"]:
            out.append(f"- {n}")
    else:
        out.append("(none detected)")
    return "\n".join(out) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Parse an RFP into structured requirements.")
    parser.add_argument("--input", help="Path to RFP markdown/text file.")
    parser.add_argument("--output", choices=["json", "markdown"], default="markdown")
    parser.add_argument("--sample", action="store_true", help="Use built-in synthetic RFP.")
    args = parser.parse_args(argv)

    if args.sample:
        text = SAMPLE_RFP
    elif args.input:
        path = Path(args.input)
        if not path.exists():
            print(f"ERROR: input file not found: {args.input}", file=sys.stderr)
            return 1
        text = path.read_text(encoding="utf-8")
    else:
        parser.print_help()
        return 0

    parsed = parse(text)
    if args.output == "json":
        print(json.dumps(parsed, indent=2))
    else:
        print(render_markdown(parsed))
    return 0


if __name__ == "__main__":
    sys.exit(main())
