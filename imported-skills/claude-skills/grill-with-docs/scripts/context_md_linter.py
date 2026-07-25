#!/usr/bin/env python3
"""context_md_linter.py — Validate a CONTEXT.md against the CONTEXT-FORMAT.md structure.

Stdlib-only. Walks a CONTEXT.md and applies the format rules from Matt Pocock's
upstream CONTEXT-FORMAT.md (preserved verbatim in the skill's CONTEXT-FORMAT.md):

  1. H1 present at top (the context name)
  2. One-or-two-sentence description follows the H1
  3. ## Language section present
  4. Inside Language: each term is in `**Term**:` bold form
  5. Inside Language: each term has a one-sentence definition
  6. Inside Language: each term has a `_Avoid_:` aliases line (WARN if missing)
  7. ## Relationships section present (WARN if missing)
  8. ## Example dialogue section present (WARN if missing)
  9. Optional: ## Flagged ambiguities section

Output: PASS / WARN / FAIL per rule + an overall verdict.

NO LLM CALLS. Pure regex + line walking.

Usage:
    python context_md_linter.py CONTEXT.md
    python context_md_linter.py CONTEXT.md --output json
    python context_md_linter.py --sample        # lint the embedded sample
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple


SAMPLE_CONTEXT_MD = """# Ordering

The ordering context receives customer orders and tracks them through to handoff to Fulfillment.

## Language

**Order**:
A confirmed request from a Customer to acquire one or more Products.
_Avoid_: Purchase, transaction, cart

**Customer**:
A person or organization that places Orders.
_Avoid_: Client, buyer, account

**Product**:
A single SKU that can appear on an Order line.
_Avoid_: Item, good, SKU

## Relationships

- An **Order** belongs to exactly one **Customer**
- An **Order** has one or more **Products** via line items
- A **Customer** can have many **Orders**

## Example dialogue

> **Dev:** "When a **Customer** places an **Order**, are the **Products** locked at order time?"
> **Domain expert:** "Yes — Product price + spec is snapshotted onto the Order line. Subsequent Product edits don't change historical Orders."

## Flagged ambiguities

- "account" was used to mean both **Customer** and "billing account" — resolved: billing account moves to Billing context.
"""


def split_into_sections(text: str) -> Dict[str, str]:
    """Split markdown into top-level ## sections keyed by header text."""
    sections: Dict[str, str] = {}
    current_header = "_preamble_"
    buffer: List[str] = []
    for line in text.splitlines():
        m = re.match(r"^##\s+(.+?)\s*$", line)
        if m:
            sections[current_header] = "\n".join(buffer).strip()
            current_header = m.group(1).strip().lower()
            buffer = []
        else:
            buffer.append(line)
    sections[current_header] = "\n".join(buffer).strip()
    return sections


def extract_terms(language_section: str) -> List[Tuple[str, str, str]]:
    """Return list of (term, definition_line, avoid_line) tuples from the Language section.

    Each term entry looks like:
        **Term**:
        Definition sentence.
        _Avoid_: alias1, alias2
    """
    results: List[Tuple[str, str, str]] = []
    # Match `**Term**:` followed by the next non-empty line as definition,
    # and optionally an `_Avoid_:` line within the next 3 lines.
    pattern = re.compile(
        r"\*\*([^*]+?)\*\*\s*:\s*\n([^\n]+)\n?(?:([^\n]*_Avoid_[^\n]*)\n?)?",
        re.MULTILINE,
    )
    for match in pattern.finditer(language_section):
        term = match.group(1).strip()
        definition = match.group(2).strip()
        avoid = (match.group(3) or "").strip()
        results.append((term, definition, avoid))
    return results


def lint(text: str) -> Dict[str, Any]:
    findings: List[Dict[str, str]] = []

    def add(rule: str, level: str, message: str) -> None:
        findings.append({"rule": rule, "level": level, "message": message})

    # Rule 1: H1 present
    lines = text.splitlines()
    h1_line_index = None
    for i, line in enumerate(lines):
        if re.match(r"^#\s+\S", line):
            h1_line_index = i
            break
    if h1_line_index is None:
        add("h1-present", "FAIL", "No H1 (top-level '# Title') found. CONTEXT.md must start with the context name as H1.")
    else:
        add("h1-present", "PASS", f"H1 found at line {h1_line_index + 1}.")

    # Rule 2: one-or-two-sentence description after H1
    if h1_line_index is not None:
        desc_lines: List[str] = []
        for line in lines[h1_line_index + 1 :]:
            if re.match(r"^##\s", line):
                break
            if line.strip():
                desc_lines.append(line.strip())
        desc = " ".join(desc_lines).strip()
        sentence_count = len(re.findall(r"[.!?](?:\s|$)", desc))
        if not desc:
            add("description-present", "FAIL", "No description sentence between the H1 and the first ## section.")
        elif sentence_count > 3:
            add(
                "description-length",
                "WARN",
                f"Description has {sentence_count} sentences. CONTEXT-FORMAT.md asks for one or two.",
            )
        else:
            add("description-present", "PASS", f"Description present ({sentence_count} sentence(s)).")

    # Rule 3: ## Language section present
    sections = split_into_sections(text)
    if "language" not in sections:
        add("language-section", "FAIL", "No '## Language' section found. This is the required core of CONTEXT.md.")
        return finalize(findings)
    add("language-section", "PASS", "'## Language' section found.")

    # Rules 4 + 5 + 6: terms inside Language
    terms = extract_terms(sections["language"])
    if not terms:
        add(
            "language-terms",
            "FAIL",
            "No terms detected in the Language section. Each term must be in '**Term**:' bold form followed by a one-sentence definition.",
        )
    else:
        add("language-terms", "PASS", f"Detected {len(terms)} term(s) in Language section.")
        for term, definition, avoid in terms:
            # Rule 5: definition exists
            if not definition or definition.startswith("_Avoid_") or definition.startswith("**"):
                add(
                    "term-definition",
                    "FAIL",
                    f"Term '**{term}**:' has no definition line (next non-empty line should be the definition).",
                )
            else:
                # Length heuristic: definition should be <= 200 chars (one sentence-ish)
                if len(definition) > 200:
                    add(
                        "term-definition-length",
                        "WARN",
                        f"Term '**{term}**' definition is {len(definition)} chars. CONTEXT-FORMAT.md asks for one sentence max.",
                    )
            # Rule 6: _Avoid_ line
            if not avoid:
                add(
                    "term-avoid",
                    "WARN",
                    f"Term '**{term}**' has no '_Avoid_:' aliases line. Without forbidden aliases, the glossary can't push back on drift.",
                )

    # Rule 7: Relationships section
    if "relationships" not in sections:
        add(
            "relationships-section",
            "WARN",
            "No '## Relationships' section found. CONTEXT-FORMAT.md asks for one to show cardinality between terms.",
        )
    else:
        add("relationships-section", "PASS", "'## Relationships' section found.")

    # Rule 8: Example dialogue
    if "example dialogue" not in sections:
        add(
            "example-dialogue",
            "WARN",
            "No '## Example dialogue' section found. CONTEXT-FORMAT.md asks for a dev/domain-expert exchange.",
        )
    else:
        add("example-dialogue", "PASS", "'## Example dialogue' section found.")

    # Rule 9: Flagged ambiguities (optional, only check presence)
    if "flagged ambiguities" in sections:
        add("flagged-ambiguities", "PASS", "'## Flagged ambiguities' section found (optional but useful).")

    return finalize(findings)


def finalize(findings: List[Dict[str, str]]) -> Dict[str, Any]:
    counts = {"PASS": 0, "WARN": 0, "FAIL": 0}
    for f in findings:
        counts[f["level"]] += 1
    if counts["FAIL"] > 0:
        verdict = "FAIL"
    elif counts["WARN"] > 0:
        verdict = "WARN"
    else:
        verdict = "PASS"
    return {"verdict": verdict, "counts": counts, "findings": findings}


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    verdict = result["verdict"]
    counts = result["counts"]
    out.append(f"CONTEXT.md lint verdict: {verdict}")
    out.append(f"  PASS: {counts['PASS']}  WARN: {counts['WARN']}  FAIL: {counts['FAIL']}")
    out.append("")
    out.append("Findings:")
    for f in result["findings"]:
        marker = {"PASS": "[ok]", "WARN": "[warn]", "FAIL": "[FAIL]"}[f["level"]]
        out.append(f"  {marker} {f['rule']}: {f['message']}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("path", nargs="?", help="Path to CONTEXT.md")
    parser.add_argument("--sample", action="store_true", help="Lint the embedded sample CONTEXT.md")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        text = SAMPLE_CONTEXT_MD
    elif args.path:
        p = Path(args.path)
        if not p.exists():
            print(f"error: {args.path} not found", file=sys.stderr)
            return 2
        text = p.read_text(encoding="utf-8")
    else:
        parser.print_help()
        return 0

    result = lint(text)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0 if result["verdict"] != "FAIL" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
