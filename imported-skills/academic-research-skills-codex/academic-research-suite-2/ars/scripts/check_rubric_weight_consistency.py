#!/usr/bin/env python3
"""#396 lint — reviewer rubric weights must agree across files, single-sourced.

The Originality weight drifted between two reviewer reference docs
(quality_rubrics.md said 20%, review_criteria_framework.md said 15%) and
nothing caught it. The reconciliation (issue #396) made
`academic-paper-reviewer/references/quality_rubrics.md` the single source
of truth for aggregation weights; this lint keeps it that way.

Invariants enforced:
  1. quality_rubrics.md dimension-header weights ("## Dimension N: X
     (Weight: NN%)") match the terms of its own Aggregation Formula
     ("(X x 0.NN)"), dimension by dimension.
  2. The weighted-dimension weights sum to exactly 100%.
  3. academic-paper/SKILL.md rule 14 ("Five dimensions — X (NN%), ...")
     states the same five weights as quality_rubrics.md.
  4. review_criteria_framework.md does NOT restate any weight — no
     "Weight NN%" / "Weight: NN%" header suffix and no "(NN%)" formula
     term may reappear there (it defers to quality_rubrics.md by name).

Exit codes:
  0 = consistent
  1 = drift detected (prints each mismatch)
  2 = could not parse an expected anchor (file move / heading rename /
      regex break) — fail loud, never skip silently
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


RUBRICS_REL = Path("academic-paper-reviewer/references/quality_rubrics.md")
FRAMEWORK_REL = Path("academic-paper-reviewer/references/review_criteria_framework.md")
PAPER_SKILL_REL = Path("academic-paper/SKILL.md")

# The aggregation formula abbreviates dimension names; map the short formula
# token to the canonical dimension-header name.
FORMULA_ALIASES = {
    "Originality": "Originality",
    "Methodology": "Methodological Rigor",
    "Evidence": "Evidence Sufficiency",
    "Coherence": "Argument Coherence",
    "Writing": "Writing Quality",
}

HEADER_RE = re.compile(
    r"^##\s*Dimension\s+\d+:\s*(?P<name>[^(\n]+?)\s*\(Weight:\s*(?P<pct>\d+)%\)",
    re.MULTILINE,
)
FORMULA_TERM_RE = re.compile(r"\(\s*(?P<name>[A-Za-z ]+?)\s*x\s*0\.(?P<frac>\d+)\s*\)")
SKILL_RULE_RE = re.compile(
    r"\*\*Five dimensions\*\*\s*—\s*(?P<body>[^\n]+)", re.MULTILINE
)
SKILL_TERM_RE = re.compile(r"(?P<name>[A-Za-z][A-Za-z &]*?)\s*\((?P<pct>\d+)%\)")
# Any weight restatement in the framework doc: a "Weight NN%" phrase or a bare
# "(NN%)" aggregation-style term.
FRAMEWORK_FORBIDDEN_RE = re.compile(r"Weight\s*:?\s*\d+\s*%|\(\s*\d+\s*%\s*\)")


def _parse_rubrics_headers(text: str) -> dict[str, int]:
    found = {m.group("name").strip(): int(m.group("pct")) for m in HEADER_RE.finditer(text)}
    if not found:
        raise RuntimeError(
            "no '## Dimension N: <name> (Weight: NN%)' headers found in quality_rubrics.md"
        )
    return found


def _parse_rubrics_formula(text: str) -> dict[str, int]:
    anchor = text.find("## Aggregation Formula")
    if anchor < 0:
        raise RuntimeError("'## Aggregation Formula' heading not found in quality_rubrics.md")
    terms: dict[str, int] = {}
    for m in FORMULA_TERM_RE.finditer(text, anchor):
        short = m.group("name").strip()
        canonical = FORMULA_ALIASES.get(short)
        if canonical is None:
            raise RuntimeError(
                f"formula term '{short}' has no alias mapping — update FORMULA_ALIASES"
            )
        frac = m.group("frac")
        terms[canonical] = round(int(frac) * 100 / (10 ** len(frac)))
    if not terms:
        raise RuntimeError("no '(<name> x 0.NN)' terms found under Aggregation Formula")
    return terms


def _parse_skill_rule(text: str) -> dict[str, int]:
    m = SKILL_RULE_RE.search(text)
    if not m:
        raise RuntimeError("'**Five dimensions** —' rule not found in academic-paper/SKILL.md")
    found = {
        t.group("name").strip(): int(t.group("pct"))
        for t in SKILL_TERM_RE.finditer(m.group("body"))
    }
    if not found:
        raise RuntimeError("no '<name> (NN%)' terms found in the Five dimensions rule")
    return found


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="repo root (tests point this at a fake tree)",
    )
    args = parser.parse_args(argv)

    try:
        paper_skill_rel = (
            Path("academic-paper/WORKFLOW.md")
            if (args.root / "academic-paper/WORKFLOW.md").is_file()
            else PAPER_SKILL_REL
        )
        rubrics_text = (args.root / RUBRICS_REL).read_text(encoding="utf-8")
        framework_text = (args.root / FRAMEWORK_REL).read_text(encoding="utf-8")
        skill_text = (args.root / paper_skill_rel).read_text(encoding="utf-8")
        headers = _parse_rubrics_headers(rubrics_text)
        formula = _parse_rubrics_formula(rubrics_text)
        skill_weights = _parse_skill_rule(skill_text)
    except (OSError, RuntimeError) as exc:
        print(f"PARSE ERROR: {exc}", file=sys.stderr)
        return 2

    errors: list[str] = []

    # Invariant 1: headers vs formula (formula terms define the weighted set).
    for name, pct in sorted(formula.items()):
        if name not in headers:
            errors.append(f"formula dimension '{name}' has no (Weight: NN%) header")
        elif headers[name] != pct:
            errors.append(
                f"'{name}': header says {headers[name]}%, formula says {pct}%"
            )
    weighted_headers = {n: p for n, p in headers.items() if n in formula}
    for name in sorted(set(headers) - set(formula)):
        errors.append(f"header dimension '{name}' missing from the aggregation formula")

    # Invariant 2: weights sum to 100.
    total = sum(formula.values())
    if total != 100:
        errors.append(f"formula weights sum to {total}%, expected 100%")

    # Invariant 3: academic-paper SKILL.md rule 14 agrees.
    if skill_weights != weighted_headers and skill_weights != formula:
        errors.append(
            "academic-paper/SKILL.md Five-dimensions rule disagrees with "
            f"quality_rubrics.md: SKILL.md={skill_weights}, rubrics={formula}"
        )

    # Invariant 4: framework doc restates no weights.
    m = FRAMEWORK_FORBIDDEN_RE.search(framework_text)
    if m:
        errors.append(
            "review_criteria_framework.md restates a weight "
            f"('{m.group(0)}') — it must defer to quality_rubrics.md (issue #396)"
        )

    if errors:
        for e in errors:
            print(f"DRIFT: {e}", file=sys.stderr)
        return 1

    print(
        "rubric weights consistent: "
        + ", ".join(f"{n} {p}%" for n, p in sorted(formula.items()))
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
