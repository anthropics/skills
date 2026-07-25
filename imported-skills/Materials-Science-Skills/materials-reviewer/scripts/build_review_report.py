#!/usr/bin/env python3
"""Build a structured two-reviewer materials review report."""

from __future__ import annotations

import argparse
from pathlib import Path


def build_report(title: str, journal_family: str) -> str:
    recommendation = "Major Revision"
    return f"""# Simulated Materials Science Peer Review

Manuscript: {title}
Target journal family: {journal_family}

## Reviewer A

Overall assessment: {recommendation}.

Scores:

- Innovation and contribution: 3/5
- Methodology soundness: 3/5
- Evidence completeness: 2/5
- Writing quality: 3/5
- Figure/table quality: 3/5
- Journal fit: 3/5

Major comments:

1. Severity: Major. The novelty statement needs a sharper comparison with recent materials literature and existing tack coat or composite systems.
2. Severity: Major. The methods should report material specifications, mixing speed, mixing duration, curing age, and test conditions.
3. Severity: Minor. Define all abbreviations and keep units consistent in figure axes.

Recommendation: {recommendation}. The work may be publishable after evidence gaps and method reproducibility issues are addressed.

## Reviewer B

Overall assessment: {recommendation}.

Scores:

- Innovation and contribution: 3/5
- Methodology soundness: 2/5
- Evidence completeness: 2/5
- Writing quality: 3/5
- Figure/table quality: 2/5
- Journal fit: 3/5

Major comments:

1. Severity: Critical. Mechanism claims require direct support from FTIR, SEM, fluorescence, rheology, XRD, TG/DTG, or another complementary technique.
2. Severity: Major. Performance figures should define error bars, replicate count, and conditioning protocols.
3. Severity: Minor. Captions should state what each figure supports and what remains hypothetical.

Recommendation: {recommendation}. The manuscript needs stronger mechanism-evidence linkage and figure/statistics cleanup.

## Cross-review synthesis

Agreed issues:

- Both reviewers flag evidence completeness and method reporting as the main barriers.
- Both reviewers require clearer boundaries between measured performance and inferred mechanism.

Disagreed issues:

- Reviewer A is more concerned with novelty positioning.
- Reviewer B is more concerned with figures, statistics, and mechanism support.

Combined recommendation: {recommendation}. Highest priority revisions are evidence-chain strengthening, reproducible methods, and reviewer-safe figure captions.
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--title", required=True)
    parser.add_argument("--journal-family", default="CBM")
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(build_report(args.title, args.journal_family), encoding="utf-8")
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
