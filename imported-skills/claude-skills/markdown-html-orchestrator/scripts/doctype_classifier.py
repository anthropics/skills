#!/usr/bin/env python3
"""doctype_classifier.py - Deterministic document-type classifier for markdown-html.

Stdlib-only. Reads a markdown file (or stdin), scans for filename + content signals,
and returns a routing recommendation: document / review / slides / ambiguous.

Routing discipline mirrors research-ops/skills/research-ops-skills/SKILL.md:
  - Two-signal threshold: silent-route when score >= 3 OR (winner >= 2 AND
    winner >= 2x runner-up). Below threshold => ambiguous, ask the user.
  - Filename hint = 2 points; each content signal = 1 point.
  - Never silently chain. The orchestrator (Claude) decides; this script
    just produces a structured recommendation it can act on.

Hard rule from the article: documents below MIN_LINES are NOT candidates for
HTML conversion — markdown still wins. The classifier surfaces a line_count
field and a below_min_lines boolean so the orchestrator can refuse before
routing.

NO LLM CALLS. Pure regex + counting.

Usage:
    python doctype_classifier.py --input report.md --output json
    python doctype_classifier.py --input - --output human  # stdin
    python doctype_classifier.py --sample
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

MIN_LINES = 100  # Shihipar's threshold — markdown wins below this

FILENAME_HINTS: dict[str, list[str]] = {
    "document": [
        r"\breport\b", r"-doc\b", r"\bspec\b", r"^rfc-", r"-analysis\b",
        r"\bexplainer\b", r"\bguide\b", r"\bplan\b",
    ],
    "review": [
        r"\breview\b", r"-pr-", r"\.diff(?:\.md)?$", r"code-review",
        r"\bpr-writeup\b",
    ],
    "slides": [
        r"\bdeck\b", r"\bslides\b", r"-talk\b", r"\bpresentation\b",
        r"\bkeynote\b",
    ],
}

CONTENT_SIGNALS: dict[str, list[tuple[str, str, int]]] = {
    "document": [
        # (regex, description, weight)
        (r"^## Table of Contents", "TOC heading", 2),
        (r"^# .{3,}$", "H1 with title", 1),
        (r"^## .{3,}$", "H2 with title", 1),
        (r"^\| .+\| .+\|$", "markdown table row", 1),
        (r"^> \[!NOTE\]|^> \[!TIP\]|^> \[!IMPORTANT\]", "GFM callout", 1),
    ],
    "review": [
        (r"^```diff\b", "diff fence", 2),
        (r"^[-+]{3} ", "unified-diff file header", 2),
        (r"^@@ .* @@", "unified-diff hunk header", 2),
        (r"^> \[!BLOCKER\]|^> \[!MAJOR\]|^> \[!MINOR\]|^> \[!NIT\]", "severity callout", 2),
        (r"\bLGTM\b|\bnit:|\bblocker:|\bmajor:", "review-vocab inline", 1),
    ],
    "slides": [
        (r"^---\s*$", "HR slide boundary", 1),
        (r"<!--\s*notes:", "presenter notes", 2),
        (r"^# .{3,}$", "H1 (slide title candidate)", 1),
    ],
}


def _score_filename(path: Path) -> dict[str, int]:
    name = path.name.lower()
    out: dict[str, int] = {"document": 0, "review": 0, "slides": 0}
    for cls, patterns in FILENAME_HINTS.items():
        for p in patterns:
            if re.search(p, name):
                out[cls] += 2
                break
    return out


def _score_content(text: str) -> tuple[dict[str, int], dict[str, list[str]]]:
    scores: dict[str, int] = {"document": 0, "review": 0, "slides": 0}
    evidence: dict[str, list[str]] = {"document": [], "review": [], "slides": []}

    lines = text.splitlines()
    for cls, sigs in CONTENT_SIGNALS.items():
        for pattern, label, weight in sigs:
            compiled = re.compile(pattern, re.MULTILINE)
            matches = compiled.findall(text)
            if matches:
                hit_count = len(matches)
                scores[cls] += weight * min(hit_count, 5)  # cap each signal at 5 hits to avoid runaway
                evidence[cls].append(f"{label} x{hit_count}")

    # slides special-case: HR slide boundary count >= 3 is a stronger signal
    hr_count = len(re.findall(r"^---\s*$", text, re.MULTILINE))
    if hr_count >= 3:
        scores["slides"] += 2
        evidence["slides"].append(f"hr boundaries >= 3 (count={hr_count})")

    # slides special-case: many H1s with mostly-empty bodies between
    h1_indices = [i for i, ln in enumerate(lines) if re.match(r"^# .{3,}$", ln)]
    if len(h1_indices) >= 5:
        gaps = [h1_indices[i + 1] - h1_indices[i] for i in range(len(h1_indices) - 1)]
        if gaps and sum(g <= 12 for g in gaps) / len(gaps) >= 0.6:
            scores["slides"] += 2
            evidence["slides"].append(
                f"H1 cadence: {len(h1_indices)} H1s, median gap ~{sorted(gaps)[len(gaps)//2]} lines"
            )

    return scores, evidence


def classify(input_path: Path | None, text: str | None) -> dict[str, Any]:
    if text is None:
        if input_path is None:
            raise ValueError("Need either input_path or text")
        text = input_path.read_text(encoding="utf-8")

    fn_scores = _score_filename(input_path) if input_path else {"document": 0, "review": 0, "slides": 0}
    content_scores, evidence = _score_content(text)
    total = {k: fn_scores[k] + content_scores[k] for k in fn_scores}

    line_count = len(text.splitlines())
    below_min = line_count < MIN_LINES

    # Ranking
    ranked = sorted(total.items(), key=lambda kv: kv[1], reverse=True)
    winner_cls, winner_score = ranked[0]
    runner_cls, runner_score = ranked[1]

    silent_route = (
        winner_score >= 3
        and (runner_score == 0 or winner_score >= 2 * runner_score)
    )

    if winner_score == 0:
        verdict = "ambiguous"
        recommendation = "Ask the user which document type — no signals matched."
    elif silent_route:
        verdict = winner_cls
        recommendation = f"Route to md-{winner_cls} (score {winner_score} vs runner-up {runner_score})."
    elif winner_score >= 2:
        verdict = "needs-clarification"
        recommendation = (
            f"Top candidate is md-{winner_cls} (score {winner_score}) "
            f"but md-{runner_cls} also scored {runner_score} — ask user to confirm."
        )
    else:
        verdict = "ambiguous"
        recommendation = (
            f"Weak signal ({winner_cls}={winner_score}). "
            f"Ask user, or treat as md-document by default."
        )

    return {
        "verdict": verdict,
        "winner": winner_cls,
        "winner_score": winner_score,
        "runner_up": runner_cls,
        "runner_up_score": runner_score,
        "filename_scores": fn_scores,
        "content_scores": content_scores,
        "total_scores": total,
        "evidence": evidence,
        "line_count": line_count,
        "below_min_lines": below_min,
        "min_lines_threshold": MIN_LINES,
        "recommendation": recommendation,
        "silent_route_allowed": silent_route,
    }


def render_human(result: dict[str, Any]) -> str:
    lines = []
    lines.append(f"Doctype classification: {result['verdict']}")
    lines.append(f"  recommendation: {result['recommendation']}")
    lines.append(f"  line count: {result['line_count']} (threshold {result['min_lines_threshold']})")
    if result["below_min_lines"]:
        lines.append(
            f"  ! below threshold — markdown still wins under "
            f"{result['min_lines_threshold']} lines (Shihipar). Recommend keeping as markdown."
        )
    lines.append("")
    lines.append("Scores:")
    for cls in ["document", "review", "slides"]:
        fn = result["filename_scores"][cls]
        ct = result["content_scores"][cls]
        total = result["total_scores"][cls]
        lines.append(f"  md-{cls:<10s} total={total:<3d} (filename={fn}, content={ct})")
    lines.append("")
    lines.append("Evidence:")
    for cls, sigs in result["evidence"].items():
        if sigs:
            lines.append(f"  md-{cls}: {', '.join(sigs)}")
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--input", help="Path to markdown file, or '-' for stdin")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    parser.add_argument("--sample", action="store_true",
                        help="Classify a built-in sample (a Shihipar-style 200-line spec)")
    args = parser.parse_args(argv)

    if args.sample:
        sample_text = SAMPLE_MARKDOWN
        result = classify(None, sample_text)
    elif args.input:
        if args.input == "-":
            text = sys.stdin.read()
            result = classify(None, text)
        else:
            path = Path(args.input)
            if not path.exists():
                print(f"error: input not found: {path}", file=sys.stderr)
                return 2
            result = classify(path, None)
    else:
        parser.print_help()
        return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


SAMPLE_MARKDOWN = """# Implementation Plan: Payment Gateway Integration

## Table of Contents

- Goals
- Architecture
- Risks

## Goals

We will integrate Stripe Connect with the existing checkout flow.

| Phase | Timeline | Owner |
|---|---|---|
| Design | Week 1 | jane |
| Build | Week 2-3 | dev team |
| Ship | Week 4 | jane |

## Architecture

The integration will use webhooks for async events.

> [!NOTE]
> All webhook handlers must be idempotent.

## Risks

1. Webhook delivery delays
2. Tax calculation edge cases
3. Refund cascading
""" + "\n" * 120  # pad to > MIN_LINES


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
