#!/usr/bin/env python3
"""
cheat_code_filter.py — filter the claude-coach cheat-code glossary by use case.

Reads references/cheat-codes.md, parses tiered technique entries, and returns
the top-N matches scored against a user's stated use cases (writing, coding,
research, learning, business, etc.). Stdlib-only.

Usage:
    python3 cheat_code_filter.py --use-cases "writing,coding" --top 7
    python3 cheat_code_filter.py --use-cases "research" --json
    python3 cheat_code_filter.py --sample
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Iterable

USE_CASE_KEYWORDS: dict[str, tuple[str, ...]] = {
    "writing": ("write", "draft", "tone", "audience", "rewrite", "edit", "voice", "format"),
    "coding": ("code", "function", "bug", "debug", "review", "test", "refactor", "stack"),
    "research": ("research", "search", "source", "cite", "summary", "synthes", "compare"),
    "learning": ("explain", "teach", "concept", "understand", "tutorial", "learn"),
    "business": ("plan", "strategy", "memo", "decision", "tradeoff", "stakeholder", "report"),
    "data": ("json", "table", "structured", "parse", "format", "schema", "extract"),
}

DEFAULT_GLOSSARY = Path(__file__).resolve().parent.parent / "references" / "cheat-codes.md"

TIER_HEADING = re.compile(r"^##\s+Tier\s+(\d+)", re.IGNORECASE)
TECHNIQUE_HEADING = re.compile(r"^###\s+(?P<title>.+?)\s*\((?P<level>Beginner|Intermediate|Advanced)\)\s*$", re.IGNORECASE)
EXAMPLE_LINE = re.compile(r"^\*\*Example:\*\*\s+(?P<text>.+)$")


@dataclass
class Technique:
    title: str
    level: str
    tier: int
    explanation: str
    example: str
    score: float = 0.0


def parse_glossary(path: Path) -> list[Technique]:
    if not path.exists():
        raise FileNotFoundError(f"Glossary not found at {path}")
    techniques: list[Technique] = []
    current_tier = 99
    current: Technique | None = None
    lines = path.read_text(encoding="utf-8").splitlines()
    for line in lines:
        tier_match = TIER_HEADING.match(line)
        if tier_match:
            current_tier = int(tier_match.group(1))
            continue
        tech_match = TECHNIQUE_HEADING.match(line)
        if tech_match:
            if current is not None:
                techniques.append(current)
            current = Technique(
                title=tech_match.group("title").strip(),
                level=tech_match.group("level").capitalize(),
                tier=current_tier,
                explanation="",
                example="",
            )
            continue
        if current is None:
            continue
        ex_match = EXAMPLE_LINE.match(line)
        if ex_match:
            current.example = ex_match.group("text").strip()
            continue
        if line.strip() and not line.startswith("---") and not line.startswith("##"):
            if not current.explanation:
                current.explanation = line.strip()
    if current is not None:
        techniques.append(current)
    return techniques


def score_technique(tech: Technique, use_cases: Iterable[str]) -> float:
    text = f"{tech.title} {tech.explanation} {tech.example}".lower()
    score = 0.0
    matched_use_cases = 0
    for uc in use_cases:
        uc = uc.strip().lower()
        keywords = USE_CASE_KEYWORDS.get(uc, (uc,))
        hits = sum(1 for kw in keywords if kw in text)
        if hits:
            matched_use_cases += 1
            score += hits
    tier_weight = max(0.0, 6 - tech.tier) * 1.5
    level_weight = {"Beginner": 2.0, "Intermediate": 1.0, "Advanced": 0.5}.get(tech.level, 1.0)
    return score + tier_weight + level_weight + matched_use_cases * 0.5


def rank(techniques: list[Technique], use_cases: list[str], top: int) -> list[Technique]:
    for tech in techniques:
        tech.score = score_technique(tech, use_cases)
    techniques.sort(key=lambda t: (-t.score, t.tier, t.title))
    return techniques[:top]


def render_human(picks: list[Technique]) -> str:
    if not picks:
        return "No techniques matched the supplied use cases."
    out: list[str] = []
    for tech in picks:
        out.append(f"- **{tech.title}** ({tech.level}) — {tech.explanation}")
        if tech.example:
            out.append(f"  _{tech.example}_")
    return "\n".join(out)


def sample_run(as_json: bool = False) -> int:
    sample_path = DEFAULT_GLOSSARY
    if not sample_path.exists():
        print("Sample glossary not found; place references/cheat-codes.md alongside this script.", file=sys.stderr)
        return 1
    use_cases = ["writing", "coding"]
    picks = rank(parse_glossary(sample_path), use_cases, 5)
    if as_json:
        print(json.dumps({"use_cases": use_cases, "picks": [asdict(t) for t in picks]}, indent=2))
        return 0
    print(render_human(picks))
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Filter cheat-codes.md by use cases.")
    parser.add_argument("--glossary", type=Path, default=DEFAULT_GLOSSARY, help="Path to cheat-codes.md")
    parser.add_argument("--use-cases", type=str, default="", help="Comma-separated use cases (writing,coding,research,learning,business,data)")
    parser.add_argument("--top", type=int, default=7, help="Number of techniques to return (default 7)")
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of human-readable text")
    parser.add_argument("--sample", action="store_true", help="Run on the bundled glossary with sample use cases")
    args = parser.parse_args(argv)

    if args.sample:
        return sample_run(args.json)

    if not args.use_cases:
        parser.error("--use-cases is required unless --sample is passed")

    use_cases = [u.strip() for u in args.use_cases.split(",") if u.strip()]
    try:
        techniques = parse_glossary(args.glossary)
    except FileNotFoundError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    picks = rank(techniques, use_cases, args.top)

    if args.json:
        print(json.dumps({"use_cases": use_cases, "picks": [asdict(t) for t in picks]}, indent=2))
    else:
        print(render_human(picks))
    return 0


if __name__ == "__main__":
    sys.exit(main())
