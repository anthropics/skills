#!/usr/bin/env python3
"""Audit sentence length and reviewer-risk language in materials prose."""

from __future__ import annotations

import argparse
import csv
import re
import sys
from pathlib import Path


RISK_RULES = [
    ("overclaim-proof", r"\b(prove|proved|proves|confirm|confirmed|demonstrate|demonstrated)\b", "Use only with direct evidence; otherwise use suggest/indicate/show."),
    ("absolute", r"\b(completely|fully|perfectly|entirely|always|never)\b", "Absolute wording is rarely reviewer-safe."),
    ("unsupported-sustainability", r"\b(environmentally friendly|green|eco-friendly|sustainable)\b", "State LCA/resource/emission boundary or soften the claim."),
    ("novelty-priority", r"\b(first|novel|new|unprecedented)\b", "Requires live literature support or a precise gap statement."),
    ("statistics", r"\b(significant|significantly)\b", "Use only when statistical significance is reported."),
    ("vague-quality", r"\b(excellent|good|obvious|remarkable|superior)\b", "Replace vague praise with measured comparison."),
    ("mechanism-risk", r"\b(mechanism was confirmed|confirmed the mechanism|proved the mechanism)\b", "Mechanism confirmation needs direct mechanism evidence."),
]

# Suggestion rules: label -> list of (compiled_regex, replacement) pairs
# Each rule is applied in order; replacements are case-insensitive.
_SUGGEST_PATTERNS: dict[str, list[tuple[re.Pattern, str]]] = {
    "overclaim-proof": [
        (re.compile(r"\bproves\b", re.I), "provides evidence for"),
        (re.compile(r"\bprove\b", re.I), "provide evidence for"),
        (re.compile(r"\bproved\b", re.I), "provided evidence for"),
        (re.compile(r"\bdemonstrates\b", re.I), "suggests"),
        (re.compile(r"\bdemonstrated\b", re.I), "suggested"),
        (re.compile(r"\bdemonstrate\b", re.I), "suggest"),
        (re.compile(r"\bconfirms\b", re.I), "is consistent with"),
        (re.compile(r"\bconfirmed\b", re.I), "was consistent with"),
        (re.compile(r"\bconfirm\b", re.I), "be consistent with"),
    ],
    "absolute": [
        (re.compile(r"\balways\b", re.I), "typically"),
        (re.compile(r"\bnever\b", re.I), "rarely observed"),
        (re.compile(r"\bcompletely\b", re.I), "largely"),
        (re.compile(r"\bfully\b", re.I), "substantially"),
        (re.compile(r"\bperfectly\b", re.I), "highly"),
        (re.compile(r"\bentirely\b", re.I), "predominantly"),
    ],
    "unsupported-sustainability": [
        (re.compile(r"\bsustainable\b", re.I), "with potential for reduced environmental impact"),
        (re.compile(r"\benvironmentally friendly\b", re.I), "with potential for reduced environmental impact"),
        (re.compile(r"\beco-friendly\b", re.I), "with potential for reduced environmental impact"),
        (re.compile(r"\bgreen\b", re.I), "potentially lower-impact"),
    ],
    "novelty-priority": [
        (re.compile(r"\bfirst time\b", re.I), "to our knowledge, among the first"),
        (re.compile(r"\bfirst\b", re.I), "to our knowledge, among the first"),
        (re.compile(r"\bnovel\b", re.I), "previously unreported"),
        (re.compile(r"\bunprecedented\b", re.I), "rarely explored"),
    ],
    "vague-quality": [
        (re.compile(r"\bexcellent\b", re.I), "significant improvement (Δ = X%)"),
        (re.compile(r"\bremarkable\b", re.I), "notable (Δ = X%)"),
        (re.compile(r"\bsuperior\b", re.I), "higher (quantify: X vs Y)"),
        (re.compile(r"\bobvious\b", re.I), "measurable"),
        (re.compile(r"\bgood\b", re.I), "measurable"),
    ],
    "statistics": [
        # No text replacement; the suggestion is an advisory note appended below.
    ],
    "mechanism-risk": [
        (re.compile(r"\bconfirmed the mechanism\b", re.I), "is consistent with the proposed mechanism"),
        (re.compile(r"\bmechanism was confirmed\b", re.I), "the mechanism is supported by the data"),
        (re.compile(r"\bproved the mechanism\b", re.I), "is consistent with the proposed mechanism"),
    ],
}

# Advisory notes appended for categories where a simple text swap is insufficient.
_SUGGEST_NOTES: dict[str, str] = {
    "statistics": "Consider adding ± SD or n = N to substantiate the claim.",
}


def split_sentences(text: str) -> list[str]:
    return [s.strip() for s in re.split(r"(?<=[.!?])\s+", text) if s.strip()]


def audit_sentence(sentence: str, max_words: int) -> dict[str, str] | None:
    words = re.findall(r"[A-Za-z0-9%./-]+", sentence)
    flags: list[str] = []
    advice: list[str] = []
    if len(words) > max_words:
        flags.append("long-sentence")
        advice.append(f"Split or tighten; {len(words)} words exceeds {max_words}.")
    lower = sentence.lower()
    for label, pattern, message in RISK_RULES:
        if re.search(pattern, lower):
            flags.append(label)
            advice.append(message)
    if not flags:
        return None
    return {
        "words": str(len(words)),
        "flags": ";".join(flags),
        "advice": " ".join(advice),
        "sentence": sentence,
    }


def suggest_rewrite(sentence: str, flags: list[str]) -> str:
    """Generate a suggested rewrite for a sentence based on its flagged risk categories."""
    result = sentence
    notes: list[str] = []

    for label in flags:
        if label == "long-sentence":
            continue
        patterns = _SUGGEST_PATTERNS.get(label)
        if patterns:
            for regex, replacement in patterns:
                result = regex.sub(replacement, result)
        note = _SUGGEST_NOTES.get(label)
        if note:
            notes.append(note)

    if notes:
        result = result + " [" + " ".join(notes) + "]"

    return result


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", help="UTF-8 text file to audit")
    parser.add_argument("--max-words", type=int, default=30)
    parser.add_argument("--format", choices=["text", "csv"], default="text")
    parser.add_argument("--output", help="Optional output path for CSV format.")
    parser.add_argument(
        "--suggest",
        action="store_true",
        default=False,
        help="Enable suggested rewrites for flagged risk language. "
        "Adds 'suggested_rewrite' column (CSV) or 'suggestion' field (text).",
    )
    args = parser.parse_args()

    text = Path(args.file).read_text(encoding="utf-8-sig")
    rows = []
    for idx, sentence in enumerate(split_sentences(text), 1):
        row = audit_sentence(sentence, args.max_words)
        if row:
            row["sentence_id"] = str(idx)
            if args.suggest:
                flag_list = row["flags"].split(";")
                row["suggested_rewrite"] = suggest_rewrite(sentence, flag_list)
            rows.append(row)
    if args.format == "csv":
        output = Path(args.output or "materials-language-audit.csv")
        fieldnames = ["sentence_id", "words", "flags", "advice", "sentence"]
        if args.suggest:
            fieldnames.append("suggested_rewrite")
        with output.open("w", encoding="utf-8-sig", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)
        print(output)
        return 0
    for row in rows:
        print(f"Sentence {row['sentence_id']}: words={row['words']} flags={row['flags']}")
        print(row["advice"])
        print(row["sentence"])
        if args.suggest:
            print(f"  -> Suggested: {row['suggested_rewrite']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
