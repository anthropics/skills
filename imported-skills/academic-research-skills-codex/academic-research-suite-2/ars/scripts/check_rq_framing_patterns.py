#!/usr/bin/env python3
"""Calibration checker for the #257 Socratic wording-pattern advisory.

The detector is intentionally lexical and conservative. It is not a novelty
model and does not judge research quality; it only checks whether a proposed RQ
uses one of the common surface shells documented in the Socratic mentor prompts.
"""
from __future__ import annotations

import argparse
import json
import re
import string
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_GOLD_SET = REPO_ROOT / "evals/gold/rq_framing_patterns/gold_set.json"
POSITIVE_LABEL = "wording_cliche"
NEGATIVE_LABEL = "domain_native"

_PUNCT_TRANSLATION = str.maketrans({c: " " for c in string.punctuation})


@dataclass(frozen=True)
class PatternSpec:
    pattern_id: str
    label: str
    regex: re.Pattern[str]


def _rx(pattern: str) -> re.Pattern[str]:
    return re.compile(pattern, re.IGNORECASE)


REFERENCE_PATTERNS: tuple[PatternSpec, ...] = (
    PatternSpec("WP01", "impact/effect frame", _rx(r"\b(?:explor\w*|investigat\w*|examin\w*|analyz\w*|study\w*)\s+(?:the\s+)?(?:impact|effect)s?\s+of\b.+\bon\b")),
    PatternSpec("WP02", "relationship frame", _rx(r"\b(?:investigat\w*|examin\w*|explor\w*)?\s*(?:the\s+)?(?:relationship|association|correlation)\s+between\b")),
    PatternSpec("WP03", "role frame", _rx(r"\b(?:understand\w*|examin\w*|investigat\w*|explor\w*|analyz\w*|assess\w*)\s+(?:the\s+)?role\s+of\b.+\bin\b")),
    PatternSpec("WP04", "influence frame", _rx(r"\b(?:analyz\w*|investigat\w*|examin\w*|explor\w*)\s+how\b.+\b(?:influences?|affects?)\b")),
    PatternSpec("WP05", "generic factors frame", _rx(r"\b(?:explor\w*|investigat\w*|examin\w*|analyz\w*)?\s*factors\s+(?:influencing|affecting|that\s+influence|that\s+affect)\b")),
    PatternSpec("WP06", "bare study-of frame", _rx(r"^(?:a|an|the)\s+(?:\w+\s+)?study\s+of\b")),
    PatternSpec("WP07", "impact case-study frame", _rx(r"\bimpact\s+of\b.+\bon\b.+\bcase\s+study\b|\bcase\s+study\b.+\bimpact\s+of\b")),
    PatternSpec("WP08", "challenges/opportunities pair", _rx(r"\bchallenges\s+and\s+opportunities\s+of\b")),
    PatternSpec("WP09", "perception/attitude survey frame", _rx(r"\b(?:perceptions|attitudes)\s+(?:of\b.+\s+)?(?:toward|towards|about)\b")),
    PatternSpec("WP10", "performance/achievement effect frame", _rx(r"\b(?:the\s+)?effect\s+of\b.+\bon\b.+\b(?:performance|achievement|satisfaction|outcomes?)\b")),
    PatternSpec("WP11", "achievement relationship frame", _rx(r"\brelationship\s+between\b.+\band\b.+\b(?:performance|achievement|outcomes?)\b")),
    PatternSpec("WP12", "generic use/application frame", _rx(r"\b(?:explor\w*|investigat\w*|examin\w*|analyz\w*|assess\w*)\s+(?:the\s+)?(?:use|application|implementation)\s+of\b.+\bin\b")),
    PatternSpec("WP13", "effectiveness frame", _rx(r"\b(?:investigat\w*|examin\w*|evaluat\w*)?\s*(?:the\s+)?effectiveness\s+of\b.+\b(?:for|in|on)\b")),
    PatternSpec("WP14", "mediator/moderator template", _rx(r"\b(?:mediating|moderating)\s+role\s+of\b")),
    PatternSpec("WP15", "adoption/intention/satisfaction factors", _rx(r"\bfactors\s+affecting\b.+\b(?:adoption|intention|satisfaction)\b")),
    PatternSpec("WP16", "barriers/facilitators pair", _rx(r"\bbarriers\s+and\s+facilitators\s+to\b")),
    PatternSpec("WP17", "comparative-study shell", _rx(r"\bcomparative\s+study\s+of\b")),
    PatternSpec("WP18", "framework/model shell", _rx(r"\btowards?\s+a\s+(?:framework|model)\s+for\b")),
    PatternSpec("WP19", "technology-enhancement shell", _rx(r"\brole\s+of\s+(?:technology|ai|artificial\s+intelligence|digital\s+tools)\b.+\benhanc\w*\b")),
    PatternSpec("WP20", "experience-of frame", _rx(r"\b(?:explor\w*|investigat\w*|examin\w*)?\s*(?:the\s+)?experiences\s+of\b.+\b(?:in|with|during)\b")),
)


def normalize(text: str) -> str:
    return " ".join(text.lower().translate(_PUNCT_TRANSLATION).split())


def analyze_framing(text: str) -> dict[str, Any]:
    normalized = normalize(text)
    matches = [spec for spec in REFERENCE_PATTERNS if spec.regex.search(normalized)]
    return {
        "trigger_advisory": bool(matches),
        "matched_pattern_ids": [spec.pattern_id for spec in matches],
        "matched_pattern_labels": [spec.label for spec in matches],
    }


def _load_gold_set(path: Path) -> list[dict[str, Any]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    items = data.get("items")
    if not isinstance(items, list):
        raise ValueError("gold set must contain an items[] list")
    return items


def evaluate_items(items: list[dict[str, Any]]) -> dict[str, Any]:
    tp = tn = fp = fn = 0
    item_results: list[dict[str, Any]] = []
    errors: list[str] = []

    for item in items:
        item_id = item.get("id", "<missing-id>")
        label = item.get("label")
        if label not in {POSITIVE_LABEL, NEGATIVE_LABEL}:
            errors.append(f"{item_id}: invalid label {label!r}")
            continue
        text = item.get("text")
        if not isinstance(text, str) or not text.strip():
            errors.append(f"{item_id}: missing non-empty text")
            continue
        analysis = analyze_framing(text)
        predicted_positive = analysis["trigger_advisory"]
        actual_positive = label == POSITIVE_LABEL
        expected_pattern_ids = item.get("expected_pattern_ids", [])
        if not isinstance(expected_pattern_ids, list):
            errors.append(f"{item_id}: expected_pattern_ids must be a list")
            continue

        matched = set(analysis["matched_pattern_ids"])
        missing_expected = sorted(set(expected_pattern_ids) - matched)
        if actual_positive and missing_expected:
            errors.append(f"{item_id}: expected patterns not matched: {missing_expected}")
        if not actual_positive and matched:
            errors.append(f"{item_id}: domain-native item matched unexpected patterns: {sorted(matched)}")

        if predicted_positive and actual_positive:
            tp += 1
        elif predicted_positive and not actual_positive:
            fp += 1
        elif not predicted_positive and actual_positive:
            fn += 1
        else:
            tn += 1

        item_results.append({
            "id": item_id,
            "label": label,
            "predicted_positive": predicted_positive,
            **analysis,
        })

    positives = tp + fn
    negatives = tn + fp
    fnr = fn / positives if positives else 0.0
    fpr = fp / negatives if negatives else 0.0
    tpr = tp / positives if positives else 0.0
    tnr = tn / negatives if negatives else 0.0
    balanced_accuracy = (tpr + tnr) / 2 if positives and negatives else 0.0

    if len(items) != 40:
        errors.append(f"sample_n must be 40, got {len(items)}")
    if positives != 20 or negatives != 20:
        errors.append(f"gold set must be balanced 20/20, got positives={positives}, negatives={negatives}")
    if fnr >= 0.30:
        errors.append(f"FNR {fnr:.3f} must be < 0.30")
    if fpr >= 0.20:
        errors.append(f"FPR {fpr:.3f} must be < 0.20")
    if balanced_accuracy < 0.75:
        errors.append(f"balanced accuracy {balanced_accuracy:.3f} must be >= 0.75")

    return {
        "counts": {"tp": tp, "tn": tn, "fp": fp, "fn": fn, "positives": positives, "negatives": negatives},
        "metrics": {"fnr": fnr, "fpr": fpr, "balanced_accuracy": balanced_accuracy},
        "item_results": item_results,
        "errors": errors,
    }


def validate_gold_set(path: Path = DEFAULT_GOLD_SET) -> dict[str, Any]:
    return evaluate_items(_load_gold_set(path))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("gold_set", nargs="?", type=Path, default=DEFAULT_GOLD_SET)
    args = parser.parse_args(argv)

    result = validate_gold_set(args.gold_set)
    counts = result["counts"]
    metrics = result["metrics"]
    print(
        "rq_framing_patterns: "
        f"tp={counts['tp']} tn={counts['tn']} fp={counts['fp']} fn={counts['fn']} "
        f"fnr={metrics['fnr']:.3f} fpr={metrics['fpr']:.3f} "
        f"balanced_accuracy={metrics['balanced_accuracy']:.3f}"
    )
    if result["errors"]:
        for error in result["errors"]:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
