#!/usr/bin/env python3
"""complexity_estimator.py — Recommend full-4-section vs compressed output.

Stdlib-only. Counts non-empty items in a dump, detects clustering signal
(repeated keywords across items), and recommends one of:

  format=full        →  use the full Projects/Tasks/Connections/How-I-Can-Help
                        4-section format (8+ items AND clustering signal)
  format=compressed  →  use the compressed What-I-heard / How-I-can-help
                        format (≤5 items OR no clustering signal)

The recommendation is HEURISTIC. The capture skill applies judgment on top
based on full dump context. Use this as the seed.

NO LLM CALLS. Pure word counting + frequency analysis.

Usage:
    python complexity_estimator.py path/to/dump.txt
    python complexity_estimator.py path/to/dump.txt --output json
    python complexity_estimator.py --sample
"""

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Dict, List


SAMPLE_DUMP_LARGE = """Ok dump time.
Q3 launch needs pricing nailed down.
Draft the Q3 launch email.
Brief Sarah on the Q3 marketing angle.
Decide: launch July 15 or August 1?
Ferret app idea keeps nagging me.
Should I talk to my cofounder about ferret app?
Sketch the ferret matching algorithm if serious.
Decide: ferret app serious or shelf?
Fix the auth bug.
Rewrite the login form (ugly).
Write tests for auth + login.
Add 2fa module to auth.
Do my Q3 OKRs before launch.
"""

SAMPLE_DUMP_SMALL = """Email Sarah.
Fix the flaky test.
Decide: Postgres or Mongo for new service.
Dentist appointment.
Finish reading the RAG article.
"""


# Stop-words to exclude from clustering detection
STOP_WORDS = {
    "a", "an", "the", "is", "are", "was", "were", "be", "been", "being",
    "to", "of", "in", "on", "at", "for", "with", "by", "from", "up", "down",
    "and", "or", "but", "if", "then", "else", "so", "as",
    "i", "you", "he", "she", "it", "we", "they", "me", "my", "your", "our",
    "this", "that", "these", "those", "do", "did", "have", "has", "had",
    "will", "would", "should", "could", "can", "may", "might",
    "what", "when", "where", "why", "how", "who", "which",
    "go", "get", "got", "make", "made", "let", "let's", "yeah", "ok", "well",
    "just", "really", "very", "much", "more", "most", "some", "any",
    "not", "no", "yes", "now", "before", "after",
}


def extract_items(text: str) -> List[str]:
    """Return non-empty stripped lines (each line = one item)."""
    return [line.strip() for line in text.splitlines() if line.strip()]


def extract_keywords(items: List[str]) -> List[str]:
    """Return all alphabetic tokens >= 3 chars, lowercased, stop-words removed."""
    tokens: List[str] = []
    for it in items:
        for tok in re.findall(r"\b[A-Za-z][a-zA-Z]{2,}\b", it):
            t = tok.lower()
            if t in STOP_WORDS:
                continue
            tokens.append(t)
    return tokens


def detect_clusters(items: List[str], min_cluster_size: int) -> List[Dict[str, Any]]:
    """A 'cluster' is a keyword that appears in min_cluster_size+ different items."""
    keyword_to_item_indices: Dict[str, List[int]] = {}
    for i, it in enumerate(items):
        seen_in_item: set = set()
        for tok in re.findall(r"\b[A-Za-z][a-zA-Z]{2,}\b", it):
            t = tok.lower()
            if t in STOP_WORDS or t in seen_in_item:
                continue
            seen_in_item.add(t)
            keyword_to_item_indices.setdefault(t, []).append(i)
    clusters: List[Dict[str, Any]] = []
    for kw, idxs in keyword_to_item_indices.items():
        if len(idxs) >= min_cluster_size:
            clusters.append({"keyword": kw, "item_indices": idxs, "size": len(idxs)})
    clusters.sort(key=lambda c: (-c["size"], c["keyword"]))
    return clusters


def estimate(text: str, min_cluster_size: int = 3) -> Dict[str, Any]:
    items = extract_items(text)
    item_count = len(items)
    clusters = detect_clusters(items, min_cluster_size)
    cluster_count = len(clusters)

    # Decision logic per references/complexity_matching.md
    if item_count >= 8 and cluster_count >= 1:
        recommendation = "full"
        rationale = f"{item_count} items with {cluster_count} cluster(s) of {min_cluster_size}+ → full 4-section format"
    elif item_count >= 8 and cluster_count == 0:
        recommendation = "compressed"
        rationale = f"{item_count} items but no clustering signal → compressed (with 'no clusters' note)"
    elif 5 <= item_count <= 7 and cluster_count >= 1:
        recommendation = "full"
        rationale = f"{item_count} items with clustering signal → judgment call, defaulting full"
    elif 5 <= item_count <= 7 and cluster_count == 0:
        recommendation = "compressed"
        rationale = f"{item_count} items, no clustering → compressed"
    elif item_count <= 5:
        recommendation = "compressed"
        rationale = f"{item_count} items (small dump) → compressed"
    else:
        recommendation = "compressed"
        rationale = "fallback → compressed"

    return {
        "item_count": item_count,
        "cluster_count": cluster_count,
        "clusters": clusters[:5],  # top 5 only in output for readability
        "recommendation": recommendation,
        "rationale": rationale,
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Item count:       {result['item_count']}")
    out.append(f"Cluster count:    {result['cluster_count']}")
    out.append(f"Recommendation:   format={result['recommendation']}")
    out.append(f"Rationale:        {result['rationale']}")
    if result["clusters"]:
        out.append("")
        out.append("Top clusters (keyword → items containing it):")
        for c in result["clusters"]:
            out.append(f"  - '{c['keyword']}' in {c['size']} items: lines {c['item_indices']}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("path", nargs="?", help="Path to dump file")
    parser.add_argument("--sample", choices=["large", "small"], help="Estimate the embedded sample dump (large or small)")
    parser.add_argument("--min-cluster-size", type=int, default=3, help="Minimum items sharing a keyword to count as a cluster (default: 3)")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        text = SAMPLE_DUMP_LARGE if args.sample == "large" else SAMPLE_DUMP_SMALL
    elif args.path:
        p = Path(args.path)
        if not p.exists():
            print(f"error: {args.path} not found", file=sys.stderr)
            return 2
        text = p.read_text(encoding="utf-8")
    else:
        parser.print_help()
        return 0

    result = estimate(text, args.min_cluster_size)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
