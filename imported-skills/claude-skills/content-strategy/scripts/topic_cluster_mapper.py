#!/usr/bin/env python3
"""
topic_cluster_mapper.py — Groups keywords/topics into content clusters
Usage:
  python3 topic_cluster_mapper.py --file keywords.txt
  python3 topic_cluster_mapper.py --json
  python3 topic_cluster_mapper.py          # demo mode (20 marketing topics)
"""

import argparse
import json
import re
import sys
from collections import defaultdict


# ---------------------------------------------------------------------------
# Simple stemmer (no nltk)
# ---------------------------------------------------------------------------

STOP_WORDS = {
    "a", "an", "the", "and", "or", "but", "in", "on", "at", "to", "for",
    "of", "with", "by", "from", "is", "are", "was", "were", "be", "been",
    "how", "what", "why", "when", "where", "who", "which", "that", "this",
    "it", "its", "do", "does", "your", "our", "my", "their", "we", "you",
    "get", "make", "use", "using", "used", "can", "will", "should", "best",
}


def simple_stem(word: str) -> str:
    """Very simple suffix-stripping stemmer."""
    w = word.lower()
    if len(w) <= 3:
        return w
    # Order matters — try longer suffixes first
    suffixes = [
        "ization", "isation", "ational", "fulness", "ousness", "iveness",
        "iveness", "ingness", "ations", "nesses", "ators", "ation",
        "ating", "alism", "ality", "alize", "alise", "ation", "ator",
        "ness", "ment", "less", "tion", "sion", "tion", "ing", "ers",
        "ies", "ied", "ily", "ful", "ous", "ive", "ize", "ise", "est",
        "ed", "er", "ly", "al", "ic", "s",
    ]
    for sfx in suffixes:
        if w.endswith(sfx) and len(w) - len(sfx) >= 3:
            return w[: -len(sfx)]
    return w


def extract_stems(topic: str) -> set:
    words = re.findall(r"\b[a-zA-Z]+\b", topic.lower())
    return {simple_stem(w) for w in words if w not in STOP_WORDS and len(w) > 2}


# ---------------------------------------------------------------------------
# Clustering
# ---------------------------------------------------------------------------

def compute_similarity(stems_a: set, stems_b: set) -> float:
    """Jaccard similarity between two stem sets."""
    if not stems_a or not stems_b:
        return 0.0
    intersection = stems_a & stems_b
    union = stems_a | stems_b
    return len(intersection) / len(union)


def build_clusters(topics: list, threshold: float = 0.15) -> list:
    """
    Greedy clustering: assign each topic to the first cluster it's
    similar-enough to; else start a new cluster.
    """
    # Pre-compute stems
    topic_stems = {t: extract_stems(t) for t in topics}

    clusters = []  # list of {"pillar": str, "topics": [str], "stems": set}

    for topic in topics:
        t_stems = topic_stems[topic]
        best_cluster = None
        best_score = 0.0

        for cluster in clusters:
            sim = compute_similarity(t_stems, cluster["stems"])
            if sim > best_score:
                best_score = sim
                best_cluster = cluster

        if best_cluster and best_score >= threshold:
            best_cluster["topics"].append(topic)
            best_cluster["stems"] |= t_stems  # grow cluster centroid
        else:
            clusters.append({
                "pillar": topic,
                "topics": [topic],
                "stems": set(t_stems),
            })

    # Identify best pillar: topic with most shared stems to others in cluster
    for cluster in clusters:
        if len(cluster["topics"]) == 1:
            continue
        all_stems = [topic_stems[t] for t in cluster["topics"]]
        best_topic = cluster["topics"][0]
        best_conn = 0
        for i, topic in enumerate(cluster["topics"]):
            conn = sum(
                len(topic_stems[topic] & topic_stems[other])
                for j, other in enumerate(cluster["topics"]) if i != j
            )
            if conn > best_conn:
                best_conn = conn
                best_topic = topic
        cluster["pillar"] = best_topic

    return clusters


def build_output(topics: list, clusters: list) -> dict:
    cluster_output = []
    for i, c in enumerate(clusters, 1):
        supporting = [t for t in c["topics"] if t != c["pillar"]]
        cluster_output.append({
            "cluster_id": i,
            "pillar_topic": c["pillar"],
            "size": len(c["topics"]),
            "supporting_topics": supporting,
            "suggested_url_slug": re.sub(r"[^a-z0-9]+", "-", c["pillar"].lower()).strip("-"),
        })

    # Sort by cluster size desc
    cluster_output.sort(key=lambda x: -x["size"])

    return {
        "total_topics": len(topics),
        "total_clusters": len(clusters),
        "clusters": cluster_output,
        "recommendations": _make_recommendations(cluster_output),
    }


def _make_recommendations(clusters: list) -> list:
    recs = []
    large = [c for c in clusters if c["size"] >= 3]
    singletons = [c for c in clusters if c["size"] == 1]

    if large:
        recs.append(f"Create {len(large)} pillar page(s) for clusters with 3+ topics")
    if singletons:
        recs.append(
            f"{len(singletons)} singleton topic(s) — consider merging or expanding to form mini-clusters"
        )
    if clusters:
        biggest = clusters[0]
        recs.append(
            f"Highest-priority cluster: '{biggest['pillar_topic']}' "
            f"({biggest['size']} related topics) — start content here"
        )
    return recs


# ---------------------------------------------------------------------------
# Demo topics
# ---------------------------------------------------------------------------

DEMO_TOPICS = [
    "email marketing strategy",
    "email subject line tips",
    "email open rate optimization",
    "email automation workflows",
    "SEO keyword research",
    "on-page SEO optimization",
    "SEO content strategy",
    "technical SEO audit",
    "social media marketing",
    "social media content calendar",
    "Instagram marketing tips",
    "LinkedIn marketing for B2B",
    "content marketing ROI",
    "content strategy planning",
    "blog content ideas",
    "landing page conversion rate",
    "conversion rate optimization",
    "A/B testing landing pages",
    "paid ads budget allocation",
    "Google Ads campaign setup",
]


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Topic cluster mapper — groups keywords into content clusters."
    )
    parser.add_argument("--file", help="Text file with one topic/keyword per line")
    parser.add_argument("--threshold", type=float, default=0.15,
                        help="Similarity threshold for clustering (default: 0.15)")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    if args.file:
        with open(args.file, "r", encoding="utf-8") as f:
            topics = [line.strip() for line in f if line.strip()]
    else:
        topics = DEMO_TOPICS
        if not args.json:
            print("No input provided — running in demo mode with 20 marketing topics.\n")

    if not topics:
        print("No topics found.", file=sys.stderr)
        sys.exit(1)

    clusters = build_clusters(topics, threshold=args.threshold)
    output = build_output(topics, clusters)

    if args.json:
        print(json.dumps(output, indent=2))
        return

    print("=" * 62)
    print(f"  TOPIC CLUSTER MAP   {output['total_topics']} topics → {output['total_clusters']} clusters")
    print("=" * 62)

    for cluster in output["clusters"]:
        print(f"\n  Cluster {cluster['cluster_id']}  ({cluster['size']} topics)")
        print(f"  ┌─ PILLAR: {cluster['pillar_topic']}")
        print(f"  │  Slug:   /{cluster['suggested_url_slug']}")
        for st in cluster["supporting_topics"]:
            print(f"  └─ Supporting: {st}")

    print("\n" + "=" * 62)
    print("  RECOMMENDATIONS")
    print("=" * 62)
    for rec in output["recommendations"]:
        print(f"  • {rec}")
    print()


if __name__ == "__main__":
    main()
