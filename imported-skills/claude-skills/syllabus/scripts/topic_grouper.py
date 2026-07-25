#!/usr/bin/env python3
"""topic_grouper.py — Heuristic 6-12 section grouping from extracted syllabus topics.

Stdlib-only. Given a list of extracted course topics, produce a proposed
grouping into 6-12 sections by detecting shared keywords.

The output feeds the Phase 2 group-and-confirm checkpoint where the user
can override (proceed / merge / split / add / remove).

Algorithm:
  1. Tokenize each topic into significant words (stop-words removed)
  2. Build word → topics inverted index
  3. Greedy clustering: topics sharing 2+ significant words → same section
  4. Cap at 12 sections (over-cap → merge smallest); ensure minimum 6 (under → split largest)
  5. Each section gets a heading derived from its dominant shared keyword

NO LLM CALLS. Pure tokenization + clustering.

Usage:
    python topic_grouper.py --topics "Cell biology, DNA replication, Protein synthesis, ..."
    python topic_grouper.py --topics-file /tmp/topics.json
    python topic_grouper.py --sample
"""

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from typing import Any, Dict, List, Set


STOP_WORDS = {
    "the", "a", "an", "and", "or", "but", "if", "of", "in", "on", "at", "to",
    "for", "with", "by", "from", "is", "are", "was", "were", "be", "been",
    "this", "that", "these", "those", "introduction", "overview", "basics",
    "fundamentals", "principles", "concepts", "topics", "review", "advanced",
    "intermediate", "i", "ii", "iii", "iv", "v", "1", "2", "3", "4", "5",
    "6", "7", "8", "9", "10", "11", "12", "week", "lecture", "chapter", "unit",
    "module", "lesson", "section",
}

MIN_SECTIONS = 6
MAX_SECTIONS = 12
SHARED_WORD_THRESHOLD = 2


def tokenize(topic: str) -> Set[str]:
    """Extract significant words from a topic string."""
    words = re.findall(r"\b[a-z]{3,}\b", topic.lower())
    return {w for w in words if w not in STOP_WORDS}


def cluster_topics(topics: List[str]) -> List[Dict[str, Any]]:
    """Cluster topics by shared significant words."""
    topic_tokens = [(i, t, tokenize(t)) for i, t in enumerate(topics)]
    clusters: List[List[int]] = []  # list of topic-index lists
    assigned: Set[int] = set()

    for i, _, tokens_i in topic_tokens:
        if i in assigned:
            continue
        # Start a new cluster with topic i
        cluster = [i]
        assigned.add(i)
        # Try to add other topics that share >= SHARED_WORD_THRESHOLD tokens
        for j, _, tokens_j in topic_tokens:
            if j in assigned or j == i:
                continue
            shared = tokens_i & tokens_j
            if len(shared) >= SHARED_WORD_THRESHOLD:
                cluster.append(j)
                assigned.add(j)
        clusters.append(cluster)

    return _normalize_to_size(clusters, topic_tokens)


def _normalize_to_size(clusters: List[List[int]], topic_tokens: List[tuple]) -> List[Dict[str, Any]]:
    """Ensure 6-12 sections by merging smallest or splitting largest."""
    # Merge smallest if over MAX_SECTIONS
    while len(clusters) > MAX_SECTIONS:
        clusters.sort(key=len)
        smallest = clusters.pop(0)
        # Merge into next-smallest
        if clusters:
            clusters[0].extend(smallest)
        else:
            clusters.append(smallest)

    # Split largest if under MIN_SECTIONS (and largest has >= 4 items)
    while len(clusters) < MIN_SECTIONS and clusters:
        clusters.sort(key=len, reverse=True)
        largest = clusters.pop(0)
        if len(largest) >= 4:
            mid = len(largest) // 2
            clusters.extend([largest[:mid], largest[mid:]])
        else:
            clusters.insert(0, largest)
            break  # Can't split further

    # Generate section heading per cluster (most-common shared word)
    sections: List[Dict[str, Any]] = []
    topic_lookup = {i: (t, tokens) for i, t, tokens in topic_tokens}
    for cluster_indices in clusters:
        all_tokens: Counter = Counter()
        cluster_topics: List[str] = []
        for idx in cluster_indices:
            topic, tokens = topic_lookup[idx]
            cluster_topics.append(topic)
            all_tokens.update(tokens)
        # Heading = top 1-3 most common tokens, capitalized
        top_words = [w for w, _ in all_tokens.most_common(2)]
        heading = " + ".join(w.capitalize() for w in top_words) if top_words else f"Section {len(sections) + 1}"
        sections.append({
            "heading": heading,
            "topic_count": len(cluster_indices),
            "topics": cluster_topics,
        })

    return sections


SAMPLE_TOPICS = [
    "Cell Biology Fundamentals",
    "DNA Replication",
    "Protein Synthesis",
    "Cell Division and Mitosis",
    "Mendelian Genetics",
    "Population Genetics",
    "Evolution and Natural Selection",
    "Speciation",
    "Ecology Basics",
    "Ecosystem Dynamics",
    "Energy Flow in Ecosystems",
    "Conservation Biology",
    "Plant Anatomy",
    "Plant Physiology",
    "Animal Anatomy Overview",
    "Animal Behavior",
    "Microbiology Introduction",
    "Bacterial Genetics",
    "Viruses and Pathogens",
]


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--topics", help="Comma-separated topic list")
    parser.add_argument("--topics-file", help="Path to JSON file with topics array")
    parser.add_argument("--sample", action="store_true")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        topics = SAMPLE_TOPICS
    elif args.topics:
        topics = [t.strip() for t in args.topics.split(",") if t.strip()]
    elif args.topics_file:
        from pathlib import Path
        p = Path(args.topics_file)
        if not p.exists():
            print(f"error: {args.topics_file} not found", file=sys.stderr); return 2
        topics = json.loads(p.read_text(encoding="utf-8"))
    else:
        parser.print_help(); return 0

    sections = cluster_topics(topics)
    result = {
        "input_topic_count": len(topics),
        "section_count": len(sections),
        "sections": sections,
    }

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(f"Input topics:    {len(topics)}")
        print(f"Output sections: {len(sections)}  (target: {MIN_SECTIONS}-{MAX_SECTIONS})")
        print()
        print("Proposed sections (present this at Phase 2 checkpoint):")
        for i, s in enumerate(sections, 1):
            print(f"")
            print(f"  Section {i}: {s['heading']}  ({s['topic_count']} topics)")
            for t in s["topics"]:
                print(f"    - {t}")
        print()
        print("Group-and-confirm checkpoint forcing options:")
        print("  1. Looks good — proceed with these sections")
        print("  2. Merge sections [X] and [Y]")
        print("  3. Split section [X] into two")
        print("  4. Add a section for [topic]")
        print("  5. Remove section [X]")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
