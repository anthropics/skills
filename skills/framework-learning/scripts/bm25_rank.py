#!/usr/bin/env python3
"""
bm25_rank.py — Rank index pages by relevance to a query using BM25.

Usage:
  python bm25_rank.py --index artifacts/index.json --query "how to install" --k 20 --out artifacts/topk.json

Output:
  artifacts/topk.json with top-k ranked URLs:
  {
    "query": "how to install",
    "k": 20,
    "results": [
      {
        "id": 5,
        "url": "https://docs.example.com/install",
        "title": "Installation Guide",
        "score": 8.42
      },
      ...
    ]
  }
"""

import json
import argparse

try:
    from rank_bm25 import BM25Okapi
except ImportError:
    print("ERROR: rank_bm25 not installed. Run: pip install rank-bm25")
    exit(1)


def rank_pages(index_file: str, query: str, k: int = 20) -> dict:
    """
    Load index and rank pages by BM25 relevance to query.
    """
    with open(index_file, "r") as f:
        index = json.load(f)

    # Tokenize all page texts
    corpus = [page["text"].lower().split() for page in index["pages"]]

    # Build BM25 index
    bm25 = BM25Okapi(corpus)

    # Tokenize query
    query_tokens = query.lower().split()

    # Score all pages
    scores = bm25.get_scores(query_tokens)

    # Rank and take top-k
    ranked = sorted(
        [
            {
                "id": idx,
                "url": page["url"],
                "title": page["title"],
                "score": float(scores[idx])
            }
            for idx, page in enumerate(index["pages"])
        ],
        key=lambda x: x["score"],
        reverse=True
    )[:k]

    return {
        "query": query,
        "k": k,
        "results": ranked
    }


def main():
    parser = argparse.ArgumentParser(
        description="Rank pages using BM25 for a given query."
    )
    parser.add_argument(
        "--index",
        required=True,
        help="Index JSON file (from build_index.py)"
    )
    parser.add_argument(
        "--query",
        required=True,
        help="Search query"
    )
    parser.add_argument(
        "--k",
        type=int,
        default=20,
        help="Number of top results to return (default: 20)"
    )
    parser.add_argument(
        "--out",
        required=True,
        help="Output topk.json file"
    )

    args = parser.parse_args()

    print(f"Query: {args.query}")
    print(f"Returning top-{args.k}")

    results = rank_pages(args.index, args.query, k=args.k)

    import os
    os.makedirs(os.path.dirname(args.out), exist_ok=True)

    with open(args.out, "w") as f:
        json.dump(results, f, indent=2)

    print(f"✓ Ranked {len(results['results'])} results")
    print(f"✓ Saved to: {args.out}")

    for i, r in enumerate(results["results"][:5], 1):
        print(f"  {i}. {r['title']} (score: {r['score']:.2f})")


if __name__ == "__main__":
    main()
