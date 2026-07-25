#!/usr/bin/env python3
"""
wiki_search.py — BM25 search over a wiki vault.

Standard library only. Works as a fallback when `index.md` alone isn't enough
(e.g. you want to find which pages mention a specific term the LLM hasn't yet
cross-referenced). For larger vaults, pair this with an external tool like
qmd (https://github.com/tobi/qmd) for hybrid/vector search.

Usage:
    python wiki_search.py --vault ~/vaults/research --query "sparse autoencoder"
    python wiki_search.py --vault . --query "monosemanticity" --limit 5 --json
"""
from __future__ import annotations
import argparse
import json
import math
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

TOKEN_RE = re.compile(r"[a-zA-Z0-9][a-zA-Z0-9_\-']+")
STOPWORDS = {
    "the", "a", "an", "and", "or", "but", "if", "then", "so", "to", "of", "in",
    "on", "at", "for", "by", "with", "from", "is", "are", "was", "were", "be",
    "been", "being", "this", "that", "these", "those", "it", "its", "as", "we",
    "you", "they", "their", "our", "us", "i", "not", "no", "yes", "do", "does",
    "did", "will", "would", "can", "could", "should", "about", "into", "than",
    "out", "up", "down", "over", "under", "also",
}


def tokenize(text: str) -> list[str]:
    return [
        t.lower()
        for t in TOKEN_RE.findall(text)
        if t.lower() not in STOPWORDS and len(t) > 1
    ]


def load_docs(vault: Path) -> list[dict]:
    wiki = vault / "wiki"
    if not wiki.exists():
        raise SystemExit(f"[error] {wiki} not found")
    docs = []
    for md in sorted(wiki.rglob("*.md")):
        rel = md.relative_to(wiki)
        if rel.name in {"index.md", "log.md"}:
            continue
        if any(part.startswith(".") for part in rel.parts):
            continue
        text = md.read_text(encoding="utf-8", errors="replace")
        tokens = tokenize(text)
        docs.append(
            {
                "path": str(rel).replace("\\", "/"),
                "text": text,
                "tokens": tokens,
                "tf": Counter(tokens),
                "len": len(tokens),
            }
        )
    return docs


def bm25_scores(
    docs: list[dict], query: list[str], k1: float = 1.5, b: float = 0.75
) -> list[tuple[int, float]]:
    N = len(docs)
    if N == 0:
        return []
    avgdl = sum(d["len"] for d in docs) / N or 1
    df: dict[str, int] = defaultdict(int)
    for d in docs:
        for term in set(d["tokens"]):
            df[term] += 1
    idf = {
        term: math.log(1 + (N - df_t + 0.5) / (df_t + 0.5))
        for term, df_t in df.items()
    }

    scores: list[tuple[int, float]] = []
    for i, d in enumerate(docs):
        score = 0.0
        for term in query:
            if term not in d["tf"]:
                continue
            tf = d["tf"][term]
            denom = tf + k1 * (1 - b + b * d["len"] / avgdl)
            score += idf.get(term, 0.0) * (tf * (k1 + 1)) / (denom or 1)
        if score > 0:
            scores.append((i, score))
    scores.sort(key=lambda x: x[1], reverse=True)
    return scores


def snippet(text: str, query: list[str], width: int = 220) -> str:
    lower = text.lower()
    for term in query:
        idx = lower.find(term)
        if idx >= 0:
            start = max(0, idx - width // 3)
            end = min(len(text), start + width)
            s = text[start:end].replace("\n", " ")
            return ("…" if start > 0 else "") + s + ("…" if end < len(text) else "")
    return text[:width].replace("\n", " ") + ("…" if len(text) > width else "")


def main() -> None:
    p = argparse.ArgumentParser(description="BM25 search over an LLM Wiki vault")
    p.add_argument("--vault", required=True)
    p.add_argument("--query", required=True)
    p.add_argument("--limit", type=int, default=10)
    p.add_argument("--json", action="store_true")
    args = p.parse_args()

    docs = load_docs(Path(args.vault).expanduser().resolve())
    qtokens = tokenize(args.query)
    if not qtokens:
        print("[error] empty query after tokenization", file=sys.stderr)
        sys.exit(1)

    scored = bm25_scores(docs, qtokens)[: args.limit]
    hits = []
    for i, s in scored:
        d = docs[i]
        hits.append(
            {"path": d["path"], "score": round(s, 3), "snippet": snippet(d["text"], qtokens)}
        )

    if args.json:
        print(json.dumps({"query": args.query, "hits": hits}, indent=2, ensure_ascii=False))
    else:
        if not hits:
            print(f"No matches for: {args.query}")
            return
        print(f"Query: {args.query}  ({len(hits)} hits)")
        for h in hits:
            print(f"\n  [{h['score']}] {h['path']}")
            print(f"     {h['snippet']}")


if __name__ == "__main__":
    main()
