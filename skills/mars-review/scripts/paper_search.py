#!/usr/bin/env python3
"""Related-work retrieval for the novelty scout. Stdlib only, no API keys.

Sources:
  - arXiv API (export.arxiv.org)   — preprints, abstracts
  - Semantic Scholar Graph API     — published work, citation counts

Usage:
  python paper_search.py "query written like a knowledgeable reviewer" [--max 5] [--source arxiv|s2|both]

Output: JSON list of {title, authors, year, venue, abstract, url, citations, source}.
Rate limits: S2 unauthenticated ~1 req/s; arXiv asks for 3s between requests.
The script sleeps accordingly — call it once per query, not in tight loops.
"""
import argparse
import json
import sys
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET

UA = {"User-Agent": "holistic-paper-review-skill/1.0 (research reviewing tool)"}


def _get(url, timeout=20):
    req = urllib.request.Request(url, headers=UA)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read().decode("utf-8", errors="replace")


def search_arxiv(query, max_results=5):
    q = urllib.parse.quote(query)
    url = (f"http://export.arxiv.org/api/query?search_query=all:{q}"
           f"&max_results={max_results}&sortBy=relevance")
    ns = {"a": "http://www.w3.org/2005/Atom"}
    out = []
    try:
        root = ET.fromstring(_get(url))
        for e in root.findall("a:entry", ns):
            title = " ".join((e.findtext("a:title", "", ns) or "").split())
            out.append({
                "title": title,
                "authors": [a.findtext("a:name", "", ns) for a in e.findall("a:author", ns)][:6],
                "year": (e.findtext("a:published", "", ns) or "")[:4],
                "venue": "arXiv",
                "abstract": " ".join((e.findtext("a:summary", "", ns) or "").split())[:600],
                "url": e.findtext("a:id", "", ns),
                "citations": None,
                "source": "arxiv",
            })
    except Exception as ex:
        print(f"arxiv error: {ex}", file=sys.stderr)
    return out


def search_s2(query, max_results=5):
    q = urllib.parse.quote(query)
    fields = "title,authors,year,venue,abstract,url,citationCount"
    url = (f"https://api.semanticscholar.org/graph/v1/paper/search"
           f"?query={q}&limit={max_results}&fields={fields}")
    out = []
    try:
        data = json.loads(_get(url))
        for p in data.get("data", []):
            out.append({
                "title": p.get("title"),
                "authors": [a.get("name") for a in (p.get("authors") or [])][:6],
                "year": p.get("year"),
                "venue": p.get("venue") or "n/a",
                "abstract": (p.get("abstract") or "")[:600],
                "url": p.get("url"),
                "citations": p.get("citationCount"),
                "source": "s2",
            })
    except Exception as ex:
        print(f"s2 error: {ex}", file=sys.stderr)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("query")
    ap.add_argument("--max", type=int, default=5)
    ap.add_argument("--source", choices=["arxiv", "s2", "both"], default="both")
    args = ap.parse_args()

    results = []
    if args.source in ("s2", "both"):
        results += search_s2(args.query, args.max)
    if args.source in ("arxiv", "both"):
        if args.source == "both":
            time.sleep(1)
        results += search_arxiv(args.query, args.max)

    # De-duplicate by normalized title
    seen, deduped = set(), []
    for r in results:
        key = "".join(c for c in (r["title"] or "").lower() if c.isalnum())
        if key and key not in seen:
            seen.add(key)
            deduped.append(r)
    print(json.dumps(deduped, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
