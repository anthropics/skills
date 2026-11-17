#!/usr/bin/env python3
"""Citation resolution + verification for the fact-check pass. Stdlib only, no API keys.

Two subcommands:

  parse  <file.bib> [key ...]
      Parse a BibTeX file (brace-counting — titles with commas/braces survive).
      With keys: only those entries. Output: JSON {key: {title, author, year}}.

  verify "<title>" [--author "surname"]
      Look the title up on Crossref and report the best match, so you can check
      that a cited work exists and is what the paper says it is.
      Output: JSON {query, matched_title, authors, year, venue, doi, score_hint}.

Usage examples:
  python bib_resolve.py parse refs.bib smith2024attention
  python bib_resolve.py verify "Attention is all you need"
"""
import argparse
import json
import re
import sys
import urllib.parse
import urllib.request

UA = {"User-Agent": "holistic-paper-review-skill/1.0 (mailto:reviewer@example.org)"}


def parse_bib(text):
    """Brace-counting BibTeX parser. Returns {key: {field: value}}."""
    entries = {}
    for m in re.finditer(r'@(\w+)\s*\{\s*([^,\s]+)\s*,', text):
        if m.group(1).lower() in ("comment", "preamble", "string"):
            continue
        key = m.group(2)
        depth, i = 1, m.end()
        start = i
        while i < len(text) and depth > 0:
            if text[i] == "{":
                depth += 1
            elif text[i] == "}":
                depth -= 1
            i += 1
        body = text[start:i - 1]
        fields = {}
        for fm in re.finditer(r'(\w+)\s*=\s*', body):
            fname = fm.group(1).lower()
            j = fm.end()
            if j < len(body) and body[j] == "{":
                d, j2 = 1, j + 1
                while j2 < len(body) and d > 0:
                    if body[j2] == "{":
                        d += 1
                    elif body[j2] == "}":
                        d -= 1
                    j2 += 1
                val = body[j + 1:j2 - 1]
            elif j < len(body) and body[j] == '"':
                j2 = body.find('"', j + 1)
                val = body[j + 1:j2] if j2 != -1 else body[j + 1:]
            else:
                j2 = body.find(",", j)
                val = body[j:j2] if j2 != -1 else body[j:]
            fields[fname] = " ".join(val.replace("{", "").replace("}", "").split())
        entries[key] = {k: v for k, v in fields.items()
                        if k in ("title", "author", "year", "booktitle", "journal")}
    return entries


def verify(title, author=None):
    q = urllib.parse.quote(title)
    url = f"https://api.crossref.org/works?query.bibliographic={q}&rows=3"
    if author:
        url += f"&query.author={urllib.parse.quote(author)}"
    req = urllib.request.Request(url, headers=UA)
    with urllib.request.urlopen(req, timeout=20) as r:
        data = json.loads(r.read().decode())
    items = data.get("message", {}).get("items", [])
    if not items:
        return {"query": title, "matched_title": None,
                "note": "no Crossref match — try arXiv via paper_search.py"}
    best = items[0]
    return {
        "query": title,
        "matched_title": (best.get("title") or [None])[0],
        "authors": [f"{a.get('given','')} {a.get('family','')}".strip()
                    for a in best.get("author", [])][:6],
        "year": (best.get("issued", {}).get("date-parts") or [[None]])[0][0],
        "venue": best.get("container-title", [None])[0] if best.get("container-title") else None,
        "doi": best.get("DOI"),
        "note": "compare matched_title with query yourself — Crossref returns best-effort matches",
    }


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p1 = sub.add_parser("parse")
    p1.add_argument("bibfile")
    p1.add_argument("keys", nargs="*")
    p2 = sub.add_parser("verify")
    p2.add_argument("title")
    p2.add_argument("--author")
    args = ap.parse_args()

    if args.cmd == "parse":
        with open(args.bibfile, encoding="utf-8", errors="replace") as f:
            entries = parse_bib(f.read())
        if args.keys:
            entries = {k: v for k, v in entries.items() if k in args.keys}
        print(json.dumps(entries, indent=2, ensure_ascii=False))
    else:
        try:
            print(json.dumps(verify(args.title, args.author), indent=2, ensure_ascii=False))
        except Exception as ex:
            print(json.dumps({"query": args.title, "error": str(ex)}), file=sys.stdout)


if __name__ == "__main__":
    main()
