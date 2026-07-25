#!/usr/bin/env python3
"""
free_search.py — Free keyless academic search for the litreview skill.

Default search lane for litreview: hits PubMed E-utilities and/or OpenAlex
over plain HTTPS. No API key, no paid plan, no MCP required.

  - PubMed E-utilities (https://eutils.ncbi.nlm.nih.gov/entrez/eutils/)
    esearch.fcgi -> PMID list, then esummary.fcgi -> metadata.
    Keyless etiquette: <= 3 requests/second.
  - OpenAlex (https://api.openalex.org/works?search=...)
    Keyless; pass --mailto to join the polite pool (faster, more reliable).

Stdlib only (urllib). 15s timeout per request. Exits 2 with a clear message
when the network is unavailable (offline harnesses fail gracefully).

Usage:
  python free_search.py --query "LLM clinical reasoning" --source both --max 10
  python free_search.py --query "sepsis treatment PICO" --source pubmed --json
  python free_search.py --query "meta-analysis CRISPR" --source openalex \\
      --mailto you@example.com
"""

import argparse
import json
import sys
import urllib.error
import urllib.parse
import urllib.request

PUBMED_ESEARCH = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi"
PUBMED_ESUMMARY = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi"
OPENALEX_WORKS = "https://api.openalex.org/works"
TIMEOUT_SECONDS = 15
USER_AGENT = (
    "litreview-free-search/1.0 "
    "(claude-skills research pack; +https://github.com/alirezarezvani/claude-skills)"
)


def _get_json(url: str) -> dict:
    """GET a JSON document with a polite User-Agent and a hard timeout."""
    req = urllib.request.Request(
        url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"}
    )
    with urllib.request.urlopen(req, timeout=TIMEOUT_SECONDS) as resp:
        return json.loads(resp.read().decode("utf-8"))


def search_pubmed(query: str, max_results: int) -> list:
    """PubMed E-utilities: esearch (PMIDs) -> esummary (metadata)."""
    esearch_url = PUBMED_ESEARCH + "?" + urllib.parse.urlencode(
        {
            "db": "pubmed",
            "term": query,
            "retmode": "json",
            "retmax": str(max_results),
            "sort": "relevance",
            "tool": "litreview",
        }
    )
    pmids = _get_json(esearch_url).get("esearchresult", {}).get("idlist", [])
    if not pmids:
        return []

    esummary_url = PUBMED_ESUMMARY + "?" + urllib.parse.urlencode(
        {"db": "pubmed", "id": ",".join(pmids), "retmode": "json", "tool": "litreview"}
    )
    summary = _get_json(esummary_url).get("result", {})

    results = []
    for pmid in pmids:
        doc = summary.get(pmid)
        if not isinstance(doc, dict):
            continue
        doi = next(
            (a.get("value") for a in doc.get("articleids", []) if a.get("idtype") == "doi"),
            None,
        )
        results.append(
            {
                "source": "pubmed",
                "title": doc.get("title", "").strip(),
                "authors": [a.get("name") for a in doc.get("authors", []) if a.get("name")],
                "year": (doc.get("pubdate") or "")[:4] or None,
                "journal": doc.get("fulljournalname"),
                "doi": doi,
                "citations": None,  # esummary does not return citation counts
                "url": f"https://pubmed.ncbi.nlm.nih.gov/{pmid}/",
            }
        )
    return results


def search_openalex(query: str, max_results: int, mailto: str = None) -> list:
    """OpenAlex works search. mailto joins the polite pool (recommended)."""
    params = {"search": query, "per-page": str(max_results)}
    if mailto:
        params["mailto"] = mailto
    data = _get_json(OPENALEX_WORKS + "?" + urllib.parse.urlencode(params))

    results = []
    for work in data.get("results", []):
        authors = [
            (a.get("author") or {}).get("display_name")
            for a in work.get("authorships", [])
        ]
        venue = ((work.get("primary_location") or {}).get("source") or {}).get(
            "display_name"
        )
        results.append(
            {
                "source": "openalex",
                "title": work.get("display_name", "").strip(),
                "authors": [a for a in authors if a],
                "year": work.get("publication_year"),
                "journal": venue,
                "doi": work.get("doi"),
                "citations": work.get("cited_by_count"),
                "url": work.get("doi") or work.get("id"),
            }
        )
    return results


def render_human(results: list) -> str:
    if not results:
        return "0 results. Either niche terminology or a genuine gap — never silently fill."
    lines = []
    for i, r in enumerate(results, 1):
        authors = ", ".join(r["authors"][:3]) + (" et al." if len(r["authors"]) > 3 else "")
        cites = f" — {r['citations']} citations" if r.get("citations") is not None else ""
        lines.append(f"{i}. [{r['source']}] {r['title']} ({r.get('year') or 'n.d.'})")
        lines.append(f"   {authors or '(authors unavailable)'}{cites}")
        lines.append(f"   {r['url']}")
    return "\n".join(lines)


def main():
    p = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    p.add_argument("--query", required=True, help="Search query (plain keywords).")
    p.add_argument(
        "--source",
        choices=["pubmed", "openalex", "both"],
        default="both",
        help="Which free API to hit (default: both).",
    )
    p.add_argument("--max", type=int, default=10, help="Max results per source (default: 10).")
    p.add_argument("--json", action="store_true", help="Emit JSON instead of human-readable.")
    p.add_argument(
        "--mailto",
        default=None,
        help="Email for the OpenAlex polite pool (recommended, not required).",
    )
    args = p.parse_args()

    results = []
    try:
        if args.source in ("pubmed", "both"):
            results.extend(search_pubmed(args.query, args.max))
        if args.source in ("openalex", "both"):
            results.extend(search_openalex(args.query, args.max, args.mailto))
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, OSError) as exc:
        sys.stderr.write(
            "free_search: network unavailable or API unreachable "
            f"({exc}). The free lane needs outbound HTTPS to "
            "eutils.ncbi.nlm.nih.gov / api.openalex.org. Retry once after 3s; "
            "after 3 consecutive failures, stop and report what was collected.\n"
        )
        sys.exit(2)
    except json.JSONDecodeError as exc:
        sys.stderr.write(f"free_search: API returned non-JSON response ({exc}).\n")
        sys.exit(2)

    if args.json:
        print(json.dumps({"query": args.query, "count": len(results), "results": results}, indent=2))
    else:
        print(render_human(results))


if __name__ == "__main__":
    main()
