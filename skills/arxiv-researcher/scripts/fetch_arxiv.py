#!/usr/bin/env python3
"""Fetch papers from arXiv API. No auth required."""

import sys
import xml.etree.ElementTree as ET
import urllib.request
import urllib.parse
import json
import argparse


ARXIV_API = "http://export.arxiv.org/api/query"
SEMANTIC_SCHOLAR_API = "https://api.semanticscholar.org/graph/v1/paper"

NS = {
    'atom': 'http://www.w3.org/2005/Atom',
    'arxiv': 'http://arxiv.org/schemas/atom',
    'opensearch': 'http://a9.com/-/spec/opensearch/1.1/'
}


def fetch_arxiv(query, max_results=15, sort_by="relevance", category=None):
    if category:
        search_query = f"({urllib.parse.quote(query)}) AND cat:{category}"
    else:
        search_query = f"all:{urllib.parse.quote(query)}"

    params = urllib.parse.urlencode({
        "search_query": search_query,
        "max_results": max_results,
        "sortBy": sort_by,
        "sortOrder": "descending"
    })

    url = f"{ARXIV_API}?{params}"
    with urllib.request.urlopen(url, timeout=15) as resp:
        xml_data = resp.read().decode('utf-8')

    root = ET.fromstring(xml_data)
    papers = []

    for entry in root.findall('atom:entry', NS):
        arxiv_id_url = entry.find('atom:id', NS).text
        arxiv_id = arxiv_id_url.split('/abs/')[-1] if '/abs/' in arxiv_id_url else arxiv_id_url

        title_el = entry.find('atom:title', NS)
        title = title_el.text.strip().replace('\n', ' ') if title_el is not None else "No title"

        summary_el = entry.find('atom:summary', NS)
        abstract = summary_el.text.strip().replace('\n', ' ') if summary_el is not None else ""

        published_el = entry.find('atom:published', NS)
        published = published_el.text[:10] if published_el is not None else ""

        authors = [
            a.find('atom:name', NS).text
            for a in entry.findall('atom:author', NS)
            if a.find('atom:name', NS) is not None
        ]

        pdf_url = f"https://arxiv.org/pdf/{arxiv_id}"
        abs_url = f"https://arxiv.org/abs/{arxiv_id}"

        categories = [
            c.get('term', '')
            for c in entry.findall('arxiv:primary_category', NS)
        ]

        papers.append({
            "id": arxiv_id,
            "title": title,
            "abstract": abstract[:500] + "..." if len(abstract) > 500 else abstract,
            "published": published,
            "authors": authors[:5],
            "pdf_url": pdf_url,
            "abs_url": abs_url,
            "categories": categories
        })

    return papers


def enrich_with_citations(arxiv_id):
    """Get citation count from Semantic Scholar."""
    try:
        url = f"{SEMANTIC_SCHOLAR_API}/arXiv:{arxiv_id}?fields=citationCount,influentialCitationCount"
        with urllib.request.urlopen(url, timeout=10) as resp:
            data = json.loads(resp.read().decode('utf-8'))
            return {
                "citations": data.get("citationCount", 0),
                "influential_citations": data.get("influentialCitationCount", 0)
            }
    except Exception:
        return {"citations": None, "influential_citations": None}


def main():
    parser = argparse.ArgumentParser(description="Fetch arXiv papers")
    parser.add_argument("--query", required=True, help="Search query")
    parser.add_argument("--max", type=int, default=15, help="Max results")
    parser.add_argument("--sort", default="relevance", choices=["relevance", "lastUpdatedDate", "submittedDate"])
    parser.add_argument("--category", help="arXiv category filter (e.g. cs.AI)")
    parser.add_argument("--enrich", action="store_true", help="Add citation counts via Semantic Scholar")
    parser.add_argument("--format", default="json", choices=["json", "markdown"])
    args = parser.parse_args()

    papers = fetch_arxiv(args.query, args.max, args.sort, args.category)

    if args.enrich:
        for p in papers[:5]:
            cites = enrich_with_citations(p["id"])
            p.update(cites)

    if args.format == "json":
        print(json.dumps(papers, indent=2))
    else:
        print(f"# arXiv Search: {args.query}\n")
        print(f"Found {len(papers)} papers\n")
        for i, p in enumerate(papers, 1):
            authors_str = ", ".join(p["authors"][:3])
            if len(p["authors"]) > 3:
                authors_str += f" et al."
            cites = f" | Citations: {p.get('citations', 'N/A')}" if 'citations' in p else ""
            print(f"### {i}. {p['title']}")
            print(f"**Authors:** {authors_str} | **Published:** {p['published']}{cites}")
            print(f"**Abstract:** {p['abstract']}")
            print(f"**Links:** [Abstract]({p['abs_url']}) | [PDF]({p['pdf_url']})")
            print()


if __name__ == "__main__":
    main()
