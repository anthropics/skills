#!/usr/bin/env python3
"""Multi-source research synthesizer. All APIs free, no auth required."""

import sys
import json
import urllib.request
import urllib.parse
import xml.etree.ElementTree as ET
import argparse
import threading
from datetime import datetime


def fetch_json(url, headers=None, timeout=15):
    try:
        req = urllib.request.Request(url, headers=headers or {"User-Agent": "research-synthesizer/1.0"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode('utf-8'))
    except Exception as e:
        return {"error": str(e)}


def fetch_xml(url, timeout=15):
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "research-synthesizer/1.0"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.read().decode('utf-8')
    except Exception as e:
        return None


# --- arXiv ---
def fetch_arxiv(query, max_results=10):
    encoded = urllib.parse.quote(query)
    url = f"http://export.arxiv.org/api/query?search_query=all:{encoded}&max_results={max_results}&sortBy=relevance&sortOrder=descending"
    xml_data = fetch_xml(url)
    if not xml_data:
        return []

    NS = {'atom': 'http://www.w3.org/2005/Atom'}
    try:
        root = ET.fromstring(xml_data)
    except ET.ParseError:
        return []

    papers = []
    for entry in root.findall('atom:entry', NS):
        id_el = entry.find('atom:id', NS)
        title_el = entry.find('atom:title', NS)
        summary_el = entry.find('atom:summary', NS)
        published_el = entry.find('atom:published', NS)
        authors = [a.find('atom:name', NS).text for a in entry.findall('atom:author', NS) if a.find('atom:name', NS) is not None]

        arxiv_id = id_el.text.split('/abs/')[-1] if id_el is not None else ""
        papers.append({
            "source": "arxiv",
            "id": arxiv_id,
            "title": title_el.text.strip().replace('\n', ' ') if title_el is not None else "",
            "abstract": summary_el.text.strip()[:400] if summary_el is not None else "",
            "published": published_el.text[:10] if published_el is not None else "",
            "authors": authors[:4],
            "url": f"https://arxiv.org/abs/{arxiv_id}"
        })
    return papers


# --- PubMed ---
def fetch_pubmed(query, max_results=10):
    encoded = urllib.parse.quote(query)
    # Step 1: search
    search_url = f"https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=pubmed&term={encoded}&retmax={max_results}&retmode=json&sort=relevance"
    search_data = fetch_json(search_url)
    if "error" in search_data:
        return []

    ids = search_data.get("esearchresult", {}).get("idlist", [])
    if not ids:
        return []

    # Step 2: fetch summaries
    ids_str = ",".join(ids[:10])
    summary_url = f"https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=pubmed&id={ids_str}&retmode=json"
    summary_data = fetch_json(summary_url)

    papers = []
    result = summary_data.get("result", {})
    for pmid in ids[:10]:
        if pmid not in result:
            continue
        doc = result[pmid]
        papers.append({
            "source": "pubmed",
            "id": pmid,
            "title": doc.get("title", ""),
            "published": doc.get("pubdate", "")[:10],
            "authors": [a.get("name", "") for a in doc.get("authors", [])[:4]],
            "url": f"https://pubmed.ncbi.nlm.nih.gov/{pmid}/",
            "journal": doc.get("source", "")
        })
    return papers


# --- Semantic Scholar ---
def fetch_semantic_scholar(query, max_results=10):
    encoded = urllib.parse.quote(query)
    url = f"https://api.semanticscholar.org/graph/v1/paper/search?query={encoded}&limit={max_results}&fields=title,abstract,year,citationCount,authors,url,externalIds"
    data = fetch_json(url)
    if "error" in data:
        return []

    papers = []
    for p in data.get("data", []):
        arxiv_id = p.get("externalIds", {}).get("ArXiv", "")
        papers.append({
            "source": "semantic_scholar",
            "id": p.get("paperId", ""),
            "title": p.get("title", ""),
            "abstract": p.get("abstract", "")[:400] if p.get("abstract") else "",
            "year": p.get("year", ""),
            "citations": p.get("citationCount", 0),
            "authors": [a.get("name", "") for a in p.get("authors", [])[:4]],
            "url": p.get("url", ""),
            "arxiv_id": arxiv_id
        })
    return sorted(papers, key=lambda x: x.get("citations", 0), reverse=True)


# --- Hacker News ---
def fetch_hacker_news(query, max_results=10):
    encoded = urllib.parse.quote(query)
    url = f"https://hn.algolia.com/api/v1/search?query={encoded}&tags=story&hitsPerPage={max_results}"
    data = fetch_json(url)
    if "error" in data:
        return []

    posts = []
    for hit in data.get("hits", []):
        posts.append({
            "source": "hacker_news",
            "id": hit.get("objectID", ""),
            "title": hit.get("title", ""),
            "url": hit.get("url", f"https://news.ycombinator.com/item?id={hit.get('objectID','')}"),
            "points": hit.get("points", 0),
            "comments": hit.get("num_comments", 0),
            "date": hit.get("created_at", "")[:10],
            "hn_url": f"https://news.ycombinator.com/item?id={hit.get('objectID','')}"
        })
    return sorted(posts, key=lambda x: x.get("points", 0), reverse=True)


# --- Wikipedia ---
def fetch_wikipedia(topic):
    slug = urllib.parse.quote(topic.replace(" ", "_"))
    url = f"https://en.wikipedia.org/api/rest_v1/page/summary/{slug}"
    data = fetch_json(url)
    if "error" in data or "type" not in data:
        return None
    return {
        "source": "wikipedia",
        "title": data.get("title", ""),
        "extract": data.get("extract", ""),
        "url": data.get("content_urls", {}).get("desktop", {}).get("page", "")
    }


def run_parallel(fns):
    """Run fetch functions in parallel threads, return results dict."""
    results = {}
    threads = []

    def run(name, fn):
        results[name] = fn()

    for name, fn in fns.items():
        t = threading.Thread(target=run, args=(name, fn))
        threads.append(t)
        t.start()

    for t in threads:
        t.join(timeout=20)

    return results


def synthesize(topic, use_pubmed=True, use_arxiv=True, use_ss=True, use_hn=True, use_wiki=True):
    fns = {}
    if use_arxiv:
        fns["arxiv"] = lambda: fetch_arxiv(topic)
    if use_pubmed:
        fns["pubmed"] = lambda: fetch_pubmed(topic)
    if use_ss:
        fns["semantic_scholar"] = lambda: fetch_semantic_scholar(topic)
    if use_hn:
        fns["hacker_news"] = lambda: fetch_hacker_news(topic)
    if use_wiki:
        fns["wikipedia"] = lambda: fetch_wikipedia(topic)

    print(f"Fetching from {len(fns)} sources in parallel...", file=sys.stderr)
    results = run_parallel(fns)

    return results


def print_markdown_report(topic, results):
    today = datetime.now().strftime("%Y-%m-%d")
    sources_used = [k for k in results if results[k]]

    print(f"# Research Synthesis: {topic}")
    print(f"*Sources: {', '.join(sources_used)} | {today}*\n")

    # Wikipedia grounding
    wiki = results.get("wikipedia")
    if wiki and not isinstance(wiki, list):
        print("## Background")
        print(wiki.get("extract", "")[:500])
        print(f"\n[Wikipedia: {wiki.get('title','')}]({wiki.get('url','')})\n")

    # Top academic papers (Semantic Scholar, sorted by citations)
    ss_papers = results.get("semantic_scholar", [])
    arxiv_papers = results.get("arxiv", [])

    if ss_papers:
        print("## Key Academic Papers (by influence)")
        for i, p in enumerate(ss_papers[:5], 1):
            cites = f"Citations: {p.get('citations', 0)} | " if p.get('citations') else ""
            print(f"**{i}. {p['title']}**")
            print(f"*{', '.join(p.get('authors', [])[:3])} | {p.get('year', 'N/A')} | {cites}[Link]({p['url']})*")
            if p.get("abstract"):
                print(f"> {p['abstract'][:300]}...")
            print()

    if arxiv_papers and not ss_papers:
        print("## arXiv Papers")
        for i, p in enumerate(arxiv_papers[:7], 1):
            print(f"**{i}. {p['title']}**")
            print(f"*{', '.join(p.get('authors', [])[:3])} | {p.get('published', '')[:7]} | [arXiv]({p['url']})*")
            if p.get("abstract"):
                print(f"> {p['abstract'][:300]}...")
            print()

    # PubMed
    pubmed_papers = results.get("pubmed", [])
    if pubmed_papers:
        print("## Clinical/Medical Research (PubMed)")
        for i, p in enumerate(pubmed_papers[:5], 1):
            print(f"**{i}. {p['title']}**")
            print(f"*{', '.join(p.get('authors', [])[:3])} | {p.get('journal', '')} | {p.get('published', '')} | [PubMed]({p['url']})*")
            print()

    # HN community signals
    hn_posts = results.get("hacker_news", [])
    if hn_posts:
        print("## Community Signals (Hacker News)")
        for i, p in enumerate(hn_posts[:5], 1):
            print(f"**{i}. [{p['title']}]({p['hn_url']})** — {p.get('points', 0)} pts, {p.get('comments', 0)} comments | {p.get('date', '')}")
        print()

    print("---")
    print(f"*Synthesized from {sum(len(v) if isinstance(v, list) else (1 if v else 0) for v in results.values())} sources*")


def main():
    parser = argparse.ArgumentParser(description="Multi-source research synthesizer")
    parser.add_argument("--topic", required=True, help="Research topic")
    parser.add_argument("--all-sources", action="store_true", default=True)
    parser.add_argument("--no-pubmed", action="store_true")
    parser.add_argument("--no-arxiv", action="store_true")
    parser.add_argument("--no-hn", action="store_true")
    parser.add_argument("--no-wiki", action="store_true")
    parser.add_argument("--format", default="markdown", choices=["markdown", "json"])
    args = parser.parse_args()

    results = synthesize(
        args.topic,
        use_pubmed=not args.no_pubmed,
        use_arxiv=not args.no_arxiv,
        use_hn=not args.no_hn,
        use_wiki=not args.no_wiki
    )

    if args.format == "json":
        print(json.dumps(results, indent=2))
    else:
        print_markdown_report(args.topic, results)


if __name__ == "__main__":
    main()
