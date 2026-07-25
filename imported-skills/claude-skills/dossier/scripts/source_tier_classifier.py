#!/usr/bin/env python3
"""source_tier_classifier.py — URL → primary/secondary/tertiary tier.

Stdlib-only. Classifies a source URL into reliability tier based on domain
heuristics. The dossier skill uses tier on every flag in the DOCX so reviewers
can calibrate confidence.

Tiers:
  - PRIMARY:    Official, regulatory, court records, SEC EDGAR, .gov, company
                official site, academic publications (peer-reviewed)
  - SECONDARY:  Mainstream news (NYT, WSJ, Reuters), trade press, established
                publications (TechCrunch, The Information, Stratechery)
  - TERTIARY:   Blogs, forums, social media, user-generated content (Reddit, HN,
                Glassdoor, Medium, personal blogs)

NO LLM CALLS. Pure domain pattern matching.

Usage:
    python source_tier_classifier.py --url "https://www.sec.gov/cgi-bin/browse-edgar?..."
    python source_tier_classifier.py --url "https://news.ycombinator.com/item?id=..."
    python source_tier_classifier.py --sample
"""

import argparse
import json
import re
import sys
from typing import Any, Dict, List, Optional
from urllib.parse import urlparse


# Pattern-based tier assignment. Most specific patterns first.

PRIMARY_DOMAIN_EXACT = {
    "sec.gov", "data.sec.gov", "www.sec.gov",
    "courtlistener.com", "pacer.gov",
    "uspto.gov", "patents.google.com",  # patents.google.com indexes USPTO data
    "fda.gov", "cdc.gov", "nih.gov", "grants.nih.gov", "reporter.nih.gov",
    "federalregister.gov", "regulations.gov",
    "gao.gov", "oig.gov",
    "irs.gov",
    "sec.org",  # generic .org for SEC alternates
}

PRIMARY_DOMAIN_SUFFIX = [
    ".gov",  # any government domain
    ".mil",  # military
    ".edu",  # academic (caveat: some .edu content is tertiary, but most institutional pages are primary)
]

PRIMARY_DOMAIN_CONTAINS = [
    "projects.propublica.org/nonprofits",  # ProPublica Nonprofit Explorer (free Form 990 access)
]

# Academic publication primary sources
PRIMARY_ACADEMIC = {
    "nature.com", "science.org", "nejm.org", "thelancet.com", "jamanetwork.com",
    "pnas.org", "bmj.com", "cell.com", "plos.org",
    "scholar.google.com",  # indexes peer-reviewed; treat as primary
}

# Mainstream news (secondary)
SECONDARY_NEWS = {
    "nytimes.com", "wsj.com", "ft.com", "reuters.com", "ap.org", "apnews.com",
    "bbc.com", "bbc.co.uk", "theguardian.com", "economist.com",
    "washingtonpost.com", "latimes.com", "bloomberg.com",
    "cnbc.com", "abcnews.go.com", "nbcnews.com", "cbsnews.com",
}

# Trade press / established tech publications (secondary)
SECONDARY_TRADE = {
    "techcrunch.com", "theverge.com", "wired.com", "arstechnica.com",
    "theinformation.com", "stratechery.com",
    "axios.com", "politico.com",
    "forbes.com",  # mixed quality, but generally secondary
    "modernhealthcare.com", "healthcareitnews.com",
    "law360.com", "natlawreview.com",
}

# Trade-press journalism orgs (secondary)
SECONDARY_INVESTIGATIVE = {
    "propublica.org", "icij.org",  # ProPublica investigative reporting (separate from Nonprofit Explorer)
}

# Tertiary indicators
TERTIARY_DOMAIN_EXACT = {
    "reddit.com", "old.reddit.com", "news.ycombinator.com",
    "medium.com", "dev.to", "substack.com",
    "twitter.com", "x.com",
    "linkedin.com",  # public posts; profiles separately primary for the subject
    "glassdoor.com", "indeed.com", "comparably.com",
    "quora.com", "stackoverflow.com",
    "facebook.com", "instagram.com", "tiktok.com",
}

TERTIARY_PATTERN = [
    re.compile(r".*\.medium\.com$"),
    re.compile(r".*\.substack\.com$"),
    re.compile(r".*\.blogspot\.com$"),
    re.compile(r".*\.wordpress\.com$"),
    re.compile(r".*\.tumblr\.com$"),
]

# Company-official site detection (primary IF the dossier subject)
# Generic patterns:
def is_likely_company_official(domain: str, subject_keywords: List[str]) -> bool:
    """If the domain contains the subject's name and isn't a known news/blog, it's likely official."""
    if not subject_keywords:
        return False
    domain_lower = domain.lower()
    for kw in subject_keywords:
        if kw.lower() in domain_lower:
            return True
    return False


def classify(url: str, subject_keywords: Optional[List[str]] = None) -> Dict[str, Any]:
    if not url or not url.strip():
        return {"tier": "unknown", "url": url, "rationale": "Empty URL"}

    try:
        parsed = urlparse(url)
    except Exception as e:
        return {"tier": "unknown", "url": url, "rationale": f"URL parse failed: {e}"}

    domain = parsed.netloc.lower()
    # Strip 'www.' prefix for matching
    if domain.startswith("www."):
        domain_no_www = domain[4:]
    else:
        domain_no_www = domain

    # Strip port if present
    domain = domain.split(":")[0]
    domain_no_www = domain_no_www.split(":")[0]

    # Check exact-match tiers first
    if domain in PRIMARY_DOMAIN_EXACT or domain_no_www in PRIMARY_DOMAIN_EXACT:
        return {"tier": "primary", "url": url, "rationale": f"Domain {domain} is in primary exact-match list (regulatory/court/official)"}

    if domain in PRIMARY_ACADEMIC or domain_no_www in PRIMARY_ACADEMIC:
        return {"tier": "primary", "url": url, "rationale": f"Domain {domain} is a peer-reviewed academic publication"}

    if domain in SECONDARY_NEWS or domain_no_www in SECONDARY_NEWS:
        return {"tier": "secondary", "url": url, "rationale": f"Domain {domain} is a mainstream news outlet"}

    if domain in SECONDARY_TRADE or domain_no_www in SECONDARY_TRADE:
        return {"tier": "secondary", "url": url, "rationale": f"Domain {domain} is established trade press"}

    if domain in SECONDARY_INVESTIGATIVE or domain_no_www in SECONDARY_INVESTIGATIVE:
        return {"tier": "secondary", "url": url, "rationale": f"Domain {domain} is investigative journalism"}

    if domain in TERTIARY_DOMAIN_EXACT or domain_no_www in TERTIARY_DOMAIN_EXACT:
        return {"tier": "tertiary", "url": url, "rationale": f"Domain {domain} is user-generated content (forum/social/review)"}

    # Pattern checks
    for pattern in TERTIARY_PATTERN:
        if pattern.match(domain):
            return {"tier": "tertiary", "url": url, "rationale": f"Domain {domain} matches tertiary pattern (blog hosting platform)"}

    # Suffix checks
    for suffix in PRIMARY_DOMAIN_SUFFIX:
        if domain.endswith(suffix):
            return {"tier": "primary", "url": url, "rationale": f"Domain {domain} has primary-tier suffix '{suffix}'"}

    # Contains checks
    for pattern in PRIMARY_DOMAIN_CONTAINS:
        if pattern in url.lower():
            return {"tier": "primary", "url": url, "rationale": f"URL contains primary-tier pattern '{pattern}'"}

    # Company-official heuristic (if subject keywords provided)
    if subject_keywords and is_likely_company_official(domain, subject_keywords):
        return {"tier": "primary", "url": url, "rationale": f"Domain {domain} appears to be the subject's official site (matches subject keywords)"}

    # Default for unknown: secondary (give benefit of doubt to legitimate-looking news/site)
    # But add a confidence note
    return {
        "tier": "secondary",
        "url": url,
        "rationale": f"Domain {domain} not in known lists; defaulting to secondary. Manual review recommended for high-stakes citations.",
        "confidence": "low",
    }


SAMPLE_URLS = [
    "https://www.sec.gov/cgi-bin/browse-edgar?action=getcompany&CIK=0000789019",
    "https://www.nytimes.com/2026/05/15/tech/microsoft-ai-strategy.html",
    "https://techcrunch.com/2026/05/01/microsoft-acquires-startup-x/",
    "https://news.ycombinator.com/item?id=123456",
    "https://glassdoor.com/Reviews/Microsoft-Corp-E1651.htm",
    "https://medium.com/@author/microsoft-foundry-deep-dive",
    "https://www.microsoft.com/en-us/about",
    "https://projects.propublica.org/nonprofits/organizations/123456789",
    "https://scholar.google.com/scholar?q=...",
    "https://www.federalregister.gov/documents/2026/05/01/...",
    "https://random-blog-i-just-found.com/microsoft-rumor",
]


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--url", help="URL to classify")
    parser.add_argument("--subject", help="Subject keywords (comma-separated) for company-official heuristic")
    parser.add_argument("--sample", action="store_true", help="Classify a batch of sample URLs")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    subject_kws = [s.strip() for s in args.subject.split(",")] if args.subject else None

    if args.sample:
        results = [classify(u, ["microsoft"]) for u in SAMPLE_URLS]
        if args.output == "json":
            print(json.dumps(results, indent=2))
        else:
            for r in results:
                tier = r["tier"].upper()
                marker = {"PRIMARY": "[1°]", "SECONDARY": "[2°]", "TERTIARY": "[3°]"}.get(tier, "[?]")
                print(f"{marker} {tier:<10s} {r['url']}")
                print(f"      {r['rationale']}")
        return 0
    elif args.url:
        result = classify(args.url, subject_kws)
        if args.output == "json":
            print(json.dumps(result, indent=2))
        else:
            print(f"Tier:      {result['tier'].upper()}")
            print(f"URL:       {result['url']}")
            print(f"Rationale: {result['rationale']}")
            if result.get("confidence"):
                print(f"Confidence: {result['confidence']}")
        return 0
    else:
        parser.print_help()
        return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
