#!/usr/bin/env python3
"""
aeo_audit.py — Answer Engine Optimization audit tool.

Audits content for E-E-A-T (Experience, Expertise, Authoritativeness,
Trustworthiness) signals + structural readiness for LLM citation.
Composite score 0-100 with per-dimension breakdown.

Stdlib only. No external deps. URL mode uses urllib (no requests/bs4 required).

Industry-aware: --industry flag adjusts thresholds for healthcare, finance,
legal, saas, ecommerce, b2b, media, education.

Usage:
  python3 aeo_audit.py --input post.md                   # audit a local markdown file
  python3 aeo_audit.py --input post.md --industry healthcare
  python3 aeo_audit.py --url https://example.com/post    # audit a live URL (HTML)
  python3 aeo_audit.py --sample                          # built-in demo
  python3 aeo_audit.py --input post.md --output json     # JSON output

Source: distilled from aeo-box content_analyzer.py + utils.py.
"""

import argparse
import json
import re
import sys
import urllib.request
import urllib.error
from datetime import datetime
from pathlib import Path
from typing import Any


# ─────────────────────────────────────────────────────────────────────────
# Industry-specific thresholds (from aeo-box success_patterns.py + CLAUDE.md)
# ─────────────────────────────────────────────────────────────────────────

INDUSTRIES = {
    "saas":       {"min_composite": 70, "critical": ["author_bio", "case_study_metrics"]},
    "healthcare": {"min_composite": 85, "critical": ["medical_reviewer", "peer_review_citations", "fda_disclosure"]},
    "finance":    {"min_composite": 85, "critical": ["credentials_cfa_cpa", "investment_disclaimer", "dated_examples"]},
    "legal":      {"min_composite": 85, "critical": ["jurisdiction", "attorney_bio", "legal_disclaimer"]},
    "ecommerce":  {"min_composite": 65, "critical": ["product_reviews", "return_policy", "schema_product"]},
    "b2b":        {"min_composite": 70, "critical": ["analyst_quotes", "customer_logos", "roi_data"]},
    "media":      {"min_composite": 70, "critical": ["editorial_policy", "fact_check_link", "original_reporting"]},
    "education":  {"min_composite": 75, "critical": ["instructor_bio", "learning_outcomes"]},
}


# ─────────────────────────────────────────────────────────────────────────
# Signal extraction (pattern-based, deterministic — no LLM)
# ─────────────────────────────────────────────────────────────────────────

# Experience signals: first-person evidence, dated examples, case studies
EXPERIENCE_PATTERNS = [
    (r"\b(we|our|i|my)\s+(ran|tested|tried|built|launched|measured|implemented)\b", "first_person_evidence"),
    (r"\bin\s+(20\d{2})\b", "dated_example"),
    (r"\b(case\s+study|customer\s+story|results?:?)\b", "case_study_marker"),
    (r"\b(\$|usd|eur|€|£)\s*\d+[\d,.]*\b", "monetary_evidence"),
    (r"\b\d+(\.\d+)?\s*(%|percent)\b", "metric_evidence"),
]

# Expertise signals: credentials, citations, author depth
EXPERTISE_PATTERNS = [
    (r"\b(phd|md|cpa|cfa|esq|jd|md|do|rn|mba|ba|bs|ms|msc|pe)\b\.?", "credential_marker"),
    (r"\bauthor:?\s+", "author_byline"),
    (r"\b(peer[-\s]?review(ed)?|journal|published\s+in)\b", "academic_citation"),
    (r"\[(\d+)\]", "numbered_citation"),
    (r"\bsource:?\s*https?://", "source_link"),
]

# Authoritativeness signals: external domains, schema markup, structured data
AUTHORITY_PATTERNS = [
    (r"https?://[^\s\)\]]+", "external_link"),
    (r'"@type"\s*:\s*"[A-Z][a-zA-Z]+"', "schema_org_jsonld"),
    (r"<script[^>]*application/ld\+json", "schema_script"),
    (r"\bschema\.org/[A-Z][a-zA-Z]+\b", "schema_inline"),
]

# Trustworthiness signals: HTTPS, contact, corrections, disclosures
TRUST_PATTERNS = [
    (r"\bhttps://", "https"),
    (r"\b(contact|email|reach\s+us|get\s+in\s+touch)\b", "contact_marker"),
    (r"\b(corrections?|updated|edited|revised)\s+(on|policy|process)\b", "corrections_policy"),
    (r"\bdisclos(ure|ed?)\b", "disclosure"),
    (r"\b(privacy\s+policy|terms\s+of\s+service|gdpr|ccpa)\b", "policy_link"),
]


def count_signals(text: str, patterns: list) -> dict:
    """Count signal hits per pattern. Returns {signal_name: hit_count}."""
    counts = {name: 0 for _, name in patterns}
    for pattern, name in patterns:
        hits = re.findall(pattern, text, flags=re.IGNORECASE)
        counts[name] = len(hits)
    return counts


def score_dimension(signals: dict, scale: int = 100) -> int:
    """Convert signal counts into a 0-scale score using diminishing returns.

    Score = scale * (1 - 1/(1 + total_hits * 0.3)). Soft saturation curve.
    """
    total = sum(signals.values())
    if total == 0:
        return 0
    score = scale * (1.0 - 1.0 / (1.0 + total * 0.3))
    return min(int(round(score)), scale)


# ─────────────────────────────────────────────────────────────────────────
# Content fetching
# ─────────────────────────────────────────────────────────────────────────

def fetch_url(url: str, timeout: int = 15) -> str | None:
    """Fetch raw HTML from URL using urllib (stdlib). Returns None on failure."""
    try:
        req = urllib.request.Request(
            url,
            headers={"User-Agent": "Mozilla/5.0 (aeo_audit.py; stdlib urllib)"}
        )
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.read().decode("utf-8", errors="replace")
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError) as e:
        sys.stderr.write(f"[aeo_audit] URL fetch failed: {e}\n")
        return None


def strip_html(html: str) -> str:
    """Crude HTML-to-text. For audit purposes — we score signals on the
    text + the raw HTML (so schema.org JSON-LD blocks are still detected)."""
    # Keep <script type="application/ld+json"> blocks (they're scorable signal)
    return html


# ─────────────────────────────────────────────────────────────────────────
# Structure analysis
# ─────────────────────────────────────────────────────────────────────────

def analyze_structure(text: str) -> dict:
    """Score H2/H3 structure, list density, table presence — LLM parsability signals."""
    h2_count = len(re.findall(r"^##\s+|^<h2\b", text, flags=re.MULTILINE | re.IGNORECASE))
    h3_count = len(re.findall(r"^###\s+|^<h3\b", text, flags=re.MULTILINE | re.IGNORECASE))
    list_items = len(re.findall(r"^\s*[-*+]\s+|<li\b", text, flags=re.MULTILINE | re.IGNORECASE))
    table_count = len(re.findall(r"^\|.*\|\s*$|<table\b", text, flags=re.MULTILINE | re.IGNORECASE))
    word_count = len(text.split())

    # Structure score: bonus for diverse element types
    structure_score = 0
    if h2_count >= 3: structure_score += 25
    elif h2_count >= 1: structure_score += 15
    if h3_count >= 3: structure_score += 15
    if list_items >= 5: structure_score += 20
    if table_count >= 1: structure_score += 20
    if word_count >= 800: structure_score += 20

    return {
        "h2_count": h2_count,
        "h3_count": h3_count,
        "list_items": list_items,
        "table_count": table_count,
        "word_count": word_count,
        "structure_score": min(structure_score, 100),
    }


# ─────────────────────────────────────────────────────────────────────────
# Main audit logic
# ─────────────────────────────────────────────────────────────────────────

def audit(text: str, url: str | None, industry: str) -> dict:
    """Run full audit. Returns structured result."""
    exp_signals = count_signals(text, EXPERIENCE_PATTERNS)
    expert_signals = count_signals(text, EXPERTISE_PATTERNS)
    auth_signals = count_signals(text, AUTHORITY_PATTERNS)
    trust_signals = count_signals(text, TRUST_PATTERNS)

    exp_score = score_dimension(exp_signals)
    expert_score = score_dimension(expert_signals)
    auth_score = score_dimension(auth_signals)
    trust_score = score_dimension(trust_signals)

    structure = analyze_structure(text)

    # Composite: weighted average of 4 E-E-A-T + structure
    composite = int(round(
        (exp_score + expert_score + auth_score + trust_score) * 0.20
        + structure["structure_score"] * 0.20
    ))

    cfg = INDUSTRIES.get(industry.lower(), INDUSTRIES["saas"])
    threshold = cfg["min_composite"]
    verdict = "PASS" if composite >= threshold else "BELOW_THRESHOLD"

    # Generate top fixes (heuristic — lowest-scoring dimensions first)
    dimensions = [
        ("Experience", exp_score, _fix_for_experience(exp_signals)),
        ("Expertise", expert_score, _fix_for_expertise(expert_signals)),
        ("Authoritativeness", auth_score, _fix_for_authority(auth_signals)),
        ("Trustworthiness", trust_score, _fix_for_trust(trust_signals)),
        ("Structure", structure["structure_score"], _fix_for_structure(structure)),
    ]
    dimensions_sorted = sorted(dimensions, key=lambda d: d[1])
    top_fixes = [(name, fix) for name, score, fix in dimensions_sorted if fix][:5]

    return {
        "url": url,
        "industry": industry,
        "audited_at": datetime.utcnow().isoformat() + "Z",
        "composite_score": composite,
        "verdict": verdict,
        "threshold": threshold,
        "letter_grade": _letter_grade(composite),
        "dimensions": {
            "experience": {"score": exp_score, "signals": exp_signals},
            "expertise": {"score": expert_score, "signals": expert_signals},
            "authoritativeness": {"score": auth_score, "signals": auth_signals},
            "trustworthiness": {"score": trust_score, "signals": trust_signals},
            "structure": structure,
        },
        "top_fixes": top_fixes,
        "audit_trail": {
            "patterns_evaluated": len(EXPERIENCE_PATTERNS) + len(EXPERTISE_PATTERNS) + len(AUTHORITY_PATTERNS) + len(TRUST_PATTERNS),
            "text_length_chars": len(text),
            "text_length_words": structure["word_count"],
        },
    }


def _letter_grade(score: int) -> str:
    if score >= 90: return "A"
    if score >= 85: return "A-"
    if score >= 80: return "B+"
    if score >= 75: return "B"
    if score >= 70: return "B-"
    if score >= 65: return "C+"
    if score >= 60: return "C"
    if score >= 50: return "D"
    return "F"


def _fix_for_experience(s: dict) -> str | None:
    if s["first_person_evidence"] == 0:
        return "Add first-person evidence (\"we ran X\", \"we tested Y\") in first 200 words"
    if s["dated_example"] == 0:
        return "Add at least one dated example with a specific year (e.g., \"in 2026, we observed...\")"
    if s["metric_evidence"] == 0:
        return "Include at least one quantitative result (% or dollar figure)"
    return None


def _fix_for_expertise(s: dict) -> str | None:
    if s["credential_marker"] == 0:
        return "Add author credentials (PhD, MD, CFA, CPA, etc.) in byline or bio"
    if s["numbered_citation"] == 0:
        return "Add numbered citations [1], [2], ... pointing to primary sources"
    if s["source_link"] == 0:
        return "Link to primary sources for any factual claim"
    return None


def _fix_for_authority(s: dict) -> str | None:
    if s["schema_org_jsonld"] == 0 and s["schema_script"] == 0:
        return "Add schema.org JSON-LD markup for Article + FAQPage + Author"
    if s["external_link"] < 3:
        return "Link to at least 3 authoritative external sources"
    return None


def _fix_for_trust(s: dict) -> str | None:
    if s["https"] == 0:
        return "Migrate to HTTPS (critical for AEO trust signal)"
    if s["corrections_policy"] == 0:
        return "Link to a corrections policy from footer or article"
    if s["disclosure"] == 0:
        return "Add transparency disclosure (affiliations, sponsorships, conflicts of interest)"
    return None


def _fix_for_structure(s: dict) -> str | None:
    if s["h2_count"] < 3:
        return f"Add more H2 headings ({s['h2_count']} → target 3+) to improve LLM parsability"
    if s["list_items"] < 5:
        return "Convert key claims into bulleted or numbered lists for LLM extraction"
    if s["word_count"] < 800:
        return f"Expand content ({s['word_count']} → target 800+ words) for citation worthiness"
    return None


def render_markdown(result: dict) -> str:
    """Render the audit result as a markdown report."""
    lines = []
    title = result.get("url") or "AEO Audit Report"
    lines.append(f"# AEO Audit Report — {title}")
    lines.append("")
    if result.get("url"):
        lines.append(f"**URL:** {result['url']}")
    lines.append(f"**Date:** {result['audited_at']}")
    lines.append(f"**Industry:** {result['industry']}")
    lines.append(f"**Composite Score:** {result['composite_score']}/100 ({result['letter_grade']})")
    lines.append(f"**Verdict:** {result['verdict']} (industry threshold: {result['threshold']})")
    lines.append("")
    lines.append("## Dimension Breakdown")
    lines.append("")
    lines.append("| Dimension | Score |")
    lines.append("|---|---|")
    dims = result["dimensions"]
    for key in ["experience", "expertise", "authoritativeness", "trustworthiness"]:
        lines.append(f"| {key.title()} | {dims[key]['score']}/100 |")
    lines.append(f"| Structure | {dims['structure']['structure_score']}/100 |")
    lines.append("")
    lines.append("## Top Fixes (Priority Order)")
    lines.append("")
    for i, (name, fix) in enumerate(result["top_fixes"], 1):
        lines.append(f"{i}. **{name}** — {fix}")
    lines.append("")
    lines.append("## Audit Trail")
    lines.append("")
    a = result["audit_trail"]
    lines.append(f"- Patterns evaluated: {a['patterns_evaluated']}")
    lines.append(f"- Text length: {a['text_length_words']} words ({a['text_length_chars']} chars)")
    return "\n".join(lines)


SAMPLE_CONTENT = """# Why AEO Matters in 2026

By Jane Doe, MBA — Content Strategist at Acme

In 2026, we ran an experiment across 300 client pages. We optimized 150 for traditional SEO
and 150 for AEO (E-E-A-T + schema.org markup). The AEO cohort received 47% more LLM citations
across ChatGPT and Perplexity over 90 days. [Source: https://example.com/study]

## What Is Answer Engine Optimization?

Answer Engine Optimization (AEO) is the practice of optimizing content for LLMs (large
language models). It complements SEO but optimizes for citation, not click-through.

## Key Signals That Drive Citation

- E-E-A-T: Experience, Expertise, Authoritativeness, Trustworthiness
- Schema.org structured data (FAQPage, HowTo, Article)
- Author bio with credentials and contact

| Signal | SEO weight | AEO weight |
|---|---|---|
| Backlinks | High | Medium |
| Author credentials | Low | High |
| Schema markup | Medium | High |

Contact us at info@acme.com for our corrections policy.
"""


def main():
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("--input", help="Path to markdown/HTML file to audit")
    p.add_argument("--url", help="Live URL to fetch + audit")
    p.add_argument("--industry", default="saas", choices=list(INDUSTRIES.keys()),
                   help="Industry-aware thresholds (default: saas)")
    p.add_argument("--output", choices=["markdown", "json"], default="markdown",
                   help="Output format (default: markdown)")
    p.add_argument("--sample", action="store_true",
                   help="Run with built-in sample content")
    args = p.parse_args()

    if args.sample:
        text = SAMPLE_CONTENT
        url = "sample://acme/blog/aeo-2026"
    elif args.input:
        text = Path(args.input).read_text(encoding="utf-8")
        url = None
    elif args.url:
        text = fetch_url(args.url)
        if text is None:
            sys.exit(1)
        url = args.url
    else:
        p.error("must specify --input, --url, or --sample")

    result = audit(text, url, args.industry)

    if args.output == "json":
        print(json.dumps(result, indent=2, default=str))
    else:
        print(render_markdown(result))


if __name__ == "__main__":
    main()
