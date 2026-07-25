#!/usr/bin/env python3
"""
seo_health_scorer.py — Weighted 0-100 SEO health score across 7 categories.

Inspired by the scoring methodology used in top SEO audit tools. Replaces
binary pass/fail with a quantified health score that enables trend tracking,
stakeholder reporting, and prioritized action plans.

Categories and default weights:
  Technical SEO:   22%  (crawlability, indexation, redirects, sitemaps, robots.txt)
  Content Quality: 23%  (thin content, duplicate, keyword stuffing, readability)
  On-Page SEO:     20%  (titles, metas, headings, internal links, alt text)
  Schema Markup:   10%  (JSON-LD, breadcrumbs, FAQ, product, article schemas)
  Performance:     10%  (Core Web Vitals thresholds: LCP, CLS, INP)
  AI Readiness:    10%  (answer-first format, citability, entity clarity)
  Images:           5%  (alt text, compression, lazy loading, format)

Each check within a category returns pass/warn/fail. Severity multipliers:
  pass = 1.0, warn = 0.5, fail = 0.0

Industry profiles adjust weights:
  SaaS      → Technical +5%, Content +5%, Schema -5%, Images -5%
  Ecommerce → Schema +5%, Images +5%, AI Readiness -5%, Content -5%
  Local     → On-Page +5%, Schema +5%, Technical -5%, AI Readiness -5%
  Publisher → Content +5%, AI Readiness +5%, Technical -5%, Schema -5%

Usage:
    python seo_health_scorer.py --checks checks.json
    python seo_health_scorer.py --checks checks.json --industry saas
    python seo_health_scorer.py --checks checks.json --json
    python seo_health_scorer.py --demo

Input format (checks.json):
    [
      {"category": "technical", "check": "robots.txt exists", "result": "pass", "severity": "critical"},
      {"category": "content", "check": "thin content pages", "result": "fail", "severity": "high", "detail": "12 pages < 300 words"},
      ...
    ]

Severity levels for priority ordering:
    critical — blocks indexation or causes penalties (fix immediately)
    high     — significantly impacts rankings (fix within 1 week)
    medium   — optimization opportunity (fix within 1 month)
    low      — backlog polish item
"""
from __future__ import annotations
import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

DEFAULT_WEIGHTS = {
    "technical": 0.22,
    "content": 0.23,
    "on_page": 0.20,
    "schema": 0.10,
    "performance": 0.10,
    "ai_readiness": 0.10,
    "images": 0.05,
}

INDUSTRY_ADJUSTMENTS = {
    "saas": {"technical": 0.05, "content": 0.05, "schema": -0.05, "images": -0.05},
    "ecommerce": {"schema": 0.05, "images": 0.05, "ai_readiness": -0.05, "content": -0.05},
    "local": {"on_page": 0.05, "schema": 0.05, "technical": -0.05, "ai_readiness": -0.05},
    "publisher": {"content": 0.05, "ai_readiness": 0.05, "technical": -0.05, "schema": -0.05},
}

RESULT_SCORES = {"pass": 1.0, "warn": 0.5, "fail": 0.0}
SEVERITY_ORDER = {"critical": 0, "high": 1, "medium": 2, "low": 3}

DEMO_CHECKS = [
    {"category": "technical", "check": "robots.txt exists", "result": "pass", "severity": "critical"},
    {"category": "technical", "check": "sitemap.xml valid", "result": "pass", "severity": "critical"},
    {"category": "technical", "check": "no redirect chains", "result": "warn", "severity": "high", "detail": "2 chains found (3-hop)"},
    {"category": "technical", "check": "canonical tags present", "result": "pass", "severity": "high"},
    {"category": "technical", "check": "mobile-friendly", "result": "pass", "severity": "critical"},
    {"category": "content", "check": "no thin pages (<300 words)", "result": "fail", "severity": "high", "detail": "8 pages under 300 words"},
    {"category": "content", "check": "no duplicate titles", "result": "pass", "severity": "medium"},
    {"category": "content", "check": "no keyword stuffing", "result": "pass", "severity": "medium"},
    {"category": "content", "check": "readability (Flesch 60-70)", "result": "warn", "severity": "low", "detail": "avg Flesch 52"},
    {"category": "on_page", "check": "title tags 50-60 chars", "result": "warn", "severity": "high", "detail": "4 pages over 60 chars"},
    {"category": "on_page", "check": "meta descriptions 150-160", "result": "fail", "severity": "medium", "detail": "12 pages missing meta description"},
    {"category": "on_page", "check": "H1 tags present and unique", "result": "pass", "severity": "high"},
    {"category": "on_page", "check": "internal linking (min 3 per page)", "result": "warn", "severity": "medium", "detail": "6 pages have <3 internal links"},
    {"category": "on_page", "check": "all images have alt text", "result": "fail", "severity": "medium", "detail": "23 images missing alt"},
    {"category": "schema", "check": "JSON-LD Organization schema", "result": "pass", "severity": "medium"},
    {"category": "schema", "check": "breadcrumb schema", "result": "fail", "severity": "medium", "detail": "no breadcrumb markup found"},
    {"category": "schema", "check": "article/product schema", "result": "pass", "severity": "medium"},
    {"category": "performance", "check": "LCP < 2.5s", "result": "pass", "severity": "critical"},
    {"category": "performance", "check": "CLS < 0.1", "result": "warn", "severity": "high", "detail": "CLS 0.14 on mobile"},
    {"category": "performance", "check": "INP < 200ms", "result": "pass", "severity": "high"},
    {"category": "ai_readiness", "check": "answer-first paragraphs", "result": "fail", "severity": "medium", "detail": "most H2s don't start with a direct answer"},
    {"category": "ai_readiness", "check": "entity clarity", "result": "warn", "severity": "low", "detail": "ambiguous entity references on 3 pages"},
    {"category": "images", "check": "WebP/AVIF format", "result": "warn", "severity": "low", "detail": "14 images still JPEG"},
    {"category": "images", "check": "lazy loading", "result": "pass", "severity": "medium"},
]


def get_weights(industry=None):
    weights = dict(DEFAULT_WEIGHTS)
    if industry and industry in INDUSTRY_ADJUSTMENTS:
        for cat, adj in INDUSTRY_ADJUSTMENTS[industry].items():
            weights[cat] = weights.get(cat, 0) + adj
    return weights


def score_checks(checks, industry=None):
    weights = get_weights(industry)
    by_category = defaultdict(list)
    for c in checks:
        cat = c.get("category", "other").lower().replace("-", "_").replace(" ", "_")
        by_category[cat].append(c)

    category_scores = {}
    all_findings = []

    for cat, cat_checks in by_category.items():
        if not cat_checks:
            continue
        total = 0.0
        for check in cat_checks:
            result = check.get("result", "fail").lower()
            total += RESULT_SCORES.get(result, 0.0)
            if result != "pass":
                all_findings.append({
                    "category": cat,
                    "check": check.get("check", ""),
                    "result": result,
                    "severity": check.get("severity", "medium"),
                    "detail": check.get("detail", ""),
                })
        cat_score = (total / len(cat_checks)) * 100 if cat_checks else 100
        category_scores[cat] = round(cat_score, 1)

    # Weighted overall score
    overall = 0.0
    total_weight = 0.0
    for cat, weight in weights.items():
        if cat in category_scores:
            overall += category_scores[cat] * weight
            total_weight += weight

    if total_weight > 0:
        overall = overall / total_weight
    else:
        overall = 0.0

    # Sort findings by severity
    all_findings.sort(key=lambda f: SEVERITY_ORDER.get(f["severity"], 99))

    # Quick wins: high/critical severity + likely fast fix
    quick_wins = [f for f in all_findings if f["severity"] in ("critical", "high") and f["result"] == "warn"]

    # Grade
    if overall >= 90:
        grade = "A"
    elif overall >= 75:
        grade = "B"
    elif overall >= 60:
        grade = "C"
    elif overall >= 40:
        grade = "D"
    else:
        grade = "F"

    return {
        "overall_score": round(overall, 1),
        "grade": grade,
        "industry": industry or "general",
        "weights_used": {k: round(v, 2) for k, v in weights.items()},
        "category_scores": category_scores,
        "total_checks": len(checks),
        "passed": sum(1 for c in checks if c.get("result") == "pass"),
        "warnings": sum(1 for c in checks if c.get("result") == "warn"),
        "failures": sum(1 for c in checks if c.get("result") == "fail"),
        "findings": all_findings,
        "quick_wins": quick_wins,
        "action_plan": {
            "critical": [f for f in all_findings if f["severity"] == "critical"],
            "high": [f for f in all_findings if f["severity"] == "high"],
            "medium": [f for f in all_findings if f["severity"] == "medium"],
            "low": [f for f in all_findings if f["severity"] == "low"],
        },
    }


def print_report(result):
    print(f"SEO Health Score: {result['overall_score']}/100 (Grade: {result['grade']})")
    print(f"Industry profile: {result['industry']}")
    print(f"Checks: {result['total_checks']} total — {result['passed']} pass, {result['warnings']} warn, {result['failures']} fail")
    print()

    print("Category Breakdown:")
    for cat, score in sorted(result["category_scores"].items()):
        weight = result["weights_used"].get(cat, 0)
        bar = "█" * int(score / 5) + "░" * (20 - int(score / 5))
        print(f"  {cat:15s} {bar} {score:5.1f}/100 (weight {weight:.0%})")
    print()

    if result["quick_wins"]:
        print(f"Quick Wins ({len(result['quick_wins'])}):")
        for f in result["quick_wins"]:
            print(f"  ⚡ [{f['severity'].upper()}] {f['check']}: {f['detail']}")
        print()

    for level in ("critical", "high", "medium", "low"):
        items = result["action_plan"][level]
        if items:
            print(f"{level.upper()} ({len(items)}):")
            for f in items:
                detail = f" — {f['detail']}" if f["detail"] else ""
                print(f"  [{f['result'].upper()}] {f['check']}{detail}")
            print()


def main():
    p = argparse.ArgumentParser(
        description="Compute a weighted 0-100 SEO health score across 7 categories.",
        epilog="Run with --demo to see a sample report. Provide checks as JSON for real audits.",
    )
    p.add_argument("--checks", help="Path to checks JSON file (array of check objects)")
    p.add_argument(
        "--industry",
        choices=["saas", "ecommerce", "local", "publisher"],
        default=None,
        help="Industry profile adjusts category weights",
    )
    p.add_argument("--json", action="store_true", help="JSON output")
    p.add_argument("--demo", action="store_true", help="Run with demo data")
    args = p.parse_args()

    if args.demo:
        checks = DEMO_CHECKS
    elif args.checks:
        path = Path(args.checks)
        if not path.exists():
            print(f"[error] {path} not found", file=sys.stderr)
            sys.exit(1)
        checks = json.loads(path.read_text(encoding="utf-8"))
    else:
        p.print_help()
        sys.exit(0)

    result = score_checks(checks, industry=args.industry)

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print_report(result)


if __name__ == "__main__":
    main()
