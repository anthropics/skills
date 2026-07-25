#!/usr/bin/env python3
"""
spend_categorizer.py — UNSPSC-aligned spend categorization + Pareto + YoY growth.

Maps each line item to a UNSPSC-aligned Class -> Family -> Segment using a built-in
category map (~30 categories tuned for tech-company spend; NOT the full UNSPSC DB).
Computes Pareto (which 20% of categories drive 80% of spend?) and YoY growth when
prior-year data is supplied.

Industry profiles re-prioritize category matching:
  tech-startup | scaleup | enterprise | services | manufacturing

Stdlib only. Deterministic. No LLM calls.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


# ---------- Built-in UNSPSC-aligned category map ----------
# Shape: keyword -> (Segment, Family, Class)
# Segment is the top-level UNSPSC segment number range concept; we use plain names
# so the artifact reads cleanly without requiring the full 100k UNSPSC codeset.

CATEGORY_MAP: list[tuple[list[str], tuple[str, str, str]]] = [
    # Software / SaaS
    (["saas", "software license", "subscription", "seat license"],
     ("Information Technology", "Software", "SaaS / Subscription Software")),
    (["crm", "salesforce", "hubspot"],
     ("Information Technology", "Software", "CRM Platform")),
    (["monitoring", "datadog", "new relic", "grafana", "splunk", "observability"],
     ("Information Technology", "Software", "Monitoring / Observability")),
    (["expense", "ramp", "brex", "expensify", "navan", "concur"],
     ("Information Technology", "Software", "Expense / Spend Management")),
    (["email marketing", "mailchimp", "klaviyo", "marketo", "iterable", "sendgrid"],
     ("Marketing", "MarTech", "Email Marketing Platform")),
    (["analytics", "amplitude", "mixpanel", "heap", "ga4"],
     ("Information Technology", "Software", "Product Analytics")),
    (["hris", "hr software", "workday", "rippling", "gusto", "bamboohr"],
     ("Human Resources", "Software", "HRIS / Payroll")),
    (["ats", "applicant tracking", "greenhouse", "lever"],
     ("Human Resources", "Software", "Applicant Tracking System")),
    (["security software", "okta", "1password", "snyk", "wiz", "crowdstrike"],
     ("Information Technology", "Security", "Security Tooling")),
    (["data warehouse", "snowflake", "bigquery", "databricks", "redshift"],
     ("Information Technology", "Cloud Infrastructure", "Data Warehouse")),
    # Cloud Infrastructure
    (["aws", "amazon web services", "ec2", "s3"],
     ("Information Technology", "Cloud Infrastructure", "AWS")),
    (["gcp", "google cloud"],
     ("Information Technology", "Cloud Infrastructure", "GCP")),
    (["azure", "microsoft azure"],
     ("Information Technology", "Cloud Infrastructure", "Azure")),
    (["cloudflare", "cdn", "fastly", "akamai"],
     ("Information Technology", "Cloud Infrastructure", "CDN / Edge")),
    # Hardware
    (["laptop", "macbook", "thinkpad", "computer", "workstation"],
     ("Information Technology", "Hardware", "Endpoint Devices")),
    (["monitor", "display", "peripheral", "keyboard", "mouse"],
     ("Information Technology", "Hardware", "Peripherals")),
    # Professional Services
    (["legal services", "law firm", "outside counsel"],
     ("Professional Services", "Legal", "Outside Counsel")),
    (["accounting", "audit", "tax", "cpa", "deloitte", "pwc", "ey", "kpmg"],
     ("Professional Services", "Accounting", "Audit / Tax / Accounting")),
    (["consulting", "consultant", "advisory", "mckinsey", "bcg"],
     ("Professional Services", "Consulting", "Management Consulting")),
    (["contractor", "agency", "freelance"],
     ("Professional Services", "Contract Labor", "Contractor / Freelance")),
    # Marketing Services
    (["advertising", "google ads", "facebook ads", "linkedin ads", "ppc"],
     ("Marketing", "Advertising", "Paid Media")),
    (["content", "copywriting", "blog", "seo agency"],
     ("Marketing", "Content", "Content Production")),
    (["event", "conference", "trade show", "sponsorship"],
     ("Marketing", "Events", "Events / Sponsorship")),
    # Recruiting
    (["recruiting", "headhunter", "executive search", "linkedin recruiter"],
     ("Human Resources", "Recruiting", "Recruiting Services")),
    # Travel
    (["travel", "flight", "airfare", "hotel", "lodging", "uber", "lyft"],
     ("General & Administrative", "Travel", "Travel")),
    # Office / Facilities
    (["office", "rent", "lease", "wework", "coworking", "facilities"],
     ("General & Administrative", "Facilities", "Office / Rent")),
    (["utilities", "electric", "internet", "phone"],
     ("General & Administrative", "Facilities", "Utilities")),
    # Insurance / Benefits
    (["insurance", "liability", "d&o", "cyber insurance"],
     ("General & Administrative", "Insurance", "Business Insurance")),
    (["benefits", "health insurance", "401k", "dental", "vision"],
     ("Human Resources", "Benefits", "Employee Benefits")),
]

UNCATEGORIZED = ("Uncategorized", "Uncategorized", "Uncategorized")


# ---------- Industry profile priorities ----------
# Profiles influence which category is selected when multiple keywords match.
# The first-listed category in the priority list wins ties.

PROFILE_PRIORITIES: dict[str, list[str]] = {
    "tech-startup": [
        "SaaS / Subscription Software",
        "AWS", "GCP", "Azure",
        "Monitoring / Observability",
        "Data Warehouse",
        "Security Tooling",
        "Contractor / Freelance",
    ],
    "scaleup": [
        "Recruiting Services",
        "CRM Platform",
        "Paid Media",
        "Email Marketing Platform",
        "HRIS / Payroll",
        "SaaS / Subscription Software",
    ],
    "enterprise": [
        "Management Consulting",
        "Outside Counsel",
        "Audit / Tax / Accounting",
        "Office / Rent",
        "Employee Benefits",
        "Business Insurance",
    ],
    "services": [
        "Contractor / Freelance",
        "Outside Counsel",
        "Travel",
        "SaaS / Subscription Software",
    ],
    "manufacturing": [
        "Endpoint Devices",
        "Peripherals",
        "Office / Rent",
        "Utilities",
        "Business Insurance",
    ],
}


# ---------- Data model ----------

@dataclass
class LineItem:
    supplier: str
    description: str
    category_hint: str
    annual_spend: float
    frequency: str = "annual"
    currency: str = "USD"
    prior_year_spend: float | None = None

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> "LineItem":
        return cls(
            supplier=str(d.get("supplier", "")).strip(),
            description=str(d.get("description", "")).strip(),
            category_hint=str(d.get("category_hint", "")).strip(),
            annual_spend=float(d.get("annual_spend", 0.0)),
            frequency=str(d.get("frequency", "annual")),
            currency=str(d.get("currency", "USD")),
            prior_year_spend=(
                float(d["prior_year_spend"])
                if d.get("prior_year_spend") is not None
                else None
            ),
        )


@dataclass
class Categorized:
    item: LineItem
    segment: str
    family: str
    class_: str


# ---------- Categorization ----------

def categorize(item: LineItem, profile: str) -> Categorized:
    """Categorize one line item using keyword match + profile priority for ties."""
    haystack = " ".join([item.supplier, item.description, item.category_hint]).lower()

    matches: list[tuple[str, str, str]] = []
    for keywords, cat in CATEGORY_MAP:
        for kw in keywords:
            if kw in haystack:
                matches.append(cat)
                break

    if not matches:
        seg, fam, cls = UNCATEGORIZED
        return Categorized(item, seg, fam, cls)

    # Resolve tie using profile priority list
    priority = PROFILE_PRIORITIES.get(profile, [])
    for pri_class in priority:
        for seg, fam, cls in matches:
            if cls == pri_class:
                return Categorized(item, seg, fam, cls)

    # No priority match → first match wins (deterministic order)
    seg, fam, cls = matches[0]
    return Categorized(item, seg, fam, cls)


# ---------- Aggregation ----------

def aggregate_by_class(items: list[Categorized]) -> dict[str, dict[str, Any]]:
    agg: dict[str, dict[str, Any]] = {}
    for c in items:
        bucket = agg.setdefault(c.class_, {
            "segment": c.segment,
            "family": c.family,
            "class": c.class_,
            "spend": 0.0,
            "prior_year_spend": 0.0,
            "supplier_count": 0,
            "suppliers": set(),
        })
        bucket["spend"] += c.item.annual_spend
        if c.item.prior_year_spend is not None:
            bucket["prior_year_spend"] += c.item.prior_year_spend
        bucket["suppliers"].add(c.item.supplier)
    for b in agg.values():
        b["supplier_count"] = len(b["suppliers"])
        b["suppliers"] = sorted(b["suppliers"])
    return agg


def pareto_breakdown(agg: dict[str, dict[str, Any]]) -> tuple[list[str], float, float]:
    """Return the 20% of categories driving most spend, and the cumulative % they cover."""
    sorted_cats = sorted(agg.items(), key=lambda kv: -kv[1]["spend"])
    total_spend = sum(b["spend"] for b in agg.values()) or 1.0
    top_20_count = max(1, len(sorted_cats) // 5)
    top_classes = [cls for cls, _ in sorted_cats[:top_20_count]]
    top_spend = sum(agg[cls]["spend"] for cls in top_classes)
    return top_classes, top_spend, top_spend / total_spend * 100.0


def yoy_growth(agg: dict[str, dict[str, Any]]) -> list[tuple[str, float, float, float]]:
    """Return (class, this_year, prior_year, pct_growth) sorted by % growth desc."""
    rows: list[tuple[str, float, float, float]] = []
    for cls, b in agg.items():
        py = b["prior_year_spend"]
        ty = b["spend"]
        if py > 0:
            pct = (ty - py) / py * 100.0
            rows.append((cls, ty, py, pct))
    rows.sort(key=lambda r: -r[3])
    return rows


# ---------- Rendering ----------

def render_markdown(
    profile: str,
    categorized: list[Categorized],
    agg: dict[str, dict[str, Any]],
) -> str:
    total = sum(b["spend"] for b in agg.values())
    top_classes, top_spend, top_pct = pareto_breakdown(agg)

    lines: list[str] = []
    lines.append(f"# Categorized Spend Report ({profile} profile)\n")
    lines.append(f"- **Total annual spend:** ${total:,.0f}")
    lines.append(f"- **Line items:** {len(categorized)}")
    lines.append(f"- **Distinct categories (Class level):** {len(agg)}\n")

    lines.append("## Pareto: top 20% of categories\n")
    lines.append(f"Top {len(top_classes)} categories drive ${top_spend:,.0f} ({top_pct:.1f}% of spend):\n")
    for cls in top_classes:
        b = agg[cls]
        share = b["spend"] / (total or 1) * 100
        lines.append(f"- **{cls}** — ${b['spend']:,.0f} ({share:.1f}%), {b['supplier_count']} suppliers")
    lines.append("")

    lines.append("## All categories ranked by spend\n")
    lines.append("| Class | Family | Segment | Spend | Suppliers |")
    lines.append("|---|---|---|---:|---:|")
    for cls, b in sorted(agg.items(), key=lambda kv: -kv[1]["spend"]):
        lines.append(
            f"| {cls} | {b['family']} | {b['segment']} | "
            f"${b['spend']:,.0f} | {b['supplier_count']} |"
        )
    lines.append("")

    growth = yoy_growth(agg)
    if growth:
        lines.append("## Top YoY growth categories\n")
        lines.append("| Class | This year | Prior year | Growth |")
        lines.append("|---|---:|---:|---:|")
        for cls, ty, py, pct in growth[:10]:
            arrow = "↑" if pct > 0 else "↓"
            lines.append(f"| {cls} | ${ty:,.0f} | ${py:,.0f} | {arrow} {pct:+.1f}% |")
        lines.append("")

    # Per-line-item listing (for audit)
    lines.append("## Line items by category\n")
    by_class: dict[str, list[Categorized]] = {}
    for c in categorized:
        by_class.setdefault(c.class_, []).append(c)
    for cls in sorted(by_class.keys()):
        lines.append(f"### {cls}\n")
        lines.append("| Supplier | Description | Annual spend |")
        lines.append("|---|---|---:|")
        for c in sorted(by_class[cls], key=lambda x: -x.item.annual_spend):
            desc = c.item.description[:60]
            lines.append(f"| {c.item.supplier} | {desc} | ${c.item.annual_spend:,.0f} |")
        lines.append("")

    return "\n".join(lines)


# ---------- Sample data ----------

SAMPLE_INPUT: list[dict[str, Any]] = [
    {"supplier": "Datadog", "description": "Monitoring + APM", "category_hint": "monitoring",
     "annual_spend": 180000, "prior_year_spend": 120000},
    {"supplier": "New Relic", "description": "APM monitoring", "category_hint": "monitoring",
     "annual_spend": 90000, "prior_year_spend": 80000},
    {"supplier": "Grafana Cloud", "description": "metrics + logs monitoring",
     "category_hint": "monitoring", "annual_spend": 45000, "prior_year_spend": 0},
    {"supplier": "Ramp", "description": "corporate cards + expense", "category_hint": "expense",
     "annual_spend": 30000, "prior_year_spend": 18000},
    {"supplier": "Expensify", "description": "expense reimbursement", "category_hint": "expense",
     "annual_spend": 12000, "prior_year_spend": 12000},
    {"supplier": "Salesforce", "description": "CRM Enterprise", "category_hint": "crm",
     "annual_spend": 240000, "prior_year_spend": 200000},
    {"supplier": "AWS", "description": "EC2 + S3 + RDS", "category_hint": "cloud",
     "annual_spend": 720000, "prior_year_spend": 480000},
    {"supplier": "Snowflake", "description": "data warehouse", "category_hint": "data warehouse",
     "annual_spend": 360000, "prior_year_spend": 240000},
    {"supplier": "Klaviyo", "description": "email marketing platform",
     "category_hint": "email marketing", "annual_spend": 36000, "prior_year_spend": 24000},
    {"supplier": "Mailchimp", "description": "email marketing", "category_hint": "email marketing",
     "annual_spend": 8000, "prior_year_spend": 8000},
    {"supplier": "Iterable", "description": "email marketing", "category_hint": "email marketing",
     "annual_spend": 50000, "prior_year_spend": 0},
    {"supplier": "SendGrid", "description": "transactional email", "category_hint": "email",
     "annual_spend": 18000, "prior_year_spend": 12000},
    {"supplier": "Greenhouse", "description": "ATS", "category_hint": "applicant tracking",
     "annual_spend": 28000, "prior_year_spend": 24000},
    {"supplier": "Outside Counsel - Fenwick", "description": "legal services",
     "category_hint": "legal", "annual_spend": 95000, "prior_year_spend": 60000},
]


# ---------- CLI ----------

def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", type=str, help="Path to JSON list of spend line items")
    p.add_argument(
        "--profile",
        type=str,
        default="tech-startup",
        choices=sorted(PROFILE_PRIORITIES.keys()),
        help="Industry profile (default: tech-startup)",
    )
    p.add_argument("--output", type=str, help="Path to write markdown report")
    p.add_argument("--sample", action="store_true", help="Run with built-in sample data")
    args = p.parse_args(argv)

    if args.sample:
        data = SAMPLE_INPUT
    elif args.input:
        try:
            data = json.loads(Path(args.input).read_text())
        except Exception as e:
            print(f"error reading {args.input}: {e}", file=sys.stderr)
            return 2
    else:
        p.print_help()
        return 0

    items = [LineItem.from_dict(d) for d in data]
    categorized = [categorize(it, args.profile) for it in items]
    agg = aggregate_by_class(categorized)
    md = render_markdown(args.profile, categorized, agg)

    if args.output:
        Path(args.output).write_text(md)
        print(f"wrote {args.output}")
    else:
        print(md)
    return 0


if __name__ == "__main__":
    sys.exit(main())
