#!/usr/bin/env python3
"""
vendor_scorer.py — Multi-dimensional 0-100 vendor scoring with industry profile tuning.

Scores each vendor across 5 weighted dimensions:
  1. Reliability   — uptime % + incident count
  2. Support       — P90 ticket response hours
  3. Security      — security certifications coverage
  4. Commercial    — renewal flexibility
  5. Strategic fit — criticality vs annual spend

Industry profiles ({saas,fintech,healthcare,enterprise}) re-weight the dimensions.
Output: ranked markdown scorecard with per-dimension breakdown + verdict (KEEP/REVIEW/REPLACE).

Stdlib only. Deterministic. No LLM calls.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any


# ---------- Industry profile weights ----------

PROFILES: dict[str, dict[str, float]] = {
    "saas": {
        "reliability": 0.30,
        "support": 0.15,
        "security": 0.25,
        "commercial": 0.15,
        "strategic_fit": 0.15,
    },
    "fintech": {
        "reliability": 0.25,
        "support": 0.15,
        "security": 0.30,
        "commercial": 0.15,
        "strategic_fit": 0.15,
    },
    "healthcare": {
        "reliability": 0.25,
        "support": 0.15,
        "security": 0.35,
        "commercial": 0.10,
        "strategic_fit": 0.15,
    },
    "enterprise": {
        "reliability": 0.25,
        "support": 0.20,
        "security": 0.25,
        "commercial": 0.15,
        "strategic_fit": 0.15,
    },
}

CERT_VALUE: dict[str, int] = {
    "SOC2": 15,
    "SOC2-Type-II": 25,
    "ISO27001": 20,
    "HIPAA": 15,
    "PCI-DSS": 15,
    "FedRAMP": 20,
    "GDPR-DPA": 10,
    "CCPA": 5,
}

RENEWAL_SCORE: dict[str, int] = {
    "manual-renew": 100,
    "fixed-term": 80,
    "evergreen": 50,
    "auto-renew": 35,
}


# ---------- Data shape ----------


class Verdict(str, Enum):
    KEEP = "KEEP"
    REVIEW = "REVIEW"
    REPLACE = "REPLACE"


@dataclass
class DimensionBreakdown:
    reliability: float
    support: float
    security: float
    commercial: float
    strategic_fit: float

    def as_dict(self) -> dict[str, float]:
        return {
            "reliability": self.reliability,
            "support": self.support,
            "security": self.security,
            "commercial": self.commercial,
            "strategic_fit": self.strategic_fit,
        }


@dataclass
class ScoredVendor:
    name: str
    category: str
    annual_spend: float
    criticality: str
    overall: float
    verdict: Verdict
    dimensions: DimensionBreakdown
    notes: list[str] = field(default_factory=list)


# ---------- Per-dimension scoring (deterministic) ----------


def score_reliability(uptime_pct: float, incident_count: int) -> float:
    """Reliability = uptime_pct mapped to 0-100, penalized by incidents.

    99.95 uptime -> 95 points base. Each incident over 1 in the last 12m subtracts 5.
    """
    base = max(0.0, min(100.0, (uptime_pct - 95.0) * 20.0))  # 95.0 -> 0, 100.0 -> 100
    penalty = max(0, incident_count - 1) * 5
    return max(0.0, min(100.0, base - penalty))


def score_support(p90_hours: float) -> float:
    """Support = P90 ticket response hours mapped to 0-100.

    < 1h -> 100. 24h -> 50. 72h -> 0.
    """
    if p90_hours <= 1.0:
        return 100.0
    if p90_hours >= 72.0:
        return 0.0
    # Linear from (1, 100) to (72, 0)
    return max(0.0, min(100.0, 100.0 - ((p90_hours - 1.0) * 100.0 / 71.0)))


def score_security(certs: list[str], profile: str) -> float:
    """Security = sum of cert values, capped at 100. Healthcare/fintech demand more."""
    total = sum(CERT_VALUE.get(c, 0) for c in certs)
    # In healthcare and fintech, raw cert score is harder to max out
    if profile in {"healthcare", "fintech"}:
        total = total * 0.85
    return max(0.0, min(100.0, float(total)))


def score_commercial(renewal_terms: str) -> float:
    """Commercial = renewal flexibility. Manual renew > fixed-term > evergreen > auto-renew."""
    return float(RENEWAL_SCORE.get(renewal_terms, 50))


def score_strategic_fit(criticality: str, annual_spend: float) -> float:
    """Strategic fit = criticality vs spend alignment.

    Tier-1 paying < $50k -> 100 (high value, low cost).
    Tier-3 paying > $100k -> 20 (low value, high cost — kill candidate).
    """
    if criticality == "tier-1":
        if annual_spend < 50_000:
            return 100.0
        if annual_spend < 250_000:
            return 80.0
        return 60.0
    if criticality == "tier-2":
        if annual_spend < 25_000:
            return 90.0
        if annual_spend < 100_000:
            return 70.0
        return 50.0
    # tier-3
    if annual_spend < 10_000:
        return 70.0
    if annual_spend < 50_000:
        return 50.0
    return 20.0


def verdict_for(overall: float) -> Verdict:
    if overall >= 75:
        return Verdict.KEEP
    if overall >= 50:
        return Verdict.REVIEW
    return Verdict.REPLACE


def score_vendor(vendor: dict[str, Any], profile: str) -> ScoredVendor:
    weights = PROFILES[profile]
    rel = score_reliability(
        float(vendor.get("uptime_pct", 0.0)),
        int(vendor.get("incident_count_last_12m", 0)),
    )
    sup = score_support(float(vendor.get("support_response_hours_p90", 999.0)))
    sec = score_security(list(vendor.get("security_certs", [])), profile)
    com = score_commercial(str(vendor.get("renewal_terms", "auto-renew")))
    fit = score_strategic_fit(
        str(vendor.get("criticality", "tier-3")),
        float(vendor.get("annual_spend", 0.0)),
    )

    overall = (
        rel * weights["reliability"]
        + sup * weights["support"]
        + sec * weights["security"]
        + com * weights["commercial"]
        + fit * weights["strategic_fit"]
    )

    notes: list[str] = []
    if vendor.get("criticality") == "tier-1" and not vendor.get("security_certs"):
        notes.append("Tier-1 with no security certs — require SOC2-Type-II at renewal.")
    if vendor.get("renewal_terms") == "auto-renew" and float(vendor.get("annual_spend", 0)) > 50_000:
        notes.append("Auto-renew on $50k+ contract — renegotiate to manual-renew.")
    if int(vendor.get("incident_count_last_12m", 0)) >= 5:
        notes.append(
            f"{vendor['incident_count_last_12m']} incidents in 12m — request RCA + remediation plan."
        )

    return ScoredVendor(
        name=str(vendor.get("name", "Unknown")),
        category=str(vendor.get("category", "uncategorized")),
        annual_spend=float(vendor.get("annual_spend", 0.0)),
        criticality=str(vendor.get("criticality", "tier-3")),
        overall=round(overall, 1),
        verdict=verdict_for(overall),
        dimensions=DimensionBreakdown(
            reliability=round(rel, 1),
            support=round(sup, 1),
            security=round(sec, 1),
            commercial=round(com, 1),
            strategic_fit=round(fit, 1),
        ),
        notes=notes,
    )


# ---------- Markdown rendering ----------


def render_markdown(scored: list[ScoredVendor], profile: str) -> str:
    scored_sorted = sorted(scored, key=lambda s: s.overall, reverse=True)
    weights = PROFILES[profile]
    lines: list[str] = []
    lines.append(f"# Vendor Scorecard — `{profile}` profile")
    lines.append("")
    lines.append(
        f"Profile weights: reliability **{int(weights['reliability'] * 100)}%** · "
        f"support **{int(weights['support'] * 100)}%** · "
        f"security **{int(weights['security'] * 100)}%** · "
        f"commercial **{int(weights['commercial'] * 100)}%** · "
        f"strategic fit **{int(weights['strategic_fit'] * 100)}%**"
    )
    lines.append("")
    lines.append("## Ranked Scorecard")
    lines.append("")
    lines.append(
        "| Rank | Vendor | Category | Tier | Annual Spend | Overall | Verdict |"
    )
    lines.append("|---|---|---|---|---|---|---|")
    for i, sv in enumerate(scored_sorted, start=1):
        lines.append(
            f"| {i} | {sv.name} | {sv.category} | {sv.criticality} | "
            f"${sv.annual_spend:,.0f} | **{sv.overall}** | {sv.verdict.value} |"
        )
    lines.append("")

    lines.append("## Per-Dimension Breakdown")
    lines.append("")
    lines.append(
        "| Vendor | Reliability | Support | Security | Commercial | Strategic Fit |"
    )
    lines.append("|---|---|---|---|---|---|")
    for sv in scored_sorted:
        d = sv.dimensions
        lines.append(
            f"| {sv.name} | {d.reliability} | {d.support} | {d.security} | "
            f"{d.commercial} | {d.strategic_fit} |"
        )
    lines.append("")

    lines.append("## Verdict Summary")
    lines.append("")
    keep = [s for s in scored_sorted if s.verdict == Verdict.KEEP]
    review = [s for s in scored_sorted if s.verdict == Verdict.REVIEW]
    replace = [s for s in scored_sorted if s.verdict == Verdict.REPLACE]
    lines.append(f"- **KEEP ({len(keep)}):** " + (", ".join(s.name for s in keep) or "_none_"))
    lines.append(
        f"- **REVIEW ({len(review)}):** " + (", ".join(s.name for s in review) or "_none_")
    )
    lines.append(
        f"- **REPLACE ({len(replace)}):** " + (", ".join(s.name for s in replace) or "_none_")
    )
    lines.append("")

    flagged = [s for s in scored_sorted if s.notes]
    if flagged:
        lines.append("## Action Notes")
        lines.append("")
        for sv in flagged:
            lines.append(f"### {sv.name} ({sv.verdict.value} · {sv.overall})")
            for n in sv.notes:
                lines.append(f"- {n}")
            lines.append("")

    return "\n".join(lines)


# ---------- Sample data ----------


SAMPLE_CATALOG: list[dict[str, Any]] = [
    {
        "name": "Okta",
        "category": "identity",
        "annual_spend": 180_000,
        "contract_end_date": "2026-09-30",
        "criticality": "tier-1",
        "uptime_pct": 99.91,
        "support_response_hours_p90": 4.5,
        "incident_count_last_12m": 3,
        "security_certs": ["SOC2-Type-II", "ISO27001", "FedRAMP", "GDPR-DPA"],
        "renewal_terms": "manual-renew",
    },
    {
        "name": "Snowflake",
        "category": "data-warehouse",
        "annual_spend": 420_000,
        "contract_end_date": "2027-01-15",
        "criticality": "tier-1",
        "uptime_pct": 99.97,
        "support_response_hours_p90": 2.0,
        "incident_count_last_12m": 1,
        "security_certs": ["SOC2-Type-II", "ISO27001", "HIPAA", "GDPR-DPA"],
        "renewal_terms": "fixed-term",
    },
    {
        "name": "LegacyCRM",
        "category": "crm",
        "annual_spend": 95_000,
        "contract_end_date": "2026-06-30",
        "criticality": "tier-2",
        "uptime_pct": 98.20,
        "support_response_hours_p90": 38.0,
        "incident_count_last_12m": 11,
        "security_certs": ["SOC2"],
        "renewal_terms": "auto-renew",
    },
    {
        "name": "ChartingTool",
        "category": "analytics",
        "annual_spend": 8_000,
        "contract_end_date": "2026-08-01",
        "criticality": "tier-3",
        "uptime_pct": 99.50,
        "support_response_hours_p90": 14.0,
        "incident_count_last_12m": 2,
        "security_certs": ["SOC2", "GDPR-DPA"],
        "renewal_terms": "evergreen",
    },
    {
        "name": "BoutiqueQA",
        "category": "qa-services",
        "annual_spend": 220_000,
        "contract_end_date": "2026-12-31",
        "criticality": "tier-3",
        "uptime_pct": 99.00,
        "support_response_hours_p90": 22.0,
        "incident_count_last_12m": 6,
        "security_certs": [],
        "renewal_terms": "auto-renew",
    },
]


# ---------- CLI ----------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Score vendors 0-100 across 5 dimensions with industry profile tuning."
    )
    parser.add_argument("--input", type=Path, help="Path to JSON vendor catalog.")
    parser.add_argument(
        "--profile",
        choices=sorted(PROFILES.keys()),
        default="saas",
        help="Industry profile to use for dimension weighting (default: saas).",
    )
    parser.add_argument("--output", type=Path, help="Path to write markdown scorecard.")
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Run against built-in 5-vendor sample catalog.",
    )
    args = parser.parse_args(argv)

    if not args.sample and not args.input:
        parser.error("provide --input or --sample")

    if args.sample:
        catalog = SAMPLE_CATALOG
    else:
        try:
            catalog = json.loads(args.input.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            print(f"error reading {args.input}: {exc}", file=sys.stderr)
            return 2
        if not isinstance(catalog, list):
            print("input JSON must be a list of vendor objects", file=sys.stderr)
            return 2

    scored = [score_vendor(v, args.profile) for v in catalog]
    md = render_markdown(scored, args.profile)

    if args.output:
        args.output.write_text(md, encoding="utf-8")
        print(f"wrote {args.output}")
    else:
        print(md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
