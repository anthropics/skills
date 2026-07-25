#!/usr/bin/env python3
"""
vendor_risk_classifier.py — Classify third-party risk across 4 vectors.

Inspired by Shared Assessments SIG-Lite + NIST SP 800-161 supply chain risk.
Classifies each vendor as Critical / High / Medium / Low across:

  1. Data sensitivity      — PII / PHI / cardholder / source code access
  2. Financial exposure    — annual spend × tier multiplier
  3. Operational dependency — tier-1 + no break-glass = Critical
  4. Regulatory exposure   — industry profile drives weighting

Industry profile ({saas,fintech,healthcare,enterprise}) re-weights regulatory.

Output: risk matrix markdown + per-vendor mitigation recommendations.

Stdlib only. Deterministic. No LLM calls.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any


class RiskLevel(str, Enum):
    LOW = "Low"
    MEDIUM = "Medium"
    HIGH = "High"
    CRITICAL = "Critical"


_LEVEL_RANK = {
    RiskLevel.LOW: 0,
    RiskLevel.MEDIUM: 1,
    RiskLevel.HIGH: 2,
    RiskLevel.CRITICAL: 3,
}


@dataclass
class RiskBreakdown:
    data_sensitivity: RiskLevel
    financial_exposure: RiskLevel
    operational_dependency: RiskLevel
    regulatory_exposure: RiskLevel


@dataclass
class RiskClassification:
    vendor: str
    category: str
    overall: RiskLevel
    breakdown: RiskBreakdown
    mitigations: list[str]


# ---------- Per-vector classifiers ----------


_DATA_SENSITIVITY_KEYS = {
    "PHI": RiskLevel.CRITICAL,
    "PII": RiskLevel.HIGH,
    "cardholder": RiskLevel.CRITICAL,
    "source-code": RiskLevel.HIGH,
    "financial-records": RiskLevel.HIGH,
    "employee-records": RiskLevel.HIGH,
    "customer-emails": RiskLevel.MEDIUM,
    "logs-only": RiskLevel.LOW,
    "no-customer-data": RiskLevel.LOW,
}


def classify_data_sensitivity(vendor: dict[str, Any]) -> RiskLevel:
    """Choose worst of declared data_access tags. Default Medium if unspecified."""
    tags = vendor.get("data_access") or []
    if not tags:
        return RiskLevel.MEDIUM
    levels = [_DATA_SENSITIVITY_KEYS.get(t, RiskLevel.MEDIUM) for t in tags]
    return max(levels, key=lambda lv: _LEVEL_RANK[lv])


def classify_financial_exposure(vendor: dict[str, Any]) -> RiskLevel:
    spend = float(vendor.get("annual_spend", 0))
    crit = str(vendor.get("criticality", "tier-3"))
    multiplier = {"tier-1": 1.5, "tier-2": 1.0, "tier-3": 0.6}.get(crit, 0.6)
    weighted = spend * multiplier
    if weighted >= 500_000:
        return RiskLevel.CRITICAL
    if weighted >= 150_000:
        return RiskLevel.HIGH
    if weighted >= 50_000:
        return RiskLevel.MEDIUM
    return RiskLevel.LOW


def classify_operational_dependency(vendor: dict[str, Any]) -> RiskLevel:
    crit = str(vendor.get("criticality", "tier-3"))
    has_breakglass = bool(vendor.get("break_glass_plan", False))
    if crit == "tier-1" and not has_breakglass:
        return RiskLevel.CRITICAL
    if crit == "tier-1":
        return RiskLevel.HIGH
    if crit == "tier-2" and not has_breakglass:
        return RiskLevel.HIGH
    if crit == "tier-2":
        return RiskLevel.MEDIUM
    return RiskLevel.LOW


_REGULATORY_PROFILE: dict[str, dict[str, RiskLevel]] = {
    # Per-profile, mapping of cert presence to risk reduction.
    # Worst case before mitigations:
    # healthcare requires HIPAA, fintech requires SOC2-Type-II + PCI-DSS (if cardholder).
    "saas": {},
    "fintech": {},
    "healthcare": {},
    "enterprise": {},
}


def classify_regulatory_exposure(
    vendor: dict[str, Any], profile: str
) -> RiskLevel:
    certs = set(vendor.get("security_certs") or [])
    data_tags = set(vendor.get("data_access") or [])

    if profile == "healthcare":
        if "PHI" in data_tags and "HIPAA" not in certs:
            return RiskLevel.CRITICAL
        if "PHI" in data_tags:
            return RiskLevel.HIGH
        if "PII" in data_tags and "SOC2-Type-II" not in certs:
            return RiskLevel.HIGH
        return RiskLevel.MEDIUM

    if profile == "fintech":
        if "cardholder" in data_tags and "PCI-DSS" not in certs:
            return RiskLevel.CRITICAL
        if "cardholder" in data_tags:
            return RiskLevel.HIGH
        if "SOC2-Type-II" not in certs and "ISO27001" not in certs:
            return RiskLevel.HIGH
        return RiskLevel.MEDIUM

    if profile == "enterprise":
        if "PII" in data_tags and "SOC2-Type-II" not in certs:
            return RiskLevel.HIGH
        if "SOC2" not in certs and "SOC2-Type-II" not in certs:
            return RiskLevel.MEDIUM
        return RiskLevel.LOW

    # saas (default)
    if "PII" in data_tags and "SOC2" not in certs and "SOC2-Type-II" not in certs:
        return RiskLevel.HIGH
    if "PII" in data_tags:
        return RiskLevel.MEDIUM
    return RiskLevel.LOW


def overall_risk(breakdown: RiskBreakdown) -> RiskLevel:
    # Overall = worst-of, with one nuance: two HIGH vectors -> CRITICAL.
    levels = [
        breakdown.data_sensitivity,
        breakdown.financial_exposure,
        breakdown.operational_dependency,
        breakdown.regulatory_exposure,
    ]
    worst = max(levels, key=lambda lv: _LEVEL_RANK[lv])
    high_count = sum(1 for lv in levels if lv == RiskLevel.HIGH)
    if worst == RiskLevel.HIGH and high_count >= 2:
        return RiskLevel.CRITICAL
    return worst


def build_mitigations(
    vendor: dict[str, Any], breakdown: RiskBreakdown, profile: str
) -> list[str]:
    mits: list[str] = []
    certs = set(vendor.get("security_certs") or [])
    data_tags = set(vendor.get("data_access") or [])

    if breakdown.data_sensitivity in {RiskLevel.HIGH, RiskLevel.CRITICAL}:
        mits.append(
            "Confirm data-processing addendum (DPA) is current. Require encryption at rest + in transit."
        )
    if breakdown.financial_exposure in {RiskLevel.HIGH, RiskLevel.CRITICAL}:
        mits.append(
            "Require liability cap parity (≥ 12 months of fees). Confirm insurance certificate on file."
        )
    if breakdown.operational_dependency == RiskLevel.CRITICAL:
        mits.append(
            "Document a 72-hour break-glass plan. Identify and pre-qualify a backup vendor."
        )
    if breakdown.regulatory_exposure == RiskLevel.CRITICAL:
        if profile == "healthcare" and "HIPAA" not in certs:
            mits.append("Block PHI access until HIPAA BAA is signed and certs verified.")
        if profile == "fintech" and "cardholder" in data_tags and "PCI-DSS" not in certs:
            mits.append("Block cardholder data until PCI-DSS AOC (Attestation) is on file.")
    if breakdown.regulatory_exposure in {RiskLevel.HIGH, RiskLevel.CRITICAL}:
        mits.append("Request most recent SOC2 Type II report; review exceptions section.")
    if not mits:
        mits.append("No critical mitigations required; routine annual review.")
    return mits


def classify_vendor(vendor: dict[str, Any], profile: str) -> RiskClassification:
    breakdown = RiskBreakdown(
        data_sensitivity=classify_data_sensitivity(vendor),
        financial_exposure=classify_financial_exposure(vendor),
        operational_dependency=classify_operational_dependency(vendor),
        regulatory_exposure=classify_regulatory_exposure(vendor, profile),
    )
    return RiskClassification(
        vendor=str(vendor.get("name", "Unknown")),
        category=str(vendor.get("category", "uncategorized")),
        overall=overall_risk(breakdown),
        breakdown=breakdown,
        mitigations=build_mitigations(vendor, breakdown, profile),
    )


# ---------- Markdown rendering ----------


def render_markdown(results: list[RiskClassification], profile: str) -> str:
    by_overall = sorted(
        results, key=lambda r: _LEVEL_RANK[r.overall], reverse=True
    )
    lines: list[str] = []
    lines.append(f"# Vendor Risk Matrix — `{profile}` profile")
    lines.append("")

    crit = [r for r in by_overall if r.overall == RiskLevel.CRITICAL]
    high = [r for r in by_overall if r.overall == RiskLevel.HIGH]
    lines.append(
        f"**Summary:** {len(crit)} Critical · {len(high)} High · "
        f"{sum(1 for r in by_overall if r.overall == RiskLevel.MEDIUM)} Medium · "
        f"{sum(1 for r in by_overall if r.overall == RiskLevel.LOW)} Low"
    )
    lines.append("")

    lines.append("## Risk Matrix")
    lines.append("")
    lines.append(
        "| Vendor | Category | Data | Financial | Operational | Regulatory | Overall |"
    )
    lines.append("|---|---|---|---|---|---|---|")
    for r in by_overall:
        b = r.breakdown
        lines.append(
            f"| {r.vendor} | {r.category} | {b.data_sensitivity.value} | "
            f"{b.financial_exposure.value} | {b.operational_dependency.value} | "
            f"{b.regulatory_exposure.value} | **{r.overall.value}** |"
        )
    lines.append("")

    lines.append("## Mitigations")
    lines.append("")
    for r in by_overall:
        lines.append(f"### {r.vendor} — {r.overall.value}")
        for m in r.mitigations:
            lines.append(f"- {m}")
        lines.append("")

    return "\n".join(lines)


# ---------- Sample data ----------

SAMPLE_VENDORS: list[dict[str, Any]] = [
    {
        "name": "Okta",
        "category": "identity",
        "annual_spend": 180_000,
        "criticality": "tier-1",
        "data_access": ["PII", "employee-records"],
        "security_certs": ["SOC2-Type-II", "ISO27001", "FedRAMP", "GDPR-DPA"],
        "break_glass_plan": True,
    },
    {
        "name": "Snowflake",
        "category": "data-warehouse",
        "annual_spend": 420_000,
        "criticality": "tier-1",
        "data_access": ["PII", "PHI", "financial-records"],
        "security_certs": ["SOC2-Type-II", "ISO27001", "HIPAA", "GDPR-DPA"],
        "break_glass_plan": False,
    },
    {
        "name": "LegacyCRM",
        "category": "crm",
        "annual_spend": 95_000,
        "criticality": "tier-2",
        "data_access": ["PII", "customer-emails"],
        "security_certs": ["SOC2"],
        "break_glass_plan": False,
    },
    {
        "name": "ChartingTool",
        "category": "analytics",
        "annual_spend": 8_000,
        "criticality": "tier-3",
        "data_access": ["logs-only"],
        "security_certs": ["SOC2", "GDPR-DPA"],
        "break_glass_plan": True,
    },
    {
        "name": "BoutiqueQA",
        "category": "qa-services",
        "annual_spend": 220_000,
        "criticality": "tier-3",
        "data_access": ["source-code", "PII"],
        "security_certs": [],
        "break_glass_plan": False,
    },
]


# ---------- CLI ----------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Classify vendor risk across 4 vectors with industry profile tuning."
    )
    parser.add_argument("--input", type=Path, help="Path to JSON vendor catalog.")
    parser.add_argument(
        "--profile",
        choices=["saas", "fintech", "healthcare", "enterprise"],
        default="saas",
        help="Industry profile for regulatory weighting (default: saas).",
    )
    parser.add_argument("--output", type=Path, help="Path to write markdown risk matrix.")
    parser.add_argument(
        "--sample", action="store_true", help="Run against built-in 5-vendor sample."
    )
    args = parser.parse_args(argv)

    if not args.sample and not args.input:
        parser.error("provide --input or --sample")

    if args.sample:
        catalog = SAMPLE_VENDORS
    else:
        try:
            catalog = json.loads(args.input.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            print(f"error reading {args.input}: {exc}", file=sys.stderr)
            return 2
        if not isinstance(catalog, list):
            print("input JSON must be a list of vendor objects", file=sys.stderr)
            return 2

    results = [classify_vendor(v, args.profile) for v in catalog]
    md = render_markdown(results, args.profile)

    if args.output:
        args.output.write_text(md, encoding="utf-8")
        print(f"wrote {args.output}")
    else:
        print(md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
