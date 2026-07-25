#!/usr/bin/env python3
"""evidence_pool_generator.py — Consolidated evidence checklist across enabled frameworks.

Stdlib-only. Given a multi-framework compliance program config, produces a unified
evidence pool that maps each evidence artefact to all the (framework, control)
tuples it satisfies. Each artefact gets a reuse-leverage score = number of
distinct (framework, control) tuples satisfied.

Deterministic. No LLM calls. No external dependencies. Uses a curated evidence
catalogue distilled from ISO 27001, ISO 42001, SOC 2, GDPR, EU AI Act published
guidance.

Input schema (JSON):
{
  "program": "Acme AI Inc. compliance program",
  "enabled_frameworks": ["iso_27001", "soc_2", "iso_42001", "eu_ai_act", "gdpr"],
  "audit_cycle_year": "year_1"
}

Usage:
    python evidence_pool_generator.py
    python evidence_pool_generator.py path/to/program.json
    python evidence_pool_generator.py program.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "program": "Acme AI Inc. compliance program",
    "enabled_frameworks": ["iso_27001", "soc_2", "iso_42001", "eu_ai_act", "gdpr"],
    "audit_cycle_year": "year_1",
}


# Evidence catalogue: each artefact + the (framework, control) tuples it satisfies
# + acquisition cost (low / medium / high) + retention requirement (months)
EVIDENCE_CATALOG: List[Dict[str, Any]] = [
    {
        "id": "ev.access_review_quarterly",
        "title": "Quarterly access review records (privileged + general access)",
        "satisfies": [
            ("iso_27001", "A.5.15"), ("iso_27001", "A.8.2"), ("iso_27001", "A.8.3"),
            ("soc_2", "CC6.1"), ("soc_2", "CC6.2"), ("soc_2", "CC6.3"),
            ("iso_42001", "A.4.4"),
            ("gdpr", "Article 32(1)(b)"),
        ],
        "acquisition_cost": "low",
        "retention_months": 36,
        "owner": "IT / Security",
    },
    {
        "id": "ev.asset_register",
        "title": "Asset register with AI systems + data classification",
        "satisfies": [
            ("iso_27001", "A.5.9"), ("iso_27001", "A.5.10"), ("iso_27001", "A.5.12"),
            ("soc_2", "CC6.1"), ("soc_2", "CC3.2"),
            ("iso_42001", "A.4.2"), ("iso_42001", "A.4.3"),
            ("gdpr", "Article 30"),
        ],
        "acquisition_cost": "medium",
        "retention_months": 36,
        "owner": "Security / DPO",
    },
    {
        "id": "ev.risk_register",
        "title": "Risk register with severity matrix + treatment + residual signoff",
        "satisfies": [
            ("iso_27001", "Clause 6.1"), ("iso_27001", "Clause 8.2"),
            ("soc_2", "CC3.1"), ("soc_2", "CC3.2"), ("soc_2", "CC3.4"),
            ("iso_42001", "Clause 6.1.2"), ("iso_42001", "A.5"),
            ("eu_ai_act", "Article 9"),
            ("gdpr", "Article 35"),
        ],
        "acquisition_cost": "high",
        "retention_months": 36,
        "owner": "Compliance officer",
    },
    {
        "id": "ev.supplier_inventory_reviews",
        "title": "Supplier inventory + annual reviews + signed DPAs",
        "satisfies": [
            ("iso_27001", "A.5.19"), ("iso_27001", "A.5.20"), ("iso_27001", "A.5.21"),
            ("soc_2", "CC9.2"),
            ("iso_42001", "A.10.2"), ("iso_42001", "A.10.6"),
            ("eu_ai_act", "Article 25"),
            ("gdpr", "Article 28"),
        ],
        "acquisition_cost": "medium",
        "retention_months": 36,
        "owner": "Procurement / Compliance",
    },
    {
        "id": "ev.incident_log_postmortems",
        "title": "Incident log + severity classifications + post-incident reviews + notifications sent",
        "satisfies": [
            ("iso_27001", "A.5.24"), ("iso_27001", "A.5.25"), ("iso_27001", "A.5.26"),
            ("iso_27001", "A.5.27"), ("iso_27001", "A.6.8"),
            ("soc_2", "CC7.3"), ("soc_2", "CC7.4"), ("soc_2", "CC7.5"),
            ("iso_42001", "A.8.4"),
            ("eu_ai_act", "Article 73"),
            ("gdpr", "Article 33"), ("gdpr", "Article 34"),
        ],
        "acquisition_cost": "medium",
        "retention_months": 36,
        "owner": "Security / IR team",
    },
    {
        "id": "ev.logs_aggregated",
        "title": "Tamper-evident logs centralized with retention",
        "satisfies": [
            ("iso_27001", "A.8.15"), ("iso_27001", "A.8.16"),
            ("soc_2", "CC7.1"), ("soc_2", "CC7.2"),
            ("iso_42001", "A.9.3"), ("iso_42001", "A.9.4"),
            ("eu_ai_act", "Article 12"),
        ],
        "acquisition_cost": "high",
        "retention_months": 12,
        "owner": "Platform / SRE",
    },
    {
        "id": "ev.change_records",
        "title": "Change approval records + rollback procedure + post-implementation reviews",
        "satisfies": [
            ("iso_27001", "A.8.32"),
            ("soc_2", "CC8.1"),
            ("iso_42001", "A.6.2.5"),
        ],
        "acquisition_cost": "low",
        "retention_months": 24,
        "owner": "Engineering / Platform",
    },
    {
        "id": "ev.bcp_dr_exercises",
        "title": "BCP/DRP exercise records + RPO/RTO validation",
        "satisfies": [
            ("iso_27001", "A.5.29"), ("iso_27001", "A.5.30"),
            ("iso_27001", "A.8.13"), ("iso_27001", "A.8.14"),
            ("soc_2", "A1.2"), ("soc_2", "A1.3"),
        ],
        "acquisition_cost": "high",
        "retention_months": 36,
        "owner": "Platform / SRE",
    },
    {
        "id": "ev.training_records",
        "title": "Competence requirements per role + training completion + effectiveness verification",
        "satisfies": [
            ("iso_27001", "A.6.3"),
            ("soc_2", "CC1.4"), ("soc_2", "CC2.2"),
            ("iso_42001", "Clause 7.2"), ("iso_42001", "Clause 7.3"),
            ("eu_ai_act", "Article 4"),
        ],
        "acquisition_cost": "medium",
        "retention_months": 36,
        "owner": "HR / People Ops",
    },
    {
        "id": "ev.data_inventory_consent",
        "title": "Data inventory + provenance + retention + consent / lawful-basis register",
        "satisfies": [
            ("iso_27001", "A.5.34"),
            ("iso_42001", "A.7.2"), ("iso_42001", "A.7.3"), ("iso_42001", "A.7.4"),
            ("iso_42001", "A.7.5"), ("iso_42001", "A.7.6"),
            ("eu_ai_act", "Article 10"),
            ("gdpr", "Article 5"), ("gdpr", "Article 6"), ("gdpr", "Article 30"),
        ],
        "acquisition_cost": "high",
        "retention_months": 60,
        "owner": "DPO / Data team",
    },
    {
        "id": "ev.internal_audit_records",
        "title": "Internal audit plan + auditor independence records + findings tracking",
        "satisfies": [
            ("iso_27001", "Clause 9.2"),
            ("soc_2", "CC4.1"),
            ("iso_42001", "Clause 9.2"),
        ],
        "acquisition_cost": "medium",
        "retention_months": 36,
        "owner": "Compliance officer",
    },
    {
        "id": "ev.management_review_records",
        "title": "Management review schedule + meeting records + action item tracking",
        "satisfies": [
            ("iso_27001", "Clause 9.3"),
            ("iso_42001", "Clause 9.3"),
        ],
        "acquisition_cost": "low",
        "retention_months": 36,
        "owner": "Compliance officer + Exec",
    },
    {
        "id": "ev.policy_set",
        "title": "Policy set: AI, info-sec, privacy, code-of-conduct (signed + reviewed annually)",
        "satisfies": [
            ("iso_27001", "A.5.1"),
            ("soc_2", "CC1.1"), ("soc_2", "CC1.2"),
            ("iso_42001", "Clause 5.2"), ("iso_42001", "A.2.2"), ("iso_42001", "A.2.3"),
            ("eu_ai_act", "Article 17(1)(a)"),
            ("gdpr", "Article 24"),
        ],
        "acquisition_cost": "medium",
        "retention_months": 60,
        "owner": "Compliance officer + Exec",
    },
    {
        "id": "ev.crypto_records",
        "title": "Crypto policy + algorithm/key-length standards + key rotation records",
        "satisfies": [
            ("iso_27001", "A.8.24"),
            ("soc_2", "CC6.1"), ("soc_2", "CC6.7"),
            ("gdpr", "Article 32(1)(a)"),
        ],
        "acquisition_cost": "medium",
        "retention_months": 36,
        "owner": "Security",
    },
    {
        "id": "ev.vuln_scans_patch",
        "title": "Vulnerability scan results + patch SLAs + remediation evidence",
        "satisfies": [
            ("iso_27001", "A.8.7"), ("iso_27001", "A.8.8"), ("iso_27001", "A.8.9"),
            ("soc_2", "CC7.1"), ("soc_2", "CC7.2"), ("soc_2", "CC7.4"),
        ],
        "acquisition_cost": "medium",
        "retention_months": 24,
        "owner": "Security",
    },
]


def filter_by_enabled(catalog: List[Dict[str, Any]], enabled: List[str]) -> List[Dict[str, Any]]:
    """Filter satisfaction tuples to enabled frameworks."""
    enabled_set = set(enabled)
    out = []
    for ev in catalog:
        active = [(f, c) for (f, c) in ev["satisfies"] if f in enabled_set]
        if not active:
            continue
        leverage = len(active)
        frameworks_satisfied = sorted({f for f, _ in active})
        record = {**ev, "active_satisfaction": active, "reuse_leverage": leverage,
                  "frameworks_satisfied": frameworks_satisfied}
        out.append(record)
    out.sort(key=lambda x: (-x["reuse_leverage"], x["title"]))
    return out


def analyze(payload: Dict[str, Any]) -> Dict[str, Any]:
    enabled = payload.get("enabled_frameworks", [])
    artefacts = filter_by_enabled(EVIDENCE_CATALOG, enabled)
    total_satisfactions = sum(a["reuse_leverage"] for a in artefacts)
    by_cost: Dict[str, int] = {"low": 0, "medium": 0, "high": 0}
    by_owner: Dict[str, int] = {}
    for a in artefacts:
        by_cost[a["acquisition_cost"]] += 1
        by_owner[a["owner"]] = by_owner.get(a["owner"], 0) + 1

    # High-leverage artefacts (satisfy ≥ 5 mappings)
    high_leverage = [a for a in artefacts if a["reuse_leverage"] >= 5]

    return {
        "program": payload.get("program"),
        "enabled_frameworks": enabled,
        "audit_cycle_year": payload.get("audit_cycle_year"),
        "artefact_count": len(artefacts),
        "total_satisfactions_across_artefacts": total_satisfactions,
        "high_leverage_count": len(high_leverage),
        "by_acquisition_cost": by_cost,
        "by_owner": by_owner,
        "artefacts": artefacts,
    }


def render_text(r: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("COMPLIANCE OS — UNIFIED EVIDENCE POOL")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Program: {r['program']}")
    lines.append(f"Enabled frameworks: {', '.join(r['enabled_frameworks'])}")
    lines.append(f"Audit cycle phase: {r['audit_cycle_year']}")
    lines.append(f"Artefacts in scope: {r['artefact_count']}")
    lines.append(f"Total (framework, control) satisfactions: {r['total_satisfactions_across_artefacts']}")
    lines.append(f"High-leverage artefacts (≥ 5 mappings): {r['high_leverage_count']}")
    lines.append("")
    lines.append(f"By acquisition cost: low={r['by_acquisition_cost']['low']}  "
                 f"medium={r['by_acquisition_cost']['medium']}  high={r['by_acquisition_cost']['high']}")
    lines.append(f"By owner: {dict(r['by_owner'])}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("ARTEFACTS (sorted by reuse leverage — highest first):")
    lines.append("")

    for a in r["artefacts"]:
        lines.append(f"  [{a['id']}]  {a['title']}")
        lines.append(f"      Leverage: {a['reuse_leverage']} mappings across {len(a['frameworks_satisfied'])} frameworks ({', '.join(a['frameworks_satisfied'])})")
        lines.append(f"      Owner: {a['owner']}  |  Cost: {a['acquisition_cost']}  |  Retention: {a['retention_months']} months")
        lines.append(f"      Satisfies:")
        for fid, ctrl in a["active_satisfaction"]:
            lines.append(f"        - {fid:12s} -> {ctrl}")
        lines.append("")

    lines.append("-" * 72)
    lines.append("REUSE-LEVERAGE GUIDANCE:")
    lines.append("  Build high-leverage artefacts first (single evidence -> ≥ 5 framework controls).")
    lines.append("  High-leverage examples (depend on enabled frameworks): risk register, supplier inventory, incident log,")
    lines.append("  data inventory + consent, policy set, training records.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Unified evidence pool generator across compliance frameworks.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to program JSON (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                payload = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        payload = SAMPLE
        source = "<embedded sample: 5 enabled frameworks, year 1>"

    result = analyze(payload)
    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))
    return 0


if __name__ == "__main__":
    sys.exit(main())
