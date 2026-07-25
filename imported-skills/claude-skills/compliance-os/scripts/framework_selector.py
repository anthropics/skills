#!/usr/bin/env python3
"""framework_selector.py — Multi-framework compliance applicability selector.

Stdlib-only. Takes a company profile and returns the applicable compliance frameworks
ranked by priority + dependency graph. Supports 9 frameworks:
  - ISO 27001 (info-sec ISMS)
  - ISO 13485 (medical device QMS)
  - ISO 42001 (AI management system)
  - ISO 14971 (medical device risk mgmt)
  - EU AI Act (Regulation 2024/1689)
  - EU MDR 2017/745 (medical device regulation)
  - GDPR (Regulation 2016/679)
  - SOC 2 (Trust Services Criteria)
  - FDA QSR (21 CFR 820)

Deterministic decision tree. No LLM calls. No external dependencies.

Input schema (JSON):
{
  "company": "Acme AI Inc.",
  "industry": "saas",                  # saas | medical_device | financial | other
  "products_include_ai": true,
  "ai_high_risk_per_eu": true,         # falls under Annex III, Article 6
  "deploys_ai_in_eu": true,
  "products_are_medical_devices": false,
  "sells_to_eu_customers": true,
  "sells_to_us_customers": true,
  "sells_to_enterprise_b2b": true,
  "processes_personal_data": true,
  "processes_eu_personal_data": true,
  "headcount": 80,
  "stage": "series_b"
}

Usage:
    python framework_selector.py                        # uses embedded mid-stage AI SaaS sample
    python framework_selector.py path/to/profile.json
    python framework_selector.py profile.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "company": "Acme AI Inc.",
    "industry": "saas",
    "products_include_ai": True,
    "ai_high_risk_per_eu": True,
    "deploys_ai_in_eu": True,
    "products_are_medical_devices": False,
    "sells_to_eu_customers": True,
    "sells_to_us_customers": True,
    "sells_to_enterprise_b2b": True,
    "processes_personal_data": True,
    "processes_eu_personal_data": True,
    "headcount": 80,
    "stage": "series_b",
    # Phase 3 additions (defaults false; sample profile does not trigger HIPAA / NIS2 / CSF)
    "processes_phi": False,
    "us_healthcare_covered_entity": False,
    "us_healthcare_business_associate": False,
    "nis2_essential_entity": False,
    "nis2_important_entity": False,
    "adopts_nist_csf": False,
    "us_government_contractor": False,
}


# Framework catalogue (id, name, type, certifiable)
FRAMEWORKS = {
    "iso_27001": {"name": "ISO/IEC 27001:2022", "type": "management_system", "certifiable": True, "binding": False},
    "iso_13485": {"name": "ISO 13485:2016", "type": "management_system", "certifiable": True, "binding": False},
    "iso_42001": {"name": "ISO/IEC 42001:2023", "type": "management_system", "certifiable": True, "binding": False},
    "iso_14971": {"name": "ISO 14971:2019", "type": "process_standard", "certifiable": False, "binding": False},
    "eu_ai_act": {"name": "Regulation (EU) 2024/1689 (AI Act)", "type": "regulation", "certifiable": False, "binding": True},
    "eu_mdr_745": {"name": "Regulation (EU) 2017/745 (MDR)", "type": "regulation", "certifiable": False, "binding": True},
    "gdpr": {"name": "Regulation (EU) 2016/679 (GDPR)", "type": "regulation", "certifiable": False, "binding": True},
    "soc_2": {"name": "AICPA SOC 2 Trust Services", "type": "attestation", "certifiable": True, "binding": False},
    "fda_qsr": {"name": "FDA 21 CFR 820 (QSR)", "type": "regulation", "certifiable": False, "binding": True},
    # Phase 3 additions
    "nist_csf": {"name": "NIST Cybersecurity Framework 2.0", "type": "framework_profile", "certifiable": False, "binding": False},
    "nis2": {"name": "Directive (EU) 2022/2555 (NIS2)", "type": "regulation", "certifiable": False, "binding": True},
    "hipaa": {"name": "HIPAA Security + Privacy + Breach Notification Rules", "type": "regulation", "certifiable": False, "binding": True},
}


# Dependency graph: framework X benefits from framework Y as prerequisite
DEPENDENCIES = {
    "iso_42001": ["iso_27001"],              # AIMS reuses ISMS heavily
    "iso_13485": ["iso_14971"],              # QMS uses risk mgmt
    "eu_mdr_745": ["iso_13485", "iso_14971"],
    "eu_ai_act": ["iso_42001"],              # voluntary AIMS satisfies parts of Article 17
    "soc_2": ["iso_27001"],                  # ISO 27001 controls map to SOC 2 TSC
    "fda_qsr": ["iso_13485"],                # QSR mostly harmonised with 13485
    # Phase 3 additions
    "nist_csf": [],                          # voluntary framework; no prereqs
    "nis2": ["iso_27001"],                   # NIS2 risk-mgmt + reporting maps to 27001 controls
    "hipaa": ["iso_27001"],                  # HIPAA Security Rule overlaps ISO 27001 Annex A
}


def select_frameworks(profile: Dict[str, Any]) -> List[str]:
    selected: List[str] = []

    # GDPR — any EU personal data
    if profile.get("processes_eu_personal_data") or (
        profile.get("processes_personal_data") and profile.get("sells_to_eu_customers")
    ):
        selected.append("gdpr")

    # ISO 27001 — enterprise B2B / mature SaaS
    if profile.get("sells_to_enterprise_b2b") or profile.get("stage") in ("series_a", "series_b", "series_c", "growth"):
        selected.append("iso_27001")

    # SOC 2 — US enterprise B2B
    if profile.get("sells_to_us_customers") and profile.get("sells_to_enterprise_b2b"):
        selected.append("soc_2")

    # ISO 42001 — any AI in products
    if profile.get("products_include_ai"):
        selected.append("iso_42001")

    # EU AI Act — AI deployed in EU
    if profile.get("products_include_ai") and (
        profile.get("deploys_ai_in_eu") or profile.get("sells_to_eu_customers")
    ):
        selected.append("eu_ai_act")

    # ISO 13485 + 14971 — medical device
    if profile.get("products_are_medical_devices"):
        selected.append("iso_13485")
        selected.append("iso_14971")

        # EU MDR — medical device sold in EU
        if profile.get("sells_to_eu_customers"):
            selected.append("eu_mdr_745")

        # FDA QSR — medical device sold in US
        if profile.get("sells_to_us_customers"):
            selected.append("fda_qsr")

    # HIPAA — any US healthcare PHI processing
    if profile.get("processes_phi") or profile.get("us_healthcare_covered_entity") or profile.get("us_healthcare_business_associate"):
        selected.append("hipaa")

    # NIS2 — operates in EU as essential or important entity per Annex I/II of Directive 2022/2555
    if profile.get("nis2_essential_entity") or profile.get("nis2_important_entity"):
        selected.append("nis2")

    # NIST CSF — voluntary; recommended for any org with cybersecurity programme (esp. US gov-adjacent)
    if profile.get("adopts_nist_csf") or profile.get("us_government_contractor"):
        selected.append("nist_csf")

    return selected


def annotate(profile: Dict[str, Any]) -> Dict[str, Any]:
    selected = select_frameworks(profile)

    # Build dependency notes
    dep_notes: List[Dict[str, Any]] = []
    for fid in selected:
        deps = DEPENDENCIES.get(fid, [])
        in_program = [d for d in deps if d in selected]
        missing = [d for d in deps if d not in selected]
        if in_program or missing:
            dep_notes.append({
                "framework": fid,
                "satisfied_dependencies": in_program,
                "missing_dependencies": missing,
            })

    # Priority ranking — bindings first, then certifiable, then reference
    def priority(fid: str) -> int:
        f = FRAMEWORKS[fid]
        if f["binding"]:
            return 0
        if f["certifiable"]:
            return 1
        return 2

    ranked = sorted(selected, key=priority)

    return {
        "company": profile.get("company"),
        "industry": profile.get("industry"),
        "applicable_frameworks": [
            {"id": fid, **FRAMEWORKS[fid]} for fid in ranked
        ],
        "framework_count": len(ranked),
        "binding_count": sum(1 for fid in ranked if FRAMEWORKS[fid]["binding"]),
        "certifiable_count": sum(1 for fid in ranked if FRAMEWORKS[fid]["certifiable"]),
        "dependency_notes": dep_notes,
        "rationale": _rationale(profile, ranked),
    }


def _rationale(profile: Dict[str, Any], selected: List[str]) -> List[str]:
    notes = []
    if "gdpr" in selected:
        notes.append("GDPR: EU personal data processed; binding regardless of certifiable choice.")
    if "iso_27001" in selected:
        notes.append("ISO 27001: enterprise B2B procurement frequently requires; foundation for AIMS + SOC 2.")
    if "soc_2" in selected:
        notes.append("SOC 2: US enterprise B2B procurement requires Type II audit; overlap with ISO 27001 ~75%.")
    if "iso_42001" in selected:
        notes.append("ISO 42001: AI in products; voluntary management system; satisfies Article 17 EU AI Act QMS.")
    if "eu_ai_act" in selected:
        notes.append("EU AI Act: AI deployed in EU; binding; Article 5 prohibitions in force; high-risk obligations 2 Aug 2026.")
    if "iso_13485" in selected:
        notes.append("ISO 13485: medical device manufacturer; required for MDR / FDA submissions.")
    if "iso_14971" in selected:
        notes.append("ISO 14971: medical device risk management; harmonised under MDR.")
    if "eu_mdr_745" in selected:
        notes.append("EU MDR 745: medical device sold in EU; binding; mandatory CE marking.")
    if "fda_qsr" in selected:
        notes.append("FDA QSR: medical device sold in US; binding; FDA quality system regulation.")
    if "hipaa" in selected:
        notes.append("HIPAA: processes US PHI; binding Security Rule (45 CFR 164 Subpart C) + Privacy Rule + Breach Notification.")
    if "nis2" in selected:
        notes.append("NIS2: essential or important entity in EU per Directive 2022/2555 Annex I/II; binding; cybersecurity + incident reporting obligations.")
    if "nist_csf" in selected:
        notes.append("NIST CSF 2.0: voluntary cybersecurity framework; recommended for US gov-adjacent orgs; cross-walks ISO 27001 + SOC 2 Common Criteria.")
    return notes


def render_text(r: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("COMPLIANCE OS — APPLICABLE FRAMEWORKS")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Company: {r['company']}")
    lines.append(f"Industry: {r['industry']}")
    lines.append(f"Applicable frameworks: {r['framework_count']}  "
                 f"({r['binding_count']} binding + {r['certifiable_count']} certifiable)")
    lines.append("")
    lines.append("-" * 72)
    lines.append("RANKED FRAMEWORKS (binding > certifiable > reference):")
    lines.append("")
    for f in r["applicable_frameworks"]:
        kind = []
        if f["binding"]:
            kind.append("BINDING")
        if f["certifiable"]:
            kind.append("CERTIFIABLE")
        kind_str = " | ".join(kind) if kind else "REFERENCE"
        lines.append(f"  [{kind_str:25s}]  {f['name']:42s}  ({f['id']})")
    lines.append("")
    lines.append("-" * 72)
    lines.append("RATIONALE:")
    for r_note in r["rationale"]:
        lines.append(f"  - {r_note}")
    lines.append("")

    if r["dependency_notes"]:
        lines.append("-" * 72)
        lines.append("DEPENDENCIES:")
        for d in r["dependency_notes"]:
            if d["satisfied_dependencies"]:
                lines.append(f"  {d['framework']} satisfied by: {', '.join(d['satisfied_dependencies'])}")
            if d["missing_dependencies"]:
                lines.append(f"  {d['framework']} missing dependency: {', '.join(d['missing_dependencies'])} (consider adding)")
        lines.append("")

    lines.append("-" * 72)
    lines.append("DECISION RULES:")
    lines.append("  GDPR: any EU personal data processed -> mandatory")
    lines.append("  ISO 27001: enterprise B2B procurement requirement; foundation for AIMS + SOC 2")
    lines.append("  SOC 2: US enterprise B2B procurement requirement; overlap ~75% with ISO 27001")
    lines.append("  ISO 42001: AI in products; voluntary AIMS; satisfies parts of Article 17 AI Act")
    lines.append("  EU AI Act: AI in EU; binding; phased application through 2027")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Multi-framework compliance applicability selector.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to company profile JSON (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                profile = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        profile = SAMPLE
        source = "<embedded sample: mid-stage AI SaaS, US+EU customers, B2B>"

    result = annotate(profile)
    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))
    return 0


if __name__ == "__main__":
    sys.exit(main())
