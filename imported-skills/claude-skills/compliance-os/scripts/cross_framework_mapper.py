#!/usr/bin/env python3
"""cross_framework_mapper.py — Multi-framework control overlap computation.

Stdlib-only. Takes 1+ framework control libraries (control IDs + categories) and
computes overlap with mapping confidence (HIGH/MEDIUM/LOW) using a curated
ground-truth overlap dictionary distilled from published cross-walks:
  - ISO 27001 Annex A <-> SOC 2 TSC (the densest known pair)
  - ISO 27001 <-> ISO 42001 (info-sec reuse for AIMS)
  - ISO 42001 <-> EU AI Act (Article 17 QMS satisfaction)
  - GDPR <-> ISO 27001 (privacy controls overlap)
  - ISO 13485 <-> FDA QSR (harmonised)

For each merged control, outputs the participating frameworks + a unified
evidence-requirement statement that satisfies all of them.

Deterministic ground-truth lookup. No LLM calls. No external dependencies.

Input schema (JSON):
{
  "program": "Acme AI Inc. Compliance Program",
  "enabled_frameworks": ["iso_27001", "soc_2", "iso_42001", "eu_ai_act", "gdpr"]
}

Usage:
    python cross_framework_mapper.py                      # uses embedded 5-framework sample
    python cross_framework_mapper.py path/to/program.json
    python cross_framework_mapper.py program.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Set


SAMPLE: Dict[str, Any] = {
    "program": "Acme AI Inc. Compliance Program",
    "enabled_frameworks": [
        "iso_27001", "soc_2", "iso_42001", "eu_ai_act", "gdpr",
        "nist_csf", "nis2", "hipaa",
    ],
}


# Curated overlap database
# Each merged control: id, theme, evidence requirement, and per-framework mapping
# Mappings: framework_id -> (control_id, confidence)
# Confidence: H (high - same evidence satisfies), M (medium - evidence with overlay), L (low - concept overlap only)

MERGED_CONTROLS: List[Dict[str, Any]] = [
    {
        "id": "mc.access_control",
        "theme": "Access control (identity, authentication, authorization)",
        "evidence": "Documented access-control policy + access provisioning/de-provisioning procedure + quarterly access review records + RBAC matrix",
        "mappings": {
            "iso_27001": ("A.5.15 + A.8.2 + A.8.3", "H"),
            "soc_2": ("CC6.1 + CC6.2 + CC6.3", "H"),
            "iso_42001": ("A.4.4 (human resources for AI systems)", "M"),
            "gdpr": ("Article 32(1)(b) integrity and confidentiality", "M"),
            "nist_csf": ("PR.AA-01 + PR.AA-03 + PR.AA-05 (identities + authentication + authorization)", "H"),
            "nis2": ("Article 21(2)(i) access control policies", "M"),
            "hipaa": ("§164.308(a)(3) workforce security + §164.308(a)(4) information access management + §164.312(a)(1) access control", "H"),
        },
    },
    {
        "id": "mc.asset_inventory",
        "theme": "Asset inventory and classification",
        "evidence": "Asset register including AI systems + data classification scheme + ownership map",
        "mappings": {
            "iso_27001": ("A.5.9 + A.5.10 + A.5.12", "H"),
            "soc_2": ("CC6.1 + CC3.2", "H"),
            "iso_42001": ("A.4.2 (data) + A.4.3 (tooling)", "H"),
            "gdpr": ("Article 30 (records of processing activities)", "M"),
            "nist_csf": ("ID.AM-01 + ID.AM-02 + ID.AM-04 + ID.AM-05 (assets inventoried + classified)", "H"),
            "nis2": ("Article 21(2)(b) policies on the use of risk-management measures (implicit: know your assets)", "M"),
            "hipaa": ("§164.308(a)(1)(ii)(A) risk analysis (requires asset inventory) + §164.310(d) device + media controls", "M"),
        },
    },
    {
        "id": "mc.risk_management",
        "theme": "Risk management process",
        "evidence": "Risk methodology + risk register with severity matrix + risk treatment plan + residual-risk acceptance signoff",
        "mappings": {
            "iso_27001": ("Clause 6.1 + Clause 8.2", "H"),
            "soc_2": ("CC3.1 + CC3.2 + CC3.4", "H"),
            "iso_42001": ("Clause 6.1.2 + A.5", "H"),
            "eu_ai_act": ("Article 9 (risk management system)", "M"),
            "gdpr": ("Article 35 (DPIA where applicable)", "M"),
            "nist_csf": ("GV.RM (risk management strategy) + ID.RA (risk assessment) + ID.IM (improvement)", "H"),
            "nis2": ("Article 21(2)(a) risk analysis + Article 21(2)(b) policies on risk-management measures", "H"),
            "hipaa": ("§164.308(a)(1)(ii)(A) risk analysis + §164.308(a)(1)(ii)(B) risk management", "H"),
        },
    },
    {
        "id": "mc.supplier_management",
        "theme": "Third-party / supplier risk management",
        "evidence": "Supplier inventory + due-diligence questionnaires + contractual security/privacy/AI clauses + periodic review records",
        "mappings": {
            "iso_27001": ("A.5.19 + A.5.20 + A.5.21 + A.5.22", "H"),
            "soc_2": ("CC9.2", "H"),
            "iso_42001": ("A.10.2 + A.10.6", "H"),
            "eu_ai_act": ("Article 25 (responsibilities along the AI value chain)", "M"),
            "gdpr": ("Article 28 (processor obligations)", "H"),
            "nist_csf": ("GV.SC (cybersecurity supply chain risk management) + ID.SC", "H"),
            "nis2": ("Article 21(2)(d) supply-chain security including security-related aspects of relationships with direct suppliers", "H"),
            "hipaa": ("§164.308(b)(1) business associate contracts + §164.314(a) organizational requirements (BAAs)", "H"),
        },
    },
    {
        "id": "mc.incident_response",
        "theme": "Incident response + notification",
        "evidence": "Documented incident response procedure + severity definitions + escalation matrix + notification SLAs + post-incident reviews",
        "mappings": {
            "iso_27001": ("A.5.24 + A.5.25 + A.5.26 + A.5.27 + A.6.8", "H"),
            "soc_2": ("CC7.3 + CC7.4 + CC7.5", "H"),
            "iso_42001": ("A.8.4 (communication of AI incidents)", "M"),
            "eu_ai_act": ("Article 73 (serious-incident reporting)", "M"),
            "gdpr": ("Articles 33 + 34 (breach notification)", "H"),
            "nist_csf": ("RS.MA + RS.AN + RS.RP + RS.CO (response: management, analysis, reporting, communication)", "H"),
            "nis2": ("Article 23 incident notification (24h early warning / 72h notification / 1-month final report)", "H"),
            "hipaa": ("§164.308(a)(6) security incident procedures + §164.400-414 Breach Notification Rule", "H"),
        },
    },
    {
        "id": "mc.monitoring_logging",
        "theme": "Monitoring + logging",
        "evidence": "Logging policy + tamper-evident logs + monitoring dashboards + retention compliant with longest applicable framework",
        "mappings": {
            "iso_27001": ("A.8.15 + A.8.16", "H"),
            "soc_2": ("CC7.1 + CC7.2", "H"),
            "iso_42001": ("A.9.3 + A.9.4", "M"),
            "eu_ai_act": ("Article 12 (logging) + Article 72 (post-market monitoring)", "M"),
            "nist_csf": ("DE.CM (continuous monitoring) + DE.AE (anomalies + events)", "H"),
            "nis2": ("Article 21(2)(h) human resources security + ongoing monitoring expectations", "M"),
            "hipaa": ("§164.308(a)(1)(ii)(D) information system activity review + §164.312(b) audit controls", "H"),
        },
    },
    {
        "id": "mc.change_management",
        "theme": "Change management (system + model)",
        "evidence": "Change approval workflow + version control + rollback procedure + change advisory board records",
        "mappings": {
            "iso_27001": ("A.8.32", "H"),
            "soc_2": ("CC8.1", "H"),
            "iso_42001": ("A.6.2.5 (deployment)", "M"),
            "nist_csf": ("PR.PS (platform security including change-mgmt) + ID.IM-03 (improvements identified)", "H"),
            "nis2": ("Article 21(2)(e) security in network and information systems acquisition, development and maintenance", "M"),
            "hipaa": ("§164.308(a)(5)(ii)(B) protection from malicious software (implies controlled change) + §164.312(a)(1) access control during change", "M"),
        },
    },
    {
        "id": "mc.business_continuity",
        "theme": "Business continuity and disaster recovery",
        "evidence": "BCP/DRP documents + tested recovery objectives (RPO/RTO) + annual exercises + lessons learned",
        "mappings": {
            "iso_27001": ("A.5.29 + A.5.30 + A.8.13 + A.8.14", "H"),
            "soc_2": ("A1.2 + A1.3", "H"),
            "nist_csf": ("RC.RP (recovery planning) + RC.IM + RC.CO + ID.BE-05 (resilience requirements)", "H"),
            "nis2": ("Article 21(2)(c) business continuity, such as backup management and disaster recovery, and crisis management", "H"),
            "hipaa": ("§164.308(a)(7) contingency plan (incl. data backup + disaster recovery + emergency mode operation)", "H"),
        },
    },
    {
        "id": "mc.competence_training",
        "theme": "Competence + awareness training",
        "evidence": "Competence requirements per role + training plan + completion records + effectiveness verification",
        "mappings": {
            "iso_27001": ("A.6.3", "H"),
            "soc_2": ("CC1.4 + CC2.2", "H"),
            "iso_42001": ("Clause 7.2 + Clause 7.3 + A.4.4", "H"),
            "eu_ai_act": ("Article 4 (AI literacy)", "M"),
            "nist_csf": ("PR.AT (awareness + training)", "H"),
            "nis2": ("Article 21(2)(g) basic cyber-hygiene practices and cybersecurity training", "H"),
            "hipaa": ("§164.308(a)(5) security awareness and training", "H"),
        },
    },
    {
        "id": "mc.data_governance",
        "theme": "Data governance + data quality",
        "evidence": "Data inventory + provenance records + quality metrics + retention/deletion schedule + consent/lawful-basis records",
        "mappings": {
            "iso_27001": ("A.5.34 (privacy)", "M"),
            "iso_42001": ("A.7 (full category)", "H"),
            "eu_ai_act": ("Article 10 (data governance for high-risk)", "H"),
            "gdpr": ("Articles 5 + 6 + 30", "H"),
            "nist_csf": ("PR.DS (data security) + ID.AM-07 (data inventories) + GV.PO (policy)", "H"),
            "nis2": ("Article 21(2)(j) policies and procedures (multi-factor + secure communications) implying data discipline", "M"),
            "hipaa": ("§164.312(c)(1) integrity + §164.502 uses and disclosures of PHI + §164.514 de-identification", "H"),
        },
    },
    {
        "id": "mc.internal_audit",
        "theme": "Internal audit programme",
        "evidence": "Annual audit plan + auditor independence + findings tracking + closure verification",
        "mappings": {
            "iso_27001": ("Clause 9.2", "H"),
            "soc_2": ("CC4.1", "H"),
            "iso_42001": ("Clause 9.2", "H"),
            "nist_csf": ("ID.IM (improvement processes including audits)", "M"),
            "nis2": ("Article 21(2)(b) policies on the use of risk-management measures (implies periodic audit)", "M"),
            "hipaa": ("§164.308(a)(1)(ii)(D) information system activity review + §164.308(a)(8) periodic evaluation", "H"),
        },
    },
    {
        "id": "mc.management_review",
        "theme": "Management review",
        "evidence": "Management review procedure + scheduled inputs + meeting records + action item tracking",
        "mappings": {
            "iso_27001": ("Clause 9.3", "H"),
            "iso_42001": ("Clause 9.3", "H"),
            "nist_csf": ("GV.OV (oversight) + GV.PO (organizational policy review)", "H"),
            "nis2": ("Article 20 governance: management bodies must approve cybersecurity risk-management measures and oversee implementation", "H"),
            "hipaa": ("§164.308(a)(2) assigned security responsibility + §164.308(a)(8) periodic evaluation by senior official", "M"),
        },
    },
    {
        "id": "mc.cryptography",
        "theme": "Cryptography and key management",
        "evidence": "Cryptographic policy + algorithm + key length standards + key rotation + HSM/KMS architecture + key custody records",
        "mappings": {
            "iso_27001": ("A.8.24", "H"),
            "soc_2": ("CC6.1 + CC6.7", "H"),
            "gdpr": ("Article 32(1)(a) pseudonymisation + encryption", "H"),
            "nist_csf": ("PR.DS-02 (data-in-transit) + PR.DS-01 (data-at-rest) + PR.PS-05 (cryptography)", "H"),
            "nis2": ("Article 21(2)(h) policies on the use of cryptography and, where appropriate, encryption", "H"),
            "hipaa": ("§164.312(a)(2)(iv) encryption + decryption (addressable) + §164.312(e)(2)(ii) transmission encryption", "H"),
        },
    },
    {
        "id": "mc.secure_sdlc",
        "theme": "Secure software development lifecycle",
        "evidence": "Secure SDLC policy + threat modeling + code review records + SAST/DAST scanning + vulnerability triage",
        "mappings": {
            "iso_27001": ("A.8.25 + A.8.26 + A.8.27 + A.8.28 + A.8.29 + A.8.30 + A.8.31", "H"),
            "soc_2": ("CC8.1 + CC7.1", "H"),
            "iso_42001": ("A.6.2.2 + A.6.2.3 + A.6.2.4 (AI-specific SDLC)", "M"),
            "nist_csf": ("PR.PS (platform security including secure development) + ID.RA-08 (vulnerabilities identified)", "H"),
            "nis2": ("Article 21(2)(e) security in network and information systems acquisition, development and maintenance", "H"),
        },
    },
    {
        "id": "mc.vulnerability_mgmt",
        "theme": "Vulnerability + patch management",
        "evidence": "Vulnerability scanning schedule + patch SLAs by severity + exception tracking + remediation evidence",
        "mappings": {
            "iso_27001": ("A.8.7 + A.8.8 + A.8.9", "H"),
            "soc_2": ("CC7.1 + CC7.2 + CC7.4", "H"),
            "nist_csf": ("ID.RA-01 + ID.RA-08 (vulnerabilities) + PR.PS-02 (patching)", "H"),
            "nis2": ("Article 21(2)(f) policies and procedures to assess the effectiveness of cybersecurity risk-management measures + vulnerability handling", "H"),
            "hipaa": ("§164.308(a)(5)(ii)(B) protection from malicious software + §164.308(a)(1)(ii)(A) periodic risk analysis (covers vulnerability identification)", "M"),
        },
    },
    {
        "id": "mc.physical_security",
        "theme": "Physical security and environmental controls",
        "evidence": "Facility access controls + visitor log + environmental monitoring + tamper-evident seals on critical assets",
        "mappings": {
            "iso_27001": ("A.7.1 + A.7.2 + A.7.3 + A.7.4 + A.7.5 + A.7.6 + A.7.7 + A.7.8", "H"),
            "soc_2": ("CC6.4 + CC6.5", "H"),
            "nist_csf": ("PR.AA-06 (physical access) + PR.PS-04 (physical resource security)", "H"),
            "hipaa": ("§164.310(a)(1) facility access controls + §164.310(b) workstation use + §164.310(c) workstation security + §164.310(d) device + media controls", "H"),
        },
    },
    {
        "id": "mc.data_protection_privacy",
        "theme": "Personal data protection (privacy by design)",
        "evidence": "Privacy policy + lawful-basis register + retention/deletion schedule + DPIA records + data-subject rights workflow + DPO appointment (where required)",
        "mappings": {
            "iso_27001": ("A.5.34", "H"),
            "iso_42001": ("A.7.6 (data privacy considerations)", "M"),
            "gdpr": ("Articles 5 + 6 + 24 + 25 + 30 + 35 + 38", "H"),
            "nist_csf": ("GV.PO + PR.DS (data security)", "M"),
            "hipaa": ("§164.502 uses and disclosures (Privacy Rule) + §164.520 notice of privacy practices + §164.530 administrative requirements", "H"),
        },
    },
    {
        "id": "mc.documentation_control",
        "theme": "Documented information control",
        "evidence": "Document control procedure + version control + approval workflow + retention + obsolete-doc handling",
        "mappings": {
            "iso_27001": ("Clause 7.5", "H"),
            "soc_2": ("CC4.1 + CC5.1", "H"),
            "iso_42001": ("Clause 7.5", "H"),
            "nist_csf": ("GV.PO (policy + documentation) + ID.AM-08 (system and data are documented)", "H"),
            "nis2": ("Article 21(1) documented cybersecurity risk-management measures", "H"),
            "hipaa": ("§164.316 policies, procedures, and documentation requirements (retention 6 years)", "H"),
        },
    },
    {
        "id": "mc.continual_improvement",
        "theme": "Continual improvement + CAPA",
        "evidence": "Nonconformity tracking + root-cause analysis + corrective action plans + effectiveness verification + trend analysis",
        "mappings": {
            "iso_27001": ("Clause 10.1 + 10.2", "H"),
            "soc_2": ("CC4.1 + CC4.2 + CC5.3", "H"),
            "iso_42001": ("Clause 10.1 + 10.2", "H"),
            "nist_csf": ("ID.IM-01 + ID.IM-02 + ID.IM-03 (improvements identified, evaluated, executed)", "H"),
            "hipaa": ("§164.306(e) review + modify (security measures must be reviewed and modified as needed)", "M"),
        },
    },
]


def merged_in_scope(enabled: Set[str]) -> List[Dict[str, Any]]:
    """Return merged controls where at least 1 enabled framework maps to them."""
    out: List[Dict[str, Any]] = []
    for mc in MERGED_CONTROLS:
        active_maps = {fid: m for fid, m in mc["mappings"].items() if fid in enabled}
        if active_maps:
            out.append({
                "id": mc["id"],
                "theme": mc["theme"],
                "evidence": mc["evidence"],
                "frameworks_count": len(active_maps),
                "frameworks": active_maps,
            })
    return out


def overlap_summary(merged: List[Dict[str, Any]], enabled: Set[str]) -> Dict[str, Any]:
    """Compute per-framework coverage and per-pair overlap."""
    coverage: Dict[str, int] = {f: 0 for f in enabled}
    high_confidence: Dict[str, int] = {f: 0 for f in enabled}
    for mc in merged:
        for fid in mc["frameworks"]:
            coverage[fid] += 1
            _, conf = mc["frameworks"][fid]
            if conf == "H":
                high_confidence[fid] += 1

    multi_framework = [mc for mc in merged if mc["frameworks_count"] >= 2]
    high_reuse = [mc for mc in merged if mc["frameworks_count"] >= 3]

    return {
        "total_merged_controls_in_scope": len(merged),
        "per_framework_coverage": coverage,
        "per_framework_high_confidence": high_confidence,
        "multi_framework_count": len(multi_framework),
        "high_reuse_count_3plus_frameworks": len(high_reuse),
    }


def analyze(payload: Dict[str, Any]) -> Dict[str, Any]:
    enabled = set(payload.get("enabled_frameworks", []))
    merged = merged_in_scope(enabled)
    summary = overlap_summary(merged, enabled)
    return {
        "program": payload.get("program"),
        "enabled_frameworks": sorted(enabled),
        "summary": summary,
        "merged_controls": sorted(merged, key=lambda m: -m["frameworks_count"]),
    }


def render_text(r: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("COMPLIANCE OS — CROSS-FRAMEWORK CONTROL MAPPING")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Program: {r['program']}")
    lines.append(f"Enabled frameworks ({len(r['enabled_frameworks'])}): {', '.join(r['enabled_frameworks'])}")
    lines.append("")
    s = r["summary"]
    lines.append(f"Merged controls in scope: {s['total_merged_controls_in_scope']}")
    lines.append(f"Multi-framework controls (≥ 2): {s['multi_framework_count']}")
    lines.append(f"High-reuse controls (≥ 3 frameworks): {s['high_reuse_count_3plus_frameworks']}")
    lines.append("")
    lines.append("Per-framework coverage in merged catalogue:")
    for fid in r["enabled_frameworks"]:
        cov = s["per_framework_coverage"].get(fid, 0)
        hi = s["per_framework_high_confidence"].get(fid, 0)
        lines.append(f"  {fid:15s}  {cov} mappings  ({hi} HIGH confidence)")
    lines.append("")
    lines.append("-" * 72)
    lines.append("MERGED CONTROLS (sorted by reuse leverage):")
    lines.append("")

    for mc in r["merged_controls"]:
        lines.append(f"  [{mc['id']}]  {mc['theme']}  ({mc['frameworks_count']} frameworks)")
        lines.append(f"      Evidence: {mc['evidence']}")
        for fid, (ctrl, conf) in mc["frameworks"].items():
            conf_label = {"H": "HIGH ", "M": "MED  ", "L": "LOW  "}[conf]
            lines.append(f"        [{conf_label}] {fid:12s} -> {ctrl}")
        lines.append("")

    lines.append("-" * 72)
    lines.append("CONFIDENCE LEGEND:")
    lines.append("  HIGH  — same evidence satisfies both (direct overlap)")
    lines.append("  MED   — existing evidence with overlay")
    lines.append("  LOW   — concept overlap; mostly new artefact required")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Multi-framework control overlap computation.",
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
        source = "<embedded sample: ISO 27001 + SOC 2 + ISO 42001 + EU AI Act + GDPR>"

    result = analyze(payload)
    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))
    return 0


if __name__ == "__main__":
    sys.exit(main())
