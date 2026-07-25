#!/usr/bin/env python3
"""aims_gap_analyzer.py — ISO/IEC 42001:2023 AIMS gap analysis against Clauses 4-10.

Stdlib-only. Scores each clause as 'full' / 'partial' / 'missing' based on an evidence
inventory and outputs a prioritized remediation list with severity at certification audit.

Deterministic logic. No LLM calls. No external dependencies.

Input schema (JSON):
{
  "organization": "Acme AI Inc.",
  "scope_statement": "Customer-facing recommendation engine + internal LLM tools",
  "certification_target": "stage_1_audit_in_q3",
  "evidence": {
    "4.1_context_external": "documented",
    "4.2_interested_parties": "documented",
    "4.3_scope_statement": "documented",
    "4.4_aims_processes": "partial",
    "5.1_leadership_commitment": "documented",
    "5.2_ai_policy": "partial",
    "5.3_roles_responsibilities": "missing",
    "6.1.2_risk_assessment": "documented",
    "6.1.3_risk_treatment": "partial",
    "6.1.4_impact_assessment": "missing",
    "6.2_objectives": "documented",
    "7.1_resources": "documented",
    "7.2_competence": "missing",
    "7.3_awareness": "partial",
    "7.4_communication": "documented",
    "7.5_documented_info": "documented",
    "8.1_operational_planning": "documented",
    "8.2_impact_assessment_process": "partial",
    "8.3_ai_system_lifecycle": "missing",
    "8.4_third_party_relationships": "partial",
    "9.1_monitoring": "partial",
    "9.2_internal_audit": "missing",
    "9.3_management_review": "documented",
    "10.1_continual_improvement": "partial",
    "10.2_nonconformity_capa": "documented"
  }
}

Usage:
    python aims_gap_analyzer.py                       # uses embedded sample
    python aims_gap_analyzer.py path/to/evidence.json
    python aims_gap_analyzer.py evidence.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "organization": "Acme AI Inc.",
    "scope_statement": "Customer-facing recommendation engine + internal LLM tools",
    "certification_target": "stage_1_audit_in_q3",
    "evidence": {
        "4.1_context_external": "documented",
        "4.2_interested_parties": "documented",
        "4.3_scope_statement": "documented",
        "4.4_aims_processes": "partial",
        "5.1_leadership_commitment": "documented",
        "5.2_ai_policy": "partial",
        "5.3_roles_responsibilities": "missing",
        "6.1.2_risk_assessment": "documented",
        "6.1.3_risk_treatment": "partial",
        "6.1.4_impact_assessment": "missing",
        "6.2_objectives": "documented",
        "7.1_resources": "documented",
        "7.2_competence": "missing",
        "7.3_awareness": "partial",
        "7.4_communication": "documented",
        "7.5_documented_info": "documented",
        "8.1_operational_planning": "documented",
        "8.2_impact_assessment_process": "partial",
        "8.3_ai_system_lifecycle": "missing",
        "8.4_third_party_relationships": "partial",
        "9.1_monitoring": "partial",
        "9.2_internal_audit": "missing",
        "9.3_management_review": "documented",
        "10.1_continual_improvement": "partial",
        "10.2_nonconformity_capa": "documented",
    },
}


# Clause requirements + severity if missing
# severity: 'critical' = major nonconformity at stage 1, blocks certification
#           'major' = major nonconformity at stage 2
#           'minor' = minor nonconformity, requires corrective action plan
#           'observation' = improvement opportunity
CLAUSE_REQUIREMENTS: Dict[str, Dict[str, Any]] = {
    "4.1_context_external": {"clause": "4.1", "title": "External & internal context", "severity": "minor"},
    "4.2_interested_parties": {"clause": "4.2", "title": "Interested parties", "severity": "minor"},
    "4.3_scope_statement": {"clause": "4.3", "title": "AIMS scope statement", "severity": "critical"},
    "4.4_aims_processes": {"clause": "4.4", "title": "AIMS processes & interactions", "severity": "major"},
    "5.1_leadership_commitment": {"clause": "5.1", "title": "Leadership commitment", "severity": "major"},
    "5.2_ai_policy": {"clause": "5.2", "title": "AI policy", "severity": "critical"},
    "5.3_roles_responsibilities": {"clause": "5.3", "title": "Roles, responsibilities, authorities", "severity": "critical"},
    "6.1.2_risk_assessment": {"clause": "6.1.2", "title": "AI risk assessment", "severity": "critical"},
    "6.1.3_risk_treatment": {"clause": "6.1.3", "title": "AI risk treatment", "severity": "critical"},
    "6.1.4_impact_assessment": {"clause": "6.1.4", "title": "AI system impact assessment", "severity": "major"},
    "6.2_objectives": {"clause": "6.2", "title": "AI objectives & planning", "severity": "minor"},
    "7.1_resources": {"clause": "7.1", "title": "Resources", "severity": "minor"},
    "7.2_competence": {"clause": "7.2", "title": "Competence", "severity": "major"},
    "7.3_awareness": {"clause": "7.3", "title": "Awareness", "severity": "minor"},
    "7.4_communication": {"clause": "7.4", "title": "Communication", "severity": "minor"},
    "7.5_documented_info": {"clause": "7.5", "title": "Documented information", "severity": "major"},
    "8.1_operational_planning": {"clause": "8.1", "title": "Operational planning & control", "severity": "major"},
    "8.2_impact_assessment_process": {"clause": "8.2", "title": "Impact assessment process", "severity": "major"},
    "8.3_ai_system_lifecycle": {"clause": "8.3", "title": "AI system lifecycle process", "severity": "critical"},
    "8.4_third_party_relationships": {"clause": "8.4", "title": "Third-party / customer relationships", "severity": "major"},
    "9.1_monitoring": {"clause": "9.1", "title": "Monitoring, measurement, analysis, evaluation", "severity": "major"},
    "9.2_internal_audit": {"clause": "9.2", "title": "Internal audit programme", "severity": "critical"},
    "9.3_management_review": {"clause": "9.3", "title": "Management review", "severity": "critical"},
    "10.1_continual_improvement": {"clause": "10.1", "title": "Continual improvement", "severity": "minor"},
    "10.2_nonconformity_capa": {"clause": "10.2", "title": "Nonconformity & corrective action", "severity": "major"},
}

STATUS_SCORE = {"documented": 1.0, "partial": 0.5, "missing": 0.0}
SEVERITY_RANK = {"critical": 0, "major": 1, "minor": 2, "observation": 3}


def remediation_action(req_key: str, status: str) -> str:
    """Deterministic one-sentence next step per (clause, status)."""
    if status == "documented":
        return "Maintain via management review; re-verify at next internal audit."
    titles = CLAUSE_REQUIREMENTS[req_key]["title"]
    if status == "partial":
        return f"Complete documentation of '{titles}' — confirm signoff, version control, evidence trail."
    return f"Create from scratch: '{titles}'. Assign owner; target close before stage 1 audit."


def analyze(payload: Dict[str, Any]) -> Dict[str, Any]:
    evidence = payload.get("evidence", {})
    findings: List[Dict[str, Any]] = []
    total_weight = 0.0
    achieved_weight = 0.0

    for req_key, meta in CLAUSE_REQUIREMENTS.items():
        status = evidence.get(req_key, "missing")
        score = STATUS_SCORE.get(status, 0.0)
        # Severity-weighted: critical = 4, major = 2, minor = 1
        weight = {"critical": 4, "major": 2, "minor": 1, "observation": 1}[meta["severity"]]
        total_weight += weight
        achieved_weight += weight * score

        findings.append({
            "clause": meta["clause"],
            "title": meta["title"],
            "status": status,
            "severity_if_missing": meta["severity"],
            "remediation": remediation_action(req_key, status),
        })

    coverage_pct = round((achieved_weight / total_weight) * 100, 1) if total_weight else 0

    # Sort findings: missing/partial first by severity, then documented last
    def sort_key(f: Dict[str, Any]) -> tuple:
        status_order = {"missing": 0, "partial": 1, "documented": 2}
        return (status_order[f["status"]], SEVERITY_RANK[f["severity_if_missing"]], f["clause"])

    findings.sort(key=sort_key)

    open_gaps = [f for f in findings if f["status"] != "documented"]
    critical_gaps = [f for f in open_gaps if f["severity_if_missing"] == "critical"]
    major_gaps = [f for f in open_gaps if f["severity_if_missing"] == "major"]

    readiness = "ready" if not critical_gaps and len(major_gaps) <= 1 else (
        "stage_2_candidate" if not critical_gaps else "not_ready"
    )

    return {
        "organization": payload.get("organization"),
        "scope": payload.get("scope_statement"),
        "coverage_pct_weighted": coverage_pct,
        "certification_readiness": readiness,
        "critical_gap_count": len(critical_gaps),
        "major_gap_count": len(major_gaps),
        "open_gap_count": len(open_gaps),
        "findings": findings,
    }


def render_text(r: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("ISO/IEC 42001 AIMS — GAP ANALYSIS")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Organization: {r['organization']}")
    lines.append(f"Scope: {r['scope']}")
    lines.append(f"Weighted coverage: {r['coverage_pct_weighted']}%")
    lines.append(f"Certification readiness: {r['certification_readiness']}")
    lines.append(f"Critical gaps: {r['critical_gap_count']}  |  Major gaps: {r['major_gap_count']}  |  Open total: {r['open_gap_count']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("FINDINGS (open gaps first; critical highlighted):")
    lines.append("")

    for f in r["findings"]:
        marker = {"missing": "[X] ", "partial": "[~] ", "documented": "[✓] "}[f["status"]]
        sev = f["severity_if_missing"].upper() if f["status"] != "documented" else "OK"
        lines.append(f"  {marker}Clause {f['clause']:6s}  {f['title']:50s}  [{sev}]")
        if f["status"] != "documented":
            lines.append(f"        → {f['remediation']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("READINESS RULE: 'ready' = 0 critical AND ≤ 1 major. 'stage_2_candidate' = 0 critical.")
    lines.append("                Any critical gap blocks stage 1 certification.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="ISO/IEC 42001 AIMS gap analysis across Clauses 4-10.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to AIMS evidence JSON (uses embedded sample if omitted)")
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
        source = "<embedded sample: mid-stage AI SaaS, pre stage-1 audit>"

    result = analyze(payload)
    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))
    return 0


if __name__ == "__main__":
    sys.exit(main())
