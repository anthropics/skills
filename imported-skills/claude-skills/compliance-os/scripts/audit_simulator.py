#!/usr/bin/env python3
"""audit_simulator.py — Mock internal audit generator per ISO 19011 + IIA IPPF.

Stdlib-only. Given a framework + scope, generates a realistic mock audit with:
  - 8-15 finding scenarios per typical ISO 19011 audit depth
  - Severity distribution matching IIA expectations:
      observation/OFI: ≥ 40%
      minor:           20-30%
      major:           15-25%
      critical:        ≤ 15%
  - 3-5 interview questions per scoped control
  - Document-review request list
  - Walk-through scenarios where applicable

Deterministic generation from finding templates. Severity distribution is
proportional to the scope size. No randomness, no LLM calls.

Input schema (JSON):
{
  "audit_name": "Q3 ISO 27001 internal audit — Platform team",
  "framework": "iso_27001",
  "scope_controls": ["A.5.15", "A.8.2", "A.8.15", "A.8.32", "A.5.19"],
  "auditee_team": "Platform engineering",
  "prior_year_findings_open": 2
}

Usage:
    python audit_simulator.py
    python audit_simulator.py path/to/audit_scope.json
    python audit_simulator.py audit_scope.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "audit_name": "Q3 ISO 27001 internal audit — Platform team",
    "framework": "iso_27001",
    "scope_controls": ["A.5.15", "A.8.2", "A.8.15", "A.8.32", "A.5.19", "A.5.24", "A.6.8"],
    "auditee_team": "Platform engineering",
    "prior_year_findings_open": 2,
}


# Finding template library (theme -> {severity bucket -> finding patterns})
# Each template produces a finding scenario when invoked.
FINDING_TEMPLATES: Dict[str, Dict[str, List[str]]] = {
    "access_control": {
        "critical": [
            "Privileged access reviewed annually instead of quarterly; orphaned accounts found in production.",
        ],
        "major": [
            "Quarterly access review evidence present but lacks documented business justification for retained privileges.",
            "Joiner-mover-leaver workflow does not auto-deprovision on termination; manual gap of 5+ days observed.",
        ],
        "minor": [
            "Access review records lack documented review-completion timestamps in 2 of 6 sampled reviews.",
        ],
        "observation": [
            "Consider extending RBAC matrix to include cloud-resource scope (currently application-tier only).",
        ],
    },
    "logging_monitoring": {
        "critical": [
            "Production application logs disabled in past 30 days; no detection of the gap until audit fieldwork.",
        ],
        "major": [
            "Log retention configured at 90 days but framework requires 12 months; misalignment not detected.",
            "Tamper-evident logging not enforced on privileged-user activity logs.",
        ],
        "minor": [
            "Monitoring alert thresholds not formally documented; reviewed verbally by SRE only.",
        ],
        "observation": [
            "Centralized log aggregation in place; consider adding anomaly detection.",
        ],
    },
    "change_management": {
        "critical": [
            "Emergency change procedure not formalized; observed 3 cases of production changes without recorded approval.",
        ],
        "major": [
            "Change advisory board records show approvals but no post-implementation review of high-risk changes.",
        ],
        "minor": [
            "Rollback procedure documented but not tested for 2 services in scope.",
        ],
        "observation": [
            "Consider linking change records to deployment automation for stronger evidence chain.",
        ],
    },
    "supplier_mgmt": {
        "critical": [
            "Critical SaaS supplier in use without signed DPA + security questionnaire (GDPR exposure).",
        ],
        "major": [
            "Annual supplier security review not completed for 3 of 8 critical suppliers.",
            "Sub-processor list not maintained for critical suppliers handling personal data.",
        ],
        "minor": [
            "Supplier onboarding checklist exists but not consistently applied across business units.",
        ],
        "observation": [
            "Consider centralizing supplier risk evidence in a single GRC system.",
        ],
    },
    "incident_response": {
        "critical": [
            "Recent P1 incident lacks documented post-incident review (PIR) within 30-day SLA.",
        ],
        "major": [
            "Severity definitions documented but inconsistently applied across teams; impact varies.",
            "Notification SLAs not aligned across frameworks (GDPR 72h, framework X 24h, framework Y 15 days).",
        ],
        "minor": [
            "Incident commander rotation not documented.",
        ],
        "observation": [
            "Consider quarterly tabletop exercises to validate runbooks.",
        ],
    },
}

# Control -> theme mapping (heuristic; deterministic)
CONTROL_TO_THEME: Dict[str, str] = {
    # ISO 27001 mapping
    "A.5.15": "access_control",
    "A.8.2": "access_control",
    "A.8.3": "access_control",
    "A.5.19": "supplier_mgmt",
    "A.5.20": "supplier_mgmt",
    "A.5.21": "supplier_mgmt",
    "A.5.22": "supplier_mgmt",
    "A.5.24": "incident_response",
    "A.5.25": "incident_response",
    "A.5.26": "incident_response",
    "A.5.27": "incident_response",
    "A.6.8": "incident_response",
    "A.8.15": "logging_monitoring",
    "A.8.16": "logging_monitoring",
    "A.8.32": "change_management",
    # SOC 2 mapping
    "CC6.1": "access_control",
    "CC6.2": "access_control",
    "CC6.3": "access_control",
    "CC9.2": "supplier_mgmt",
    "CC7.3": "incident_response",
    "CC7.4": "incident_response",
    "CC7.5": "incident_response",
    "CC7.1": "logging_monitoring",
    "CC7.2": "logging_monitoring",
    "CC8.1": "change_management",
    # ISO 42001 mapping
    "A.4.4": "access_control",
    "A.9.3": "logging_monitoring",
    "A.9.4": "logging_monitoring",
    "A.6.2.5": "change_management",
    "A.10.2": "supplier_mgmt",
    "A.8.4": "incident_response",
}


def _severity_rotation() -> List[str]:
    return [
        "observation", "observation", "observation", "minor", "major",
        "observation", "minor", "observation", "major", "critical",
        "minor", "observation", "minor", "observation", "major",
    ]


def generate_findings(payload: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Generate finding scenarios deterministically from scope."""
    findings: List[Dict[str, Any]] = []
    scope = payload.get("scope_controls", [])
    prior_open = payload.get("prior_year_findings_open", 0)

    # Rotate severities to hit IIA-target distribution
    # Target: >= 40% observation, ~25% minor, ~20% major, <= 15% critical
    severity_order = _severity_rotation()
    # Pad if scope is large
    while len(severity_order) < len(scope) + 5:
        severity_order += severity_order

    for idx, control in enumerate(scope):
        theme = CONTROL_TO_THEME.get(control)
        if theme is None:
            continue
        severity = severity_order[idx]
        # If prior_open > 0, force first finding to be major (follow-up)
        if idx == 0 and prior_open > 0:
            severity = "major"
        templates = FINDING_TEMPLATES.get(theme, {}).get(severity, [])
        if not templates:
            severity = "observation"
            templates = FINDING_TEMPLATES.get(theme, {}).get("observation", ["General observation noted."])
        finding_text = templates[idx % len(templates)]
        findings.append({
            "id": f"F-{idx + 1:02d}",
            "control": control,
            "theme": theme,
            "severity": severity,
            "description": finding_text,
            "follow_up_from_prior": idx == 0 and prior_open > 0,
        })

    # Add 3-6 additional observations to hit 10-15 total range per ISO 19011 typical depth
    extras_needed = max(0, 10 - len(findings))
    extras_added = 0
    for theme in FINDING_TEMPLATES:
        if extras_added >= extras_needed:
            break
        if not any(f["theme"] == theme for f in findings):
            continue
        templates = FINDING_TEMPLATES[theme]["observation"]
        findings.append({
            "id": f"F-{len(findings) + 1:02d}",
            "control": "(general)",
            "theme": theme,
            "severity": "observation",
            "description": templates[(extras_added + 1) % len(templates)],
            "follow_up_from_prior": False,
        })
        extras_added += 1

    return findings


def interview_questions(control: str) -> List[str]:
    """Deterministic 3-5 audit interview questions per control theme."""
    theme = CONTROL_TO_THEME.get(control)
    bank = {
        "access_control": [
            "Walk me through how a new joiner gets access provisioned.",
            "Show me the last quarterly access review evidence for a privileged role.",
            "What happens within 24 hours of a termination?",
            "How is multi-factor authentication enforced for admin access?",
        ],
        "logging_monitoring": [
            "Show me a sample log entry for a privileged action in the last 30 days.",
            "What's the log retention configuration, and where is it documented?",
            "How are tampering attempts detected and alerted?",
            "Show me a monitoring alert that fired in the last 7 days and how it was triaged.",
        ],
        "change_management": [
            "Walk me through the change approval workflow for a production deployment.",
            "Show me a rejected change in the last quarter and the rejection rationale.",
            "Where is the rollback procedure for service X documented and last tested?",
            "How are emergency changes handled differently from standard changes?",
        ],
        "supplier_mgmt": [
            "Show me the supplier inventory and the last review date for 3 critical suppliers.",
            "How are AI-specific contractual clauses tracked for AI service suppliers?",
            "Walk me through onboarding of a new critical SaaS supplier.",
            "Show me where signed DPAs are stored for personal-data sub-processors.",
        ],
        "incident_response": [
            "Show me the last 3 incidents with severity, root cause, and corrective action.",
            "Walk me through your serious-incident reporting timing for GDPR + AI Act.",
            "Where are post-incident reviews documented and tracked to closure?",
            "How is the on-call rotation defined and communicated?",
        ],
    }
    return bank.get(theme, [
        "Walk me through how this control is implemented day-to-day.",
        "Show me records of the control being operated in the last 90 days.",
        "How is effectiveness of this control measured?",
    ])


def document_requests(scope: List[str]) -> List[str]:
    themes = {CONTROL_TO_THEME.get(c) for c in scope if CONTROL_TO_THEME.get(c)}
    docs = []
    for t in themes:
        if t == "access_control":
            docs.append("Access control policy + last 2 quarterly access reviews + RBAC matrix")
        elif t == "logging_monitoring":
            docs.append("Logging policy + log retention configuration + last 30 days of sample privileged-action logs")
        elif t == "change_management":
            docs.append("Change management procedure + last 90 days change records + rollback procedure")
        elif t == "supplier_mgmt":
            docs.append("Supplier inventory + last annual supplier reviews + 3 sample DPAs")
        elif t == "incident_response":
            docs.append("Incident response procedure + last 5 incident records + post-incident reviews")
    return docs


def analyze(payload: Dict[str, Any]) -> Dict[str, Any]:
    findings = generate_findings(payload)
    by_sev: Dict[str, int] = {"critical": 0, "major": 0, "minor": 0, "observation": 0}
    for f in findings:
        by_sev[f["severity"]] += 1

    total = len(findings)
    obs_pct = round((by_sev["observation"] / total) * 100, 1) if total else 0
    crit_pct = round((by_sev["critical"] / total) * 100, 1) if total else 0
    healthy = (obs_pct >= 40) and (crit_pct <= 15)

    return {
        "audit_name": payload.get("audit_name"),
        "framework": payload.get("framework"),
        "scope_controls": payload.get("scope_controls", []),
        "auditee_team": payload.get("auditee_team"),
        "findings_total": total,
        "findings_by_severity": by_sev,
        "severity_distribution_healthy": healthy,
        "obs_pct": obs_pct,
        "crit_pct": crit_pct,
        "findings": findings,
        "interview_questions_per_control": {c: interview_questions(c) for c in payload.get("scope_controls", [])},
        "document_review_requests": document_requests(payload.get("scope_controls", [])),
    }


def render_text(r: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("COMPLIANCE OS — MOCK INTERNAL AUDIT (per ISO 19011 + IIA IPPF)")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Audit: {r['audit_name']}")
    lines.append(f"Framework: {r['framework']}  |  Auditee: {r['auditee_team']}")
    lines.append(f"Scope controls ({len(r['scope_controls'])}): {', '.join(r['scope_controls'])}")
    lines.append("")
    s = r["findings_by_severity"]
    lines.append(f"Findings total: {r['findings_total']}  "
                 f"(critical={s['critical']}, major={s['major']}, minor={s['minor']}, observation={s['observation']})")
    lines.append(f"Distribution: observation={r['obs_pct']}%  critical={r['crit_pct']}%  "
                 f"healthy={r['severity_distribution_healthy']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("FINDINGS:")
    lines.append("")
    for f in r["findings"]:
        marker = "🔥 FOLLOW-UP" if f["follow_up_from_prior"] else ""
        lines.append(f"  [{f['id']}] [{f['severity'].upper():12s}] control={f['control']:12s}  theme={f['theme']:20s}  {marker}")
        lines.append(f"        {f['description']}")
        lines.append("")

    lines.append("-" * 72)
    lines.append("INTERVIEW QUESTIONS PER CONTROL:")
    for ctrl, qs in r["interview_questions_per_control"].items():
        lines.append(f"  {ctrl}:")
        for q in qs:
            lines.append(f"    - {q}")
        lines.append("")

    lines.append("-" * 72)
    lines.append("DOCUMENT-REVIEW REQUESTS:")
    for d in r["document_review_requests"]:
        lines.append(f"  - {d}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("HEALTHY-DISTRIBUTION RULE (IIA expectations):")
    lines.append("  observation/OFI ≥ 40%   AND   critical ≤ 15%")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Mock internal audit generator per ISO 19011 + IIA IPPF + AICPA AT-C.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to audit scope JSON (uses embedded sample if omitted)")
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
        source = "<embedded sample: Q3 ISO 27001 internal audit, Platform team, 7 controls>"

    result = analyze(payload)
    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))
    return 0


if __name__ == "__main__":
    sys.exit(main())
