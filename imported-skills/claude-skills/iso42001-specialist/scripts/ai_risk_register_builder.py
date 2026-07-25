#!/usr/bin/env python3
"""ai_risk_register_builder.py — ISO/IEC 42001 Annex A risk register + control mapping.

Stdlib-only. Takes identified AI risks (per ISO 23894 risk identification) and produces a
structured register with:
  - severity rating (likelihood × impact, 5x5 matrix)
  - mapped Annex A controls (treatment selection)
  - residual risk verdict (accept / additional treatment required / escalate)
  - treatment option per ISO 23894 (modify / share / retain / avoid)

Deterministic logic per ISO 23894:2023 risk-management process. No LLM calls.

Input schema (JSON):
{
  "organization": "Acme AI Inc.",
  "ai_system": "Customer recommendation engine v3",
  "risks": [
    {
      "id": "R-001",
      "source": "training_data",
      "event": "Biased dataset over-represents one demographic",
      "consequence": "Discriminatory recommendations; regulatory exposure",
      "likelihood": 3,           # 1-5
      "impact": 4,               # 1-5
      "controls_applied": ["A.7.3", "A.7.5", "A.5.2"]
    }
  ]
}

Usage:
    python ai_risk_register_builder.py                       # uses embedded 7-risk sample
    python ai_risk_register_builder.py path/to/risks.json
    python ai_risk_register_builder.py risks.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "organization": "Acme AI Inc.",
    "ai_system": "Customer recommendation engine v3",
    "risks": [
        {"id": "R-001", "source": "training_data", "event": "Biased dataset over-represents one demographic",
         "consequence": "Discriminatory recommendations; regulatory exposure", "likelihood": 3, "impact": 4,
         "controls_applied": ["A.7.3", "A.7.5", "A.5.2"]},
        {"id": "R-002", "source": "model", "event": "Concept drift after 6 months in production",
         "consequence": "Accuracy degradation; revenue impact", "likelihood": 4, "impact": 3,
         "controls_applied": ["A.9.3", "A.6.2.4"]},
        {"id": "R-003", "source": "deployment", "event": "Inference latency spike under load",
         "consequence": "User-visible failure; SLO breach", "likelihood": 3, "impact": 2,
         "controls_applied": ["A.9.3"]},
        {"id": "R-004", "source": "third_party", "event": "Foundation-model API provider deprecates endpoint",
         "consequence": "Service disruption; migration cost", "likelihood": 2, "impact": 4,
         "controls_applied": ["A.10.2"]},
        {"id": "R-005", "source": "data", "event": "Training data contains PII that should not be retained",
         "consequence": "GDPR fine; trust loss", "likelihood": 2, "impact": 5,
         "controls_applied": ["A.7.2", "A.7.4"]},
        {"id": "R-006", "source": "human_oversight", "event": "High-impact decisions deployed without impact assessment",
         "consequence": "Untracked harm; certification nonconformity", "likelihood": 3, "impact": 5,
         "controls_applied": []},
        {"id": "R-007", "source": "model", "event": "Adversarial prompt injection bypasses content filter",
         "consequence": "Toxic output to end users; reputational damage", "likelihood": 4, "impact": 4,
         "controls_applied": ["A.6.2.4", "A.9.3", "A.9.4"]},
    ],
}


# Severity matrix (5x5): likelihood (1-5) × impact (1-5)
# Score 1-4 = low, 5-9 = medium, 10-16 = high, 17-25 = critical
def severity_rating(likelihood: int, impact: int) -> str:
    score = max(1, min(5, likelihood)) * max(1, min(5, impact))
    if score <= 4:
        return "low"
    if score <= 9:
        return "medium"
    if score <= 16:
        return "high"
    return "critical"


# ISO 23894 risk treatment options
# - modify (apply controls to reduce likelihood/impact)
# - share (transfer via insurance, third-party contracts)
# - retain (accept residual risk with management signoff)
# - avoid (eliminate the activity entirely)
def treatment_option(severity: str, controls_count: int) -> str:
    if severity == "critical" and controls_count == 0:
        return "avoid_or_escalate"
    if severity in ("high", "critical"):
        return "modify"
    if severity == "medium":
        return "modify" if controls_count < 2 else "retain"
    return "retain"


# Residual-risk verdict after applied controls
def residual_verdict(severity: str, controls_count: int) -> str:
    """How many controls are 'enough' for each severity tier (heuristic, ISO 23894 Annex A guidance)."""
    expected = {"low": 0, "medium": 1, "high": 2, "critical": 3}[severity]
    if controls_count >= expected:
        return "acceptable" if severity != "critical" else "acceptable_with_management_signoff"
    return "additional_treatment_required"


# Annex A control descriptions (subset, for output annotation)
ANNEX_A_CATALOG: Dict[str, str] = {
    "A.2.2": "AI policy",
    "A.2.3": "Alignment of AI policy with other organizational policies",
    "A.3.2": "AI roles & responsibilities",
    "A.3.3": "Reporting of concerns",
    "A.4.2": "Resources for AI systems — data",
    "A.4.3": "Resources for AI systems — tooling",
    "A.4.4": "Resources for AI systems — human resources",
    "A.5.2": "AI system impact assessment",
    "A.5.4": "Documentation of impact assessment",
    "A.6.2.2": "AI system objectives",
    "A.6.2.3": "AI system lifecycle phases",
    "A.6.2.4": "Verification & validation of AI system",
    "A.7.2": "Data management for AI systems",
    "A.7.3": "Data quality",
    "A.7.4": "Data provenance",
    "A.7.5": "Data preparation",
    "A.8.2": "System documentation for users",
    "A.8.3": "User information",
    "A.8.4": "Communication of AI incidents",
    "A.9.2": "Intended use of AI system",
    "A.9.3": "Monitoring of AI system operation",
    "A.9.4": "Logging of AI system events",
    "A.10.2": "Supplier (third-party) relationships",
    "A.10.3": "Customer relationships",
}


def annotate_risk(risk: Dict[str, Any]) -> Dict[str, Any]:
    likelihood = int(risk.get("likelihood", 0))
    impact = int(risk.get("impact", 0))
    controls = list(risk.get("controls_applied", []))
    sev = severity_rating(likelihood, impact)
    treatment = treatment_option(sev, len(controls))
    residual = residual_verdict(sev, len(controls))

    return {
        "id": risk.get("id"),
        "source": risk.get("source"),
        "event": risk.get("event"),
        "consequence": risk.get("consequence"),
        "likelihood": likelihood,
        "impact": impact,
        "severity_score": likelihood * impact,
        "severity": sev,
        "controls_applied": [{"id": c, "title": ANNEX_A_CATALOG.get(c, "<unknown control>")} for c in controls],
        "control_count": len(controls),
        "treatment_option": treatment,
        "residual_verdict": residual,
    }


def analyze(payload: Dict[str, Any]) -> Dict[str, Any]:
    risks = [annotate_risk(r) for r in payload.get("risks", [])]
    # Sort by severity (critical first), then by control gap (largest first)
    sev_rank = {"critical": 0, "high": 1, "medium": 2, "low": 3}
    risks.sort(key=lambda r: (sev_rank[r["severity"]], -r["severity_score"]))

    counts_by_sev = {s: 0 for s in sev_rank}
    requires_action = 0
    for r in risks:
        counts_by_sev[r["severity"]] += 1
        if r["residual_verdict"] == "additional_treatment_required":
            requires_action += 1

    return {
        "organization": payload.get("organization"),
        "ai_system": payload.get("ai_system"),
        "total_risks": len(risks),
        "by_severity": counts_by_sev,
        "requires_additional_treatment": requires_action,
        "risks": risks,
    }


def render_text(r: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("AI RISK REGISTER — ISO/IEC 42001 Annex A + ISO 23894 treatment")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Organization: {r['organization']}")
    lines.append(f"AI system: {r['ai_system']}")
    lines.append(f"Total risks: {r['total_risks']}")
    s = r["by_severity"]
    lines.append(f"By severity:  critical={s['critical']}  high={s['high']}  medium={s['medium']}  low={s['low']}")
    lines.append(f"Risks requiring additional treatment: {r['requires_additional_treatment']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("REGISTER (highest severity first):")
    lines.append("")

    for risk in r["risks"]:
        lines.append(f"  [{risk['id']}] {risk['event']}")
        lines.append(f"      Source: {risk['source']}  |  L={risk['likelihood']} × I={risk['impact']} = {risk['severity_score']}  →  {risk['severity'].upper()}")
        lines.append(f"      Consequence: {risk['consequence']}")
        if risk["controls_applied"]:
            ctrl_str = ", ".join(c["id"] for c in risk["controls_applied"])
            lines.append(f"      Controls applied ({risk['control_count']}): {ctrl_str}")
        else:
            lines.append(f"      Controls applied: NONE")
        lines.append(f"      Treatment option: {risk['treatment_option']}")
        lines.append(f"      Residual verdict: {risk['residual_verdict']}")
        lines.append("")

    lines.append("-" * 72)
    lines.append("RULES:")
    lines.append("  - 'critical' severity (score 17-25) WITHOUT controls → 'avoid_or_escalate' to management.")
    lines.append("  - 'additional_treatment_required' → add Annex A controls or formally accept residual risk in writing.")
    lines.append("  - All 'retain' verdicts require Clause 6.1.3 risk-treatment plan signoff.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="ISO/IEC 42001 Annex A risk register builder with ISO 23894 treatment options.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to risks JSON (uses embedded sample if omitted)")
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
        source = "<embedded sample: 7-risk recommendation engine register>"

    result = analyze(payload)
    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))
    return 0


if __name__ == "__main__":
    sys.exit(main())
