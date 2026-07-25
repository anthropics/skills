#!/usr/bin/env python3
"""ai_act_obligation_tracker.py — EU AI Act per-role obligation matrix.

Stdlib-only. Given an organization's role(s) per Article 25 (provider, deployer,
importer, distributor, authorized representative) and AI system tier(s), produces
a deadline-sorted obligation matrix tied to the Act's phased application:
  - 2 Feb 2025: Article 5 prohibitions + Article 4 AI literacy
  - 2 Aug 2025: GPAI Articles 51-55 + governance + penalties
  - 2 Aug 2026: Title III high-risk obligations
  - 2 Aug 2027: Annex I sectoral high-risk obligations

Deterministic logic referencing Articles 16, 22, 23, 24, 25, 26, 27, 50,
51-55, 72, 73 + phasing per Article 113.

Input schema (JSON):
{
  "organization": "Acme AI Inc.",
  "establishment": "non_eu",          # eu | non_eu
  "roles": [
    {"role": "provider", "systems_tier": "high_risk"},
    {"role": "deployer", "systems_tier": "high_risk", "public_sector": false},
    {"role": "deployer", "systems_tier": "limited_risk"}
  ],
  "deploys_gpai": true,
  "gpai_systemic_risk": false
}

Usage:
    python ai_act_obligation_tracker.py
    python ai_act_obligation_tracker.py path/to/roles.json
    python ai_act_obligation_tracker.py roles.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "organization": "Acme AI Inc.",
    "establishment": "non_eu",
    "roles": [
        {"role": "provider", "systems_tier": "high_risk"},
        {"role": "deployer", "systems_tier": "high_risk", "public_sector": False},
        {"role": "deployer", "systems_tier": "limited_risk"},
    ],
    "deploys_gpai": True,
    "gpai_systemic_risk": False,
}


# Phasing reference (per Article 113)
PHASE_DATES = {
    "article_5_prohibitions": "2025-02-02",
    "article_4_ai_literacy": "2025-02-02",
    "gpai_articles_51_55": "2025-08-02",
    "governance_penalties": "2025-08-02",
    "title_iii_high_risk_general": "2026-08-02",
    "title_iii_annex_i_sectoral": "2027-08-02",
}


# Obligations per role + tier
PROVIDER_HIGH_RISK = [
    ("Article 9 — Establish risk management system across the full AI lifecycle", "title_iii_high_risk_general"),
    ("Article 10 — Data governance: training/validation/test data quality + bias mitigation", "title_iii_high_risk_general"),
    ("Article 11 — Maintain technical documentation per Annex IV", "title_iii_high_risk_general"),
    ("Article 12 — Implement automatic event logging", "title_iii_high_risk_general"),
    ("Article 13 — Provide instructions for use to deployers", "title_iii_high_risk_general"),
    ("Article 14 — Design for human oversight", "title_iii_high_risk_general"),
    ("Article 15 — Accuracy, robustness, cybersecurity", "title_iii_high_risk_general"),
    ("Article 16 — General provider obligations + named contact person", "title_iii_high_risk_general"),
    ("Article 17 — Establish quality management system (QMS)", "title_iii_high_risk_general"),
    ("Article 43 — Undertake conformity assessment before placing on market", "title_iii_high_risk_general"),
    ("Article 47 — Sign EU declaration of conformity (10-year retention per Article 18)", "title_iii_high_risk_general"),
    ("Article 48 — Affix CE marking", "title_iii_high_risk_general"),
    ("Article 49 — Register in EU database (Article 71) for Annex III systems", "title_iii_high_risk_general"),
    ("Article 72 — Establish post-market monitoring system", "title_iii_high_risk_general"),
    ("Article 73 — Report serious incidents to market surveillance authority within 15 days (or 2 days for critical-infrastructure incidents)", "title_iii_high_risk_general"),
]

DEPLOYER_HIGH_RISK = [
    ("Article 26(1) — Use the AI system according to provider's instructions for use", "title_iii_high_risk_general"),
    ("Article 26(2) — Assign human oversight to natural persons with necessary competence + authority + support", "title_iii_high_risk_general"),
    ("Article 26(3) — Ensure input data is relevant + sufficiently representative", "title_iii_high_risk_general"),
    ("Article 26(4) — Monitor operation; cease use if it presents Article 79 risk", "title_iii_high_risk_general"),
    ("Article 26(5) — Maintain automatically generated logs (Article 12) for ≥ 6 months", "title_iii_high_risk_general"),
    ("Article 26(7) — Inform workers + their representatives before putting the system into use in workplace", "title_iii_high_risk_general"),
    ("Article 26(8) — Cooperate with national competent authorities + AI Office", "title_iii_high_risk_general"),
    ("Article 50 — Inform natural persons subject to AI-decisions (transparency)", "title_iii_high_risk_general"),
    ("Article 86 — Right to explanation of individual decision", "title_iii_high_risk_general"),
]

DEPLOYER_PUBLIC_SECTOR = [
    ("Article 27 — Conduct Fundamental Rights Impact Assessment (FRIA) before deploying", "title_iii_high_risk_general"),
]

DEPLOYER_LIMITED_RISK = [
    ("Article 50(1) — Inform natural persons they are interacting with an AI system", "governance_penalties"),
    ("Article 50(4) — Disclose deepfakes (image, audio, video) as AI-generated; mark machine-readable", "governance_penalties"),
]

IMPORTER = [
    ("Article 23 — Verify provider completed conformity assessment + has technical docs", "title_iii_high_risk_general"),
    ("Article 23(3) — Indicate name, contact, address on the AI system or accompanying docs", "title_iii_high_risk_general"),
]

DISTRIBUTOR = [
    ("Article 24 — Verify CE marking + documentation before making the system available", "title_iii_high_risk_general"),
]

AUTH_REP_NON_EU_PROVIDER = [
    ("Article 22 — Non-EU providers MUST appoint an authorized representative established in the EU", "title_iii_high_risk_general"),
    ("Article 22(3) — Representative keeps technical docs available + liable for provider obligations", "title_iii_high_risk_general"),
]

GPAI_ALL = [
    ("Article 53 — Maintain up-to-date technical documentation of GPAI model", "gpai_articles_51_55"),
    ("Article 53 — Provide information to downstream providers integrating the model", "gpai_articles_51_55"),
    ("Article 53(1)(c) — Establish policy to comply with EU copyright law", "gpai_articles_51_55"),
    ("Article 53(1)(d) — Publish detailed summary about training data", "gpai_articles_51_55"),
]

GPAI_SYSTEMIC_RISK = [
    ("Article 55 — Perform model evaluations including adversarial testing", "gpai_articles_51_55"),
    ("Article 55 — Assess + mitigate systemic risks", "gpai_articles_51_55"),
    ("Article 55 — Track + report serious incidents to AI Office", "gpai_articles_51_55"),
    ("Article 55 — Ensure cybersecurity protection of the model + physical infrastructure", "gpai_articles_51_55"),
]

UNIVERSAL = [
    ("Article 4 — Ensure AI literacy of staff dealing with AI systems", "article_4_ai_literacy"),
    ("Article 5 — No prohibited AI practices", "article_5_prohibitions"),
]


def _make_obs(items: List[tuple], role_label: str) -> List[Dict[str, Any]]:
    return [{"role": role_label, "obligation": ob, "deadline_phase": phase,
             "deadline_date": PHASE_DATES[phase]} for ob, phase in items]


def _role_obligations(role: Dict[str, Any]) -> List[Dict[str, Any]]:
    r_type = role.get("role")
    tier = role.get("systems_tier")
    if r_type == "provider" and tier == "high_risk":
        return _make_obs(PROVIDER_HIGH_RISK, "provider/high-risk")
    if r_type == "deployer" and tier == "high_risk":
        out = _make_obs(DEPLOYER_HIGH_RISK, "deployer/high-risk")
        if role.get("public_sector"):
            out += _make_obs(DEPLOYER_PUBLIC_SECTOR, "deployer/public-sector")
        return out
    if r_type == "deployer" and tier == "limited_risk":
        return _make_obs(DEPLOYER_LIMITED_RISK, "deployer/limited-risk")
    if r_type == "importer":
        return _make_obs(IMPORTER, "importer")
    if r_type == "distributor":
        return _make_obs(DISTRIBUTOR, "distributor")
    return []


def gather_obligations(payload: Dict[str, Any]) -> List[Dict[str, Any]]:
    obligations: List[Dict[str, Any]] = []
    obligations += _make_obs(UNIVERSAL, "any")

    roles = payload.get("roles", [])
    for role in roles:
        obligations += _role_obligations(role)

    if payload.get("establishment") == "non_eu":
        provider_role = any(r.get("role") == "provider" for r in roles)
        if provider_role:
            obligations += _make_obs(AUTH_REP_NON_EU_PROVIDER, "non-EU provider")

    if payload.get("deploys_gpai"):
        obligations += _make_obs(GPAI_ALL, "GPAI provider")
        if payload.get("gpai_systemic_risk"):
            obligations += _make_obs(GPAI_SYSTEMIC_RISK, "GPAI systemic risk")

    obligations.sort(key=lambda x: (x["deadline_date"], x["role"]))
    return obligations


def analyze(payload: Dict[str, Any]) -> Dict[str, Any]:
    obs = gather_obligations(payload)
    by_phase: Dict[str, int] = {}
    by_role: Dict[str, int] = {}
    for o in obs:
        by_phase[o["deadline_phase"]] = by_phase.get(o["deadline_phase"], 0) + 1
        by_role[o["role"]] = by_role.get(o["role"], 0) + 1
    return {
        "organization": payload.get("organization"),
        "establishment": payload.get("establishment"),
        "total_obligations": len(obs),
        "by_phase": by_phase,
        "by_role": by_role,
        "obligations": obs,
    }


def render_text(r: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("EU AI ACT — OBLIGATION MATRIX (deadline-sorted)")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Organization: {r['organization']}")
    lines.append(f"Establishment: {r['establishment']}")
    lines.append(f"Total obligations: {r['total_obligations']}")
    lines.append("")
    lines.append("By deadline phase:")
    for phase, n in sorted(r["by_phase"].items(), key=lambda x: PHASE_DATES.get(x[0], "")):
        lines.append(f"  {PHASE_DATES.get(phase, '?')}  {phase:35s}  {n} obligations")
    lines.append("")
    lines.append("By role:")
    for role, n in sorted(r["by_role"].items()):
        lines.append(f"  {role:30s}  {n} obligations")
    lines.append("")
    lines.append("-" * 72)
    lines.append("FULL LIST (deadline order):")
    lines.append("")
    current_date = None
    for o in r["obligations"]:
        if o["deadline_date"] != current_date:
            current_date = o["deadline_date"]
            lines.append(f"  >> Deadline {current_date} — {o['deadline_phase']}")
        lines.append(f"     [{o['role']:25s}] {o['obligation']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("PHASING (Article 113):")
    lines.append("  2025-02-02: Article 5 prohibitions + Article 4 AI literacy")
    lines.append("  2025-08-02: GPAI (Art. 51-55) + governance + penalties")
    lines.append("  2026-08-02: Title III high-risk (general)")
    lines.append("  2027-08-02: Annex I sectoral high-risk")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="EU AI Act per-role obligation matrix with phasing deadlines.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to roles JSON (uses embedded sample if omitted)")
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
        source = "<embedded sample: non-EU provider + deployer high-risk + GPAI>"

    result = analyze(payload)
    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))
    return 0


if __name__ == "__main__":
    sys.exit(main())
