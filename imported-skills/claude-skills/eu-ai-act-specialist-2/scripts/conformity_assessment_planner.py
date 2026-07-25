#!/usr/bin/env python3
"""conformity_assessment_planner.py — EU AI Act Article 43 conformity routing + Annex IV checklist.

Stdlib-only. For a high-risk AI system, selects the conformity assessment Module
(A internal control vs H full QMS + notified body) per Article 43 and produces the
Annex IV technical documentation checklist.

Decision rule (Article 43):
  - Biometrics (Annex III §1) → Module H (notified body required) by default
  - All other Annex III categories → Module A (internal control) is permissible
    where harmonised standards are applied (Article 40)
  - Annex I products (safety components) → follow sectoral law's existing procedure

Input schema (JSON):
{
  "system_name": "CV-screening AI",
  "annex_iii_category": "employment",
  "applies_harmonised_standards": true,
  "harmonised_standards_referenced": ["EN ISO/IEC 42001", "EN ISO/IEC 23894"],
  "annex_i_product": false,
  "annex_i_sectoral_law": null,
  "existing_iso_42001_certification": false,
  "existing_iso_27001_certification": true
}

Usage:
    python conformity_assessment_planner.py                  # embedded sample
    python conformity_assessment_planner.py path/to/system.json
    python conformity_assessment_planner.py system.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "system_name": "CV-screening AI for hiring",
    "annex_iii_category": "employment",
    "applies_harmonised_standards": True,
    "harmonised_standards_referenced": ["EN ISO/IEC 42001", "EN ISO/IEC 23894"],
    "annex_i_product": False,
    "annex_i_sectoral_law": None,
    "existing_iso_42001_certification": False,
    "existing_iso_27001_certification": True,
}


# Annex IV — Technical Documentation requirements (per Article 11(1))
ANNEX_IV_ITEMS = [
    {
        "id": "iv.1",
        "title": "General description of the AI system",
        "subitems": [
            "intended purpose",
            "name & version of provider",
            "system architecture overview",
            "instructions for use (Article 13)",
        ],
        "reusable_from": "ISO 42001 SKILL scope statement; ISO 27001 system documentation",
    },
    {
        "id": "iv.2",
        "title": "Detailed description of system elements",
        "subitems": [
            "methods used (ML, rule-based, etc.)",
            "training, validation, test datasets (provenance + quality + bias mitigation per Article 10)",
            "human oversight measures (Article 14)",
            "key design choices including assumptions",
            "computational resources used",
        ],
        "reusable_from": "ISO 42001 A.6 lifecycle documentation; ISO 42001 A.7 data evidence; model cards",
    },
    {
        "id": "iv.3",
        "title": "Information about monitoring, functioning, control",
        "subitems": [
            "performance metrics & expected accuracy",
            "logging capabilities (Article 12)",
            "input data specifications",
            "human-in-the-loop and oversight (Article 14)",
        ],
        "reusable_from": "ISO 42001 A.9.3 monitoring; ISO 42001 A.9.4 logging",
    },
    {
        "id": "iv.4",
        "title": "Description of risk management system",
        "subitems": [
            "Article 9 risk management process",
            "identified risks + mitigation measures",
            "residual risk acceptance",
            "testing methodology",
        ],
        "reusable_from": "ISO 42001 Clause 6.1 + Annex A.5 + Annex A.6.2.4; ISO 23894 process",
    },
    {
        "id": "iv.5",
        "title": "Description of changes to the system after placing on market",
        "subitems": [
            "change-management procedure",
            "version control of model + data",
            "re-evaluation triggers (concept drift, fine-tuning)",
        ],
        "reusable_from": "ISO 27001 A.8.32 change management; ISO 42001 A.6.2.5 deployment",
    },
    {
        "id": "iv.6",
        "title": "List of harmonised standards applied",
        "subitems": [
            "presumption of conformity per Article 40",
            "alternative solutions documented where standards not applied",
        ],
        "reusable_from": "Standards register",
    },
    {
        "id": "iv.7",
        "title": "EU declaration of conformity",
        "subitems": [
            "Article 47 — provider declares conformity, signed by authorized signatory",
            "kept for 10 years post-market (Article 18)",
        ],
        "reusable_from": "Template only — signed at end of process",
    },
    {
        "id": "iv.8",
        "title": "Post-market monitoring system",
        "subitems": [
            "Article 72 — proactive collection of performance + incident data",
            "serious incident reporting procedure (Article 73)",
            "feedback loop into risk management (Article 9)",
        ],
        "reusable_from": "ISO 42001 A.9.3 monitoring + ISO 13485 post-market surveillance pattern",
    },
]


def select_module(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Select conformity assessment Module per Article 43."""
    annex_iii = payload.get("annex_iii_category")
    applies_standards = payload.get("applies_harmonised_standards", False)
    annex_i = payload.get("annex_i_product", False)
    sectoral_law = payload.get("annex_i_sectoral_law")

    if annex_i and sectoral_law:
        return {
            "module": "sectoral",
            "citation": "Article 43(3) — Annex I product follows existing sectoral conformity procedure",
            "notified_body_required": "depends_on_sectoral_law",
            "rationale": f"Follow {sectoral_law} existing procedure; AI Act layered on top.",
        }

    if annex_iii == "biometrics":
        return {
            "module": "H",
            "citation": "Article 43(1) + Annex VII — Full QMS + Notified Body for biometrics",
            "notified_body_required": "yes",
            "rationale": "Biometrics under Annex III §1 require notified-body involvement by default.",
        }

    if annex_iii and applies_standards:
        return {
            "module": "A",
            "citation": "Article 43(2) + Annex VI — Internal control with presumption of conformity",
            "notified_body_required": "no",
            "rationale": "Annex III system applying harmonised standards (Article 40) may use internal control.",
        }

    if annex_iii and not applies_standards:
        return {
            "module": "A_with_caveats",
            "citation": "Article 43(2) + Annex VI — Internal control without harmonised standards",
            "notified_body_required": "optional_but_recommended",
            "rationale": "Internal control still permitted but without presumption of conformity; document alternative compliance evidence in full.",
        }

    return {
        "module": "not_applicable",
        "citation": "System not classified as high-risk; conformity assessment not required",
        "notified_body_required": "no",
        "rationale": "Re-run ai_system_risk_classifier.py to confirm tier.",
    }


def reuse_summary(payload: Dict[str, Any]) -> List[str]:
    """What evidence can be reused from existing certifications."""
    notes = []
    if payload.get("existing_iso_42001_certification"):
        notes.append("ISO 42001 certification: reuse AIMS Clause 6.1 risk evidence (Annex IV item 4)")
        notes.append("ISO 42001 certification: reuse Annex A.6 lifecycle evidence (Annex IV items 1-3)")
        notes.append("ISO 42001 certification: reuse Annex A.9 monitoring evidence (Annex IV item 8)")
    if payload.get("existing_iso_27001_certification"):
        notes.append("ISO 27001 certification: reuse cybersecurity evidence for Article 15 cybersecurity requirement")
        notes.append("ISO 27001 certification: reuse A.5.19 supplier mgmt for Article 25 value-chain responsibilities")
        notes.append("ISO 27001 certification: reuse A.8.15 logging for Annex IV item 3 logging")
    if not notes:
        notes.append("No prior certifications declared; build all Annex IV evidence from scratch")
    return notes


def plan(payload: Dict[str, Any]) -> Dict[str, Any]:
    module = select_module(payload)
    return {
        "system_name": payload.get("system_name"),
        "annex_iii_category": payload.get("annex_iii_category"),
        "conformity_assessment": module,
        "annex_iv_checklist": ANNEX_IV_ITEMS,
        "reuse_from_existing_certifications": reuse_summary(payload),
        "next_steps": _next_steps(module["module"]),
    }


def _next_steps(module: str) -> List[str]:
    base = [
        "Assemble Annex IV pack per the checklist (see Article 11 + Annex IV).",
        "Conduct Article 9 risk management lifecycle (input to Annex IV item 4).",
        "Implement Article 12 logging capabilities (input to Annex IV item 3).",
        "Implement Article 14 human-oversight measures (input to Annex IV items 2-3).",
        "Stand up Article 72 post-market monitoring (input to Annex IV item 8).",
    ]
    if module == "H":
        base.append("Engage notified body for Module H assessment (Annex VII).")
        base.append("Operate full QMS per Article 17 — pair with ISO 42001 AIMS for cross-reuse.")
    elif module == "A":
        base.append("Verify each harmonised standard referenced is on Article 40 list at decision date.")
        base.append("Sign EU declaration of conformity (Article 47) AFTER assembling Annex IV pack.")
        base.append("Affix CE marking (Article 48).")
        base.append("Register in EU database (Article 71) before placing on market.")
    elif module == "A_with_caveats":
        base.append("Document equivalent alternative evidence for each requirement without a harmonised standard.")
        base.append("Consider voluntary notified-body engagement to reduce regulatory risk.")
    return base


def render_text(p: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("EU AI ACT — CONFORMITY ASSESSMENT PLAN")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"System: {p['system_name']}")
    lines.append(f"Annex III category: {p['annex_iii_category']}")
    lines.append("")
    c = p["conformity_assessment"]
    lines.append(f"Conformity Module: {c['module']}")
    lines.append(f"Citation: {c['citation']}")
    lines.append(f"Notified body required: {c['notified_body_required']}")
    lines.append(f"Rationale: {c['rationale']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("ANNEX IV TECHNICAL DOCUMENTATION CHECKLIST (8 items):")
    lines.append("")

    for item in p["annex_iv_checklist"]:
        lines.append(f"  [{item['id']}] {item['title']}")
        for sub in item["subitems"]:
            lines.append(f"        - {sub}")
        lines.append(f"        Reusable: {item['reusable_from']}")
        lines.append("")

    lines.append("-" * 72)
    lines.append("REUSE FROM EXISTING CERTIFICATIONS:")
    for note in p["reuse_from_existing_certifications"]:
        lines.append(f"  - {note}")
    lines.append("")

    lines.append("-" * 72)
    lines.append("NEXT STEPS:")
    for step in p["next_steps"]:
        lines.append(f"  - {step}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="EU AI Act Article 43 conformity routing + Annex IV technical documentation checklist.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to system JSON (uses embedded sample if omitted)")
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
        source = "<embedded sample: CV-screening AI, harmonised standards applied>"

    result = plan(payload)
    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))
    return 0


if __name__ == "__main__":
    sys.exit(main())
