#!/usr/bin/env python3
"""ai_system_risk_classifier.py — EU AI Act (2024/1689) risk-tier classifier.

Stdlib-only. Takes AI-system characteristics and classifies into one of:
  - prohibited (Article 5)
  - high-risk (Article 6 + Annex III, OR Article 6(1) + Annex I)
  - limited-risk transparency (Article 50)
  - minimal-risk (default)

Deterministic decision tree following the regulation's risk-based architecture
(Recital 26 + Articles 5, 6, 50). Article 6(3) carve-outs applied.

Input schema (JSON):
{
  "systems": [
    {
      "name": "Resume screening AI",
      "intended_purpose": "Filter and rank candidates for hiring",
      "users": "internal_hr",
      "data_processes_natural_persons": true,
      "annex_iii_category": "employment",
      "performs_profiling": true,
      "article_5_practice": null,
      "article_6_1_safety_component": false,
      "article_6_3_carveout_applies": false,
      "interacts_with_natural_persons_directly": false,
      "is_general_purpose_ai_model": false,
      "training_compute_flops": null
    }
  ]
}

Note on `article_5_practice`: this flag is the caller's legal pre-determination
that a listed Article 5 practice applies IN ITS PROHIBITED CONTEXT — the
classifier trusts it and does not re-derive it from the other fields. Context
matters: emotion recognition is prohibited under Article 5(1)(f) ONLY in
workplace and education settings (narrow safety/medical exceptions aside);
the same system in e.g. a retail setting is NOT prohibited — it is subject to
Article 50(3) transparency and possibly Annex III §1 (biometrics) high-risk rules.

Usage:
    python ai_system_risk_classifier.py                       # uses embedded 5-system sample
    python ai_system_risk_classifier.py path/to/systems.json
    python ai_system_risk_classifier.py systems.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Optional


SAMPLE: Dict[str, Any] = {
    "systems": [
        {
            # Article 5(1)(f) prohibits emotion recognition ONLY in WORKPLACE and
            # EDUCATION settings (with narrow safety/medical exceptions). The same
            # system aimed at RETAIL shoppers is NOT prohibited — it falls under
            # Article 50(3) transparency (limited-risk) and may be high-risk under
            # Annex III §1 (biometrics). This sample uses a genuine workplace
            # context so the prohibited tag is correct.
            "name": "Emotion recognition of employees in workplace CCTV",
            "intended_purpose": "Monitor employees' emotional state to score engagement",
            "users": "hr_managers",
            "data_processes_natural_persons": True,
            "annex_iii_category": None,
            "performs_profiling": False,
            "article_5_practice": "emotion_recognition_in_workplace_or_education",
            "article_6_1_safety_component": False,
            "article_6_3_carveout_applies": False,
            "interacts_with_natural_persons_directly": False,
            "is_general_purpose_ai_model": False,
            "training_compute_flops": None,
        },
        {
            "name": "CV-screening AI for job applications",
            "intended_purpose": "Filter and rank candidates for shortlist",
            "users": "internal_hr",
            "data_processes_natural_persons": True,
            "annex_iii_category": "employment",
            "performs_profiling": True,
            "article_5_practice": None,
            "article_6_1_safety_component": False,
            "article_6_3_carveout_applies": False,
            "interacts_with_natural_persons_directly": False,
            "is_general_purpose_ai_model": False,
            "training_compute_flops": None,
        },
        {
            "name": "Customer support chatbot",
            "intended_purpose": "Answer support questions; route to human agents",
            "users": "customers",
            "data_processes_natural_persons": True,
            "annex_iii_category": None,
            "performs_profiling": False,
            "article_5_practice": None,
            "article_6_1_safety_component": False,
            "article_6_3_carveout_applies": False,
            "interacts_with_natural_persons_directly": True,
            "is_general_purpose_ai_model": False,
            "training_compute_flops": None,
        },
        {
            "name": "Spam email filter",
            "intended_purpose": "Classify inbound email as spam or not",
            "users": "all_employees",
            "data_processes_natural_persons": False,
            "annex_iii_category": None,
            "performs_profiling": False,
            "article_5_practice": None,
            "article_6_1_safety_component": False,
            "article_6_3_carveout_applies": False,
            "interacts_with_natural_persons_directly": False,
            "is_general_purpose_ai_model": False,
            "training_compute_flops": None,
        },
        {
            "name": "Foundation model deployed via API",
            "intended_purpose": "General-purpose text generation",
            "users": "developers",
            "data_processes_natural_persons": True,
            "annex_iii_category": None,
            "performs_profiling": False,
            "article_5_practice": None,
            "article_6_1_safety_component": False,
            "article_6_3_carveout_applies": False,
            "interacts_with_natural_persons_directly": False,
            "is_general_purpose_ai_model": True,
            "training_compute_flops": 5e25,
        },
    ]
}


# Article 5 prohibited practices (per the binding regulation text)
ARTICLE_5_PRACTICES = {
    "subliminal_manipulation": "Article 5(1)(a) — Subliminal techniques beyond awareness causing harm",
    "exploitation_of_vulnerabilities": "Article 5(1)(b) — Exploiting vulnerabilities of age/disability/socioeconomic situation",
    "social_scoring": "Article 5(1)(c) — Social scoring by public authorities causing detrimental treatment",
    "predictive_policing_individual": "Article 5(1)(d) — Predictive policing based solely on profiling",
    "untargeted_facial_scraping": "Article 5(1)(e) — Untargeted scraping of facial images for facial recognition databases",
    "emotion_recognition_in_workplace_or_education": "Article 5(1)(f) — Emotion recognition in workplace and educational institutions",
    "biometric_categorisation_sensitive": "Article 5(1)(g) — Biometric categorisation by sensitive attributes",
    "real_time_remote_biometric_id_public_law_enforcement": "Article 5(1)(h) — Real-time remote biometric ID in publicly accessible spaces for law enforcement",
}

# Annex III high-risk categories (the 8 — Article 6(2))
ANNEX_III_CATEGORIES = {
    "biometrics": "Annex III §1 — Biometrics including biometric ID and categorisation",
    "critical_infrastructure": "Annex III §2 — Critical infrastructure (safety components)",
    "education": "Annex III §3 — Education and vocational training",
    "employment": "Annex III §4 — Employment, workers management, self-employment access",
    "essential_services": "Annex III §5 — Access to essential private/public services and benefits (including credit scoring, emergency dispatch, insurance pricing)",
    "law_enforcement": "Annex III §6 — Law enforcement",
    "migration_asylum": "Annex III §7 — Migration, asylum, border control",
    "justice_democratic_processes": "Annex III §8 — Administration of justice and democratic processes",
}


def classify(system: Dict[str, Any]) -> Dict[str, Any]:
    """Deterministic classification per Articles 5, 6, 50 + Annex III."""
    name = system.get("name", "<unnamed>")
    article_5 = system.get("article_5_practice")
    annex_iii = system.get("annex_iii_category")
    safety_component = system.get("article_6_1_safety_component", False)
    carveout = system.get("article_6_3_carveout_applies", False)
    profiling = system.get("performs_profiling", False)
    interacts = system.get("interacts_with_natural_persons_directly", False)
    is_gpai = system.get("is_general_purpose_ai_model", False)
    flops = system.get("training_compute_flops")

    # Step 1: Article 5 prohibitions (binary, no carve-out)
    if article_5 and article_5 in ARTICLE_5_PRACTICES:
        return {
            "name": name,
            "tier": "prohibited",
            "primary_citation": ARTICLE_5_PRACTICES[article_5],
            "rationale": "Listed Article 5 practice. Cannot be placed on EU market or used (penalty up to EUR 35M / 7% turnover).",
            "is_gpai": is_gpai,
            "gpai_systemic_risk": False,
        }

    # Step 2: Article 6(1) — safety component of regulated product per Annex I
    if safety_component:
        return {
            "name": name,
            "tier": "high_risk",
            "primary_citation": "Article 6(1) — Safety component of Annex I product",
            "rationale": "Safety component subject to third-party conformity assessment under sectoral law (Annex I).",
            "is_gpai": is_gpai,
            "gpai_systemic_risk": False,
        }

    # Step 3: Article 6(2) + Annex III — high-risk by category
    if annex_iii and annex_iii in ANNEX_III_CATEGORIES:
        # Article 6(3) carve-out check
        if carveout and not profiling:
            # Carve-out applies AND no profiling — drops to limited or minimal
            tier = "limited_risk" if interacts else "minimal_risk"
            return {
                "name": name,
                "tier": tier,
                "primary_citation": "Article 6(3) carve-out from Annex III — narrow procedural task / preparatory / human-result improvement",
                "rationale": "Annex III category triggered but Article 6(3) carve-out applies and no profiling.",
                "is_gpai": is_gpai,
                "gpai_systemic_risk": False,
            }
        if carveout and profiling:
            # Profiling overrides carve-out — Article 6(3) last sentence
            return {
                "name": name,
                "tier": "high_risk",
                "primary_citation": f"Article 6(2) + {ANNEX_III_CATEGORIES[annex_iii]}",
                "rationale": "Carve-out claimed but profiling of natural persons keeps it high-risk per Article 6(3) last sentence.",
                "is_gpai": is_gpai,
                "gpai_systemic_risk": False,
            }
        return {
            "name": name,
            "tier": "high_risk",
            "primary_citation": f"Article 6(2) + {ANNEX_III_CATEGORIES[annex_iii]}",
            "rationale": "Falls in Annex III high-risk category; no Article 6(3) carve-out applied.",
            "is_gpai": is_gpai,
            "gpai_systemic_risk": False,
        }

    # Step 4: Article 50 transparency (limited-risk)
    if interacts:
        return {
            "name": name,
            "tier": "limited_risk",
            "primary_citation": "Article 50(1) — Transparency for AI systems interacting with natural persons",
            "rationale": "Direct interaction with natural persons requires disclosure that they are interacting with AI.",
            "is_gpai": is_gpai,
            "gpai_systemic_risk": _gpai_systemic_risk(is_gpai, flops),
        }

    # Step 5: Default — minimal-risk
    return {
        "name": name,
        "tier": "minimal_risk",
        "primary_citation": "No Article 5, Annex III, or Article 50 trigger",
        "rationale": "Minimal-risk default. No obligations under the Act (Article 95 voluntary codes of conduct only).",
        "is_gpai": is_gpai,
        "gpai_systemic_risk": _gpai_systemic_risk(is_gpai, flops),
    }


def _gpai_systemic_risk(is_gpai: bool, flops: Optional[float]) -> bool:
    """Article 51 — systemic-risk GPAI threshold: training compute ≥ 10^25 FLOPs."""
    if not is_gpai or flops is None:
        return False
    return flops >= 1e25


def annotate_all(payload: Dict[str, Any]) -> Dict[str, Any]:
    classified = [classify(s) for s in payload.get("systems", [])]
    tier_counts: Dict[str, int] = {}
    for c in classified:
        tier_counts[c["tier"]] = tier_counts.get(c["tier"], 0) + 1
    gpai_systems = [c["name"] for c in classified if c["is_gpai"]]
    systemic_risk = [c["name"] for c in classified if c["gpai_systemic_risk"]]
    return {
        "total_systems": len(classified),
        "by_tier": tier_counts,
        "gpai_systems": gpai_systems,
        "gpai_systemic_risk_systems": systemic_risk,
        "systems": classified,
    }


def render_text(r: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("EU AI ACT (Reg. 2024/1689) — RISK CLASSIFICATION")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Total systems: {r['total_systems']}")
    lines.append(f"By tier: {r['by_tier']}")
    if r["gpai_systems"]:
        lines.append(f"GPAI systems: {', '.join(r['gpai_systems'])}")
    if r["gpai_systemic_risk_systems"]:
        lines.append(f"GPAI with systemic risk (Article 51): {', '.join(r['gpai_systemic_risk_systems'])}")
    lines.append("")
    lines.append("-" * 72)

    for s in r["systems"]:
        tier_label = s["tier"].replace("_", "-").upper()
        gpai_flag = "  [GPAI]" if s["is_gpai"] else ""
        sysrisk_flag = "  [SYSTEMIC RISK]" if s["gpai_systemic_risk"] else ""
        lines.append(f"  {s['name']}{gpai_flag}{sysrisk_flag}")
        lines.append(f"      Tier: {tier_label}")
        lines.append(f"      Citation: {s['primary_citation']}")
        lines.append(f"      Rationale: {s['rationale']}")
        lines.append("")

    lines.append("-" * 72)
    lines.append("DECISION ORDER: Article 5 prohibitions → Article 6(1) Annex I → Article 6(2) Annex III")
    lines.append("                → Article 6(3) carve-outs (overridden by profiling) → Article 50 transparency → minimal-risk default")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="EU AI Act risk tier classifier per Articles 5/6/50 + Annex III.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to systems JSON (uses embedded sample if omitted)")
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
        source = "<embedded sample: 5 systems across all 4 tiers + 1 GPAI>"

    result = annotate_all(payload)
    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))
    return 0


if __name__ == "__main__":
    sys.exit(main())
