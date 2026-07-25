#!/usr/bin/env python3
"""ai_risk_classifier.py — Classify an AI use case under EU AI Act + US state laws.

Stdlib-only. Takes a use case profile and outputs:
  - Risk tier (PROHIBITED / HIGH / LIMITED / MINIMAL) under EU AI Act
  - US state law triggers (NYC LL 144, CO SB 21-169 successor, IL HB 53, CA SB 1001)
  - Industry-specific overlays (FDA, NYDFS, NAIC)
  - Required controls + conformity assessment trigger
  - Citations to specific articles / regulations

NOT legal advice — surfaces classification for qualified AI counsel.

Input schema (JSON):
{
  "use_case": "AI screening of job applications",
  "domain": "employment",                # employment | credit | education | healthcare | critical-infra |
                                          # law-enforcement | biometric | content-moderation | b2b-general |
                                          # consumer-general
  "deploys_in_eu": true,
  "deploys_in_us_states": ["NY", "CO", "IL", "CA"],
  "decisions_affected": "consequential", # consequential | informational | internal-only
  "automation_level": "automated",       # automated | human-in-loop | advisory
  "user_facing": true,
  "biometric_data_processed": false,
  "children_under_16": false
}

Usage:
    python ai_risk_classifier.py                       # uses embedded hiring-AI sample
    python ai_risk_classifier.py path/to/use_case.json
    python ai_risk_classifier.py use_case.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "use_case": "AI-assisted screening of job applications (resume ranking)",
    "domain": "employment",
    "deploys_in_eu": True,
    "deploys_in_us_states": ["NY", "CO", "IL", "CA"],
    "decisions_affected": "consequential",
    "automation_level": "automated",
    "user_facing": False,
    "biometric_data_processed": False,
    "children_under_16": False,
}


# EU AI Act Annex III "high-risk" domains (Article 6(2))
HIGH_RISK_DOMAINS = {
    "employment",
    "credit",
    "education",
    "critical-infra",
    "law-enforcement",
    "biometric",
    "migration",
    "justice",
    "essential-services",  # insurance, public benefits
}

# EU AI Act Article 5 prohibited practices
PROHIBITED_TRIGGERS = {
    "social-scoring",
    "real-time-biometric-surveillance",
    "subliminal-manipulation",
    "exploitation-of-vulnerability",
    "predictive-policing-from-profiling",
    "emotion-recognition-workplace-or-education",
    "biometric-categorization-by-protected-traits",
}


def classify_eu(profile: Dict[str, Any]) -> Dict[str, Any]:
    """Return EU AI Act classification + reasoning."""
    deploys_eu = profile.get("deploys_in_eu", False)
    if not deploys_eu:
        return {
            "tier": "NOT_APPLICABLE",
            "reasoning": "Does not deploy in EU. EU AI Act not triggered.",
            "obligations": [],
            "citations": [],
        }

    domain = profile.get("domain", "")
    decisions = profile.get("decisions_affected", "informational")
    biometric = profile.get("biometric_data_processed", False)
    automation = profile.get("automation_level", "advisory")
    use_case = profile.get("use_case", "").lower()

    # Article 5 prohibited check (heuristic match)
    for prohibited in PROHIBITED_TRIGGERS:
        if any(kw in use_case for kw in prohibited.split("-")):
            # Conservative: match only if multiple keywords hit
            keywords = prohibited.split("-")
            hits = sum(1 for kw in keywords if kw in use_case)
            if hits >= 2:
                return {
                    "tier": "PROHIBITED",
                    "reasoning": (
                        f"Use case description appears to match Article 5 prohibited practice ({prohibited}). "
                        "Cannot deploy in EU regardless of safeguards. Re-scope the product or exclude EU market."
                    ),
                    "obligations": ["Cease deployment in EU"],
                    "citations": ["EU AI Act Art. 5"],
                }

    # Special prohibited: biometric in public spaces by law enforcement (real-time)
    if biometric and domain == "law-enforcement" and automation == "automated":
        return {
            "tier": "PROHIBITED",
            "reasoning": (
                "Real-time biometric identification by law enforcement in publicly accessible spaces is "
                "Art. 5(1)(h) prohibited (narrow exceptions for serious crimes only)."
            ),
            "obligations": ["Cease deployment unless narrow exception applies, in which case Annex III high-risk obligations also apply"],
            "citations": ["EU AI Act Art. 5(1)(h)"],
        }

    # High-risk Annex III check
    if domain in HIGH_RISK_DOMAINS and decisions == "consequential":
        return {
            "tier": "HIGH",
            "reasoning": (
                f"Annex III high-risk domain ({domain}) with consequential decisions. "
                "Conformity assessment + registration + post-market monitoring required before deployment."
            ),
            "obligations": [
                "Conformity assessment (Art. 43)",
                "Registration in EU AI database (Art. 49)",
                "Risk management system (Art. 9)",
                "Data governance: representative, accurate, complete training data (Art. 10)",
                "Technical documentation maintained throughout lifecycle (Art. 11)",
                "Logging / record-keeping (Art. 12)",
                "Transparency and instructions for use (Art. 13)",
                "Human oversight (Art. 14)",
                "Accuracy, robustness, cybersecurity (Art. 15)",
                "Post-market monitoring + incident reporting (Art. 72)",
            ],
            "citations": ["EU AI Act Art. 6", "Annex III", "Art. 8-15", "Art. 43", "Art. 49", "Art. 72"],
        }

    # Biometric data: special category — usually high-risk
    if biometric:
        return {
            "tier": "HIGH",
            "reasoning": (
                "Biometric data processing triggers Annex III obligations even outside the listed domains "
                "(special category under GDPR Art. 9 + AI Act overlay)."
            ),
            "obligations": [
                "Conformity assessment + Annex III high-risk obligations",
                "GDPR Art. 9(2) explicit consent or other Art. 9 lawful basis",
                "DPIA mandatory (GDPR Art. 35)",
            ],
            "citations": ["EU AI Act Annex III §1", "GDPR Art. 9", "GDPR Art. 35"],
        }

    # Limited risk: chatbots, deepfakes, emotion recognition (outside workplace/edu), generative AI
    if "chatbot" in use_case or "deepfake" in use_case or "image generation" in use_case or "video generation" in use_case:
        return {
            "tier": "LIMITED",
            "reasoning": (
                "Limited risk: transparency obligations apply — users must be informed they are interacting with AI "
                "or that content is AI-generated."
            ),
            "obligations": [
                "Inform users they are interacting with AI (Art. 50(1))",
                "Mark AI-generated / manipulated content (Art. 50(2))",
                "If general-purpose AI model: model card with capabilities, limitations, training-data summary (Art. 53)",
            ],
            "citations": ["EU AI Act Art. 50", "Art. 53"],
        }

    # Minimal risk default
    return {
        "tier": "MINIMAL",
        "reasoning": (
            "Does not fall under prohibited, Annex III high-risk, or limited-risk categories. "
            "No specific AI Act obligations beyond general product safety; voluntary codes of conduct recommended."
        ),
        "obligations": [
            "Voluntary alignment with NIST AI RMF / EU codes of conduct (recommended)",
            "GDPR obligations still apply if personal data is processed",
        ],
        "citations": ["EU AI Act recital 27", "NIST AI RMF 1.0"],
    }


def us_state_triggers(profile: Dict[str, Any]) -> List[Dict[str, str]]:
    """Return list of triggered US state-level obligations."""
    states = set(s.upper() for s in profile.get("deploys_in_us_states", []))
    domain = profile.get("domain", "")
    user_facing = profile.get("user_facing", False)
    triggers = []

    # NYC LL 144 — AEDTs in employment
    if "NY" in states and domain == "employment":
        triggers.append({
            "law": "NYC Local Law 144 (AEDT)",
            "trigger": "Automated Employment Decision Tool used in hiring or promotion for NYC employees",
            "obligations": (
                "Annual independent bias audit; candidate notice (10+ business days before use); "
                "publication of audit summary on company website."
            ),
            "citation": "NYC Local Law 144 of 2021; 6 RCNY § 5-300",
        })

    # Colorado AI Act / SB 21-169 successor
    if "CO" in states and domain in {"employment", "credit", "education", "insurance", "essential-services"}:
        triggers.append({
            "law": "Colorado AI Act (SB 21-169 / 2024 amendments)",
            "trigger": f"High-risk AI system in consumer decisions ({domain})",
            "obligations": (
                "Reasonable care to protect from algorithmic discrimination; impact assessment; "
                "consumer notice; right to opt-out of profiling; risk management policy."
            ),
            "citation": "Colorado SB 21-169 (as amended)",
        })

    # Illinois HB 53 — AI in employment interviews
    if "IL" in states and domain == "employment":
        triggers.append({
            "law": "Illinois HB 53 (AI Video Interview Act)",
            "trigger": "AI analyzes video interviews of Illinois applicants",
            "obligations": (
                "Candidate notice + consent before recording; explanation of how AI is used; "
                "deletion within 30 days of request; restrictions on sharing data."
            ),
            "citation": "Illinois 820 ILCS 42/",
        })

    # California SB 1001 — Bot disclosure
    if "CA" in states and user_facing:
        triggers.append({
            "law": "California SB 1001 (B.O.T. Act)",
            "trigger": "User-facing AI bot in commercial transactions or California elections",
            "obligations": "Disclose to user that they are interacting with a bot (not a human).",
            "citation": "California Business & Professions Code § 17940",
        })

    # Illinois BIPA — biometric data
    if "IL" in states and profile.get("biometric_data_processed", False):
        triggers.append({
            "law": "Illinois Biometric Information Privacy Act (BIPA)",
            "trigger": "Biometric identifier or biometric information capture",
            "obligations": (
                "Written informed consent; published retention/destruction policy; cannot sell biometric data; "
                "private right of action with statutory damages ($1K-$5K per violation)."
            ),
            "citation": "Illinois 740 ILCS 14/",
        })

    return triggers


def industry_overlays(profile: Dict[str, Any]) -> List[Dict[str, str]]:
    """Return industry-specific regulatory overlays."""
    domain = profile.get("domain", "")
    overlays = []

    if domain == "healthcare":
        overlays.append({
            "framework": "FDA AI/ML guidance + Software as Medical Device (SaMD)",
            "trigger": "AI in clinical decisions, diagnostic, or therapeutic use",
            "obligations": (
                "510(k) or De Novo or PMA pathway depending on risk class; Predetermined Change Control Plan "
                "for adaptive models; Good Machine Learning Practices (GMLP)."
            ),
            "citation": "FDA Guidance on AI/ML SaMD (2023); 21 CFR Part 820",
        })
    elif domain == "credit":
        overlays.append({
            "framework": "ECOA + FCRA + CFPB Circular 2023-03",
            "trigger": "AI used in credit underwriting or adverse action",
            "obligations": (
                "Specific reason for adverse action (not 'algorithm said no'); model risk management "
                "consistent with SR 11-7 if a bank; explainability sufficient for FCRA adverse action notice."
            ),
            "citation": "15 USC §1691 (ECOA); CFPB Circular 2023-03; Fed SR 11-7",
        })
    elif domain == "essential-services":
        overlays.append({
            "framework": "NAIC Model Bulletin on AI in Insurance",
            "trigger": "AI in insurance underwriting, pricing, claims, fraud",
            "obligations": (
                "AI program governance, risk management, third-party AI oversight; "
                "documented testing for unfair discrimination."
            ),
            "citation": "NAIC Model Bulletin on the Use of AI by Insurers (2023)",
        })

    return overlays


def required_controls(profile: Dict[str, Any], eu_classification: Dict[str, Any]) -> List[str]:
    """Return the required-controls checklist based on tier + profile."""
    tier = eu_classification.get("tier", "")
    controls = []

    if tier in ("HIGH", "LIMITED", "MINIMAL"):
        controls.extend([
            "Eval set with documented success criteria before deployment",
            "Monitoring of model output in production (drift, bias, hallucination)",
            "Fallback behavior defined for model failure modes",
            "Human-in-loop review for high-stakes outputs",
        ])

    if tier == "HIGH":
        controls.extend([
            "Conformity assessment completed and documented (EU AI Act Art. 43)",
            "Registration in EU AI database before deployment (Art. 49)",
            "Risk management system documented and maintained (Art. 9)",
            "Training data governance: representativeness, accuracy, bias mitigation (Art. 10)",
            "Technical documentation per Annex IV maintained throughout lifecycle (Art. 11)",
            "Comprehensive logging for traceability (Art. 12)",
            "Human oversight design (e.g., stop button, override capability) (Art. 14)",
            "Post-market monitoring plan + serious incident reporting (Art. 72)",
            "DPIA under GDPR Art. 35 if personal data processed",
        ])

    if tier == "LIMITED":
        controls.extend([
            "User notification: 'You are interacting with AI' or 'This content is AI-generated'",
            "If general-purpose model: publish model card per Art. 53",
        ])

    if profile.get("user_facing"):
        controls.append("Public-facing disclosure of AI usage in customer-facing communications")

    if profile.get("automation_level") == "automated" and profile.get("decisions_affected") == "consequential":
        controls.append("Right-to-explanation / contestation mechanism for affected individuals (GDPR Art. 22)")

    return controls


def analyze(profile: Dict[str, Any]) -> Dict[str, Any]:
    eu = classify_eu(profile)
    us = us_state_triggers(profile)
    overlays = industry_overlays(profile)
    controls = required_controls(profile, eu)

    conformity_required = eu.get("tier") == "HIGH"

    return {
        "eu_classification": eu,
        "us_state_triggers": us,
        "industry_overlays": overlays,
        "required_controls": controls,
        "conformity_assessment_required": conformity_required,
    }


def render_text(result: Dict[str, Any], profile: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("AI RISK CLASSIFICATION")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Use case: {profile.get('use_case')}")
    lines.append(f"  Domain: {profile.get('domain')} | Automation: {profile.get('automation_level')} | Decisions: {profile.get('decisions_affected')}")
    lines.append(f"  Deploys in EU: {profile.get('deploys_in_eu')} | US states: {', '.join(profile.get('deploys_in_us_states', []))}")
    lines.append(f"  User-facing: {profile.get('user_facing')} | Biometric: {profile.get('biometric_data_processed')}")
    lines.append("")
    lines.append("-" * 72)
    eu = result["eu_classification"]
    tier_marker = {
        "PROHIBITED": "🔴",
        "HIGH": "🟠",
        "LIMITED": "🟡",
        "MINIMAL": "🟢",
        "NOT_APPLICABLE": "⚪",
    }.get(eu["tier"], "•")
    lines.append(f"EU AI ACT TIER: {tier_marker} {eu['tier']}")
    lines.append("")
    for line in _wrap(eu["reasoning"], 2):
        lines.append(line)
    lines.append("")
    if eu["citations"]:
        lines.append(f"  Citations: {', '.join(eu['citations'])}")
        lines.append("")
    if eu["obligations"]:
        lines.append("  EU obligations:")
        for o in eu["obligations"]:
            lines.append(f"    • {o}")
        lines.append("")
    lines.append("-" * 72)

    lines.append(f"CONFORMITY ASSESSMENT REQUIRED: {'YES' if result['conformity_assessment_required'] else 'no'}")
    lines.append("")
    lines.append("-" * 72)

    us = result["us_state_triggers"]
    if us:
        lines.append(f"US STATE LAW TRIGGERS ({len(us)}):")
        lines.append("")
        for t in us:
            lines.append(f"  • {t['law']}")
            lines.append(f"    Trigger: {t['trigger']}")
            for line in _wrap(t["obligations"], 4):
                lines.append(line)
            lines.append(f"    Citation: {t['citation']}")
            lines.append("")
    else:
        lines.append("US STATE LAW TRIGGERS: none for the listed states + domain.")
        lines.append("")
    lines.append("-" * 72)

    overlays = result["industry_overlays"]
    if overlays:
        lines.append(f"INDUSTRY OVERLAYS ({len(overlays)}):")
        lines.append("")
        for o in overlays:
            lines.append(f"  • {o['framework']}")
            lines.append(f"    Trigger: {o['trigger']}")
            for line in _wrap(o["obligations"], 4):
                lines.append(line)
            lines.append(f"    Citation: {o['citation']}")
            lines.append("")
        lines.append("-" * 72)

    lines.append(f"REQUIRED CONTROLS ({len(result['required_controls'])}):")
    for c in result["required_controls"]:
        lines.append(f"  ☐ {c}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("REMINDER: This is triage, not legal advice. EU AI Act conformity assessment requires qualified")
    lines.append("AI counsel and may require Notified Body involvement. Re-run quarterly as regulations evolve.")
    return "\n".join(lines)


def _wrap(text: str, indent: int, width: int = 70) -> List[str]:
    import textwrap
    return textwrap.wrap(text, width=width, initial_indent=" " * indent, subsequent_indent=" " * indent) or [" " * indent + text]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Classify an AI use case under EU AI Act + US state laws.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to use_case JSON (uses embedded sample if omitted)")
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
        source = "<embedded sample: AI hiring screening, EU + NY/CO/IL/CA>"

    result = analyze(profile)

    if args.output == "json":
        print(json.dumps({"source": source, "profile": profile, **result}, indent=2))
    else:
        print(render_text(result, profile, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
