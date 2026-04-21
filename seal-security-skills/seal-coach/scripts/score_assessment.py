#!/usr/bin/env python3
"""
SEAL Readiness Assessment Scorer

Maps assessment answers to readiness bands per domain.
Run after coaching assessment to generate a summary.

Usage:
  python score_assessment.py --domain wallet-security --answers '{"multisig": true, "key_rotation": false}'
  python score_assessment.py --interactive

Bands: Critical | Developing | Established | Advanced
"""

import json
import sys
import argparse
from pathlib import Path

# Domain -> control checklist
# Each control: (name, weight)
DOMAIN_CHECKLISTS = {
    "wallet-security": [
        ("multisig_enabled", 3),
        ("hardware_wallets", 2),
        ("key_rotation", 2),
        ("transaction_limits", 1),
        ("key_inventory", 2),
        ("signing_audit", 1),
    ],
    "incident-management": [
        ("written_plan", 3),
        ("assigned_roles", 2),
        ("emergency_contacts", 2),
        ("tabletop_exercise", 2),
        ("detection_capability", 2),
        ("post_mortem_process", 1),
    ],
    "iam": [
        ("mfa_enabled", 3),
        ("individual_accounts", 3),
        ("offboarding_process", 2),
        ("access_reviews", 2),
        ("principle_of_least_privilege", 2),
    ],
    "devsecops": [
        ("security_linting", 2),
        ("secret_scanning", 3),
        ("code_review_security", 2),
        ("pinned_dependencies", 2),
        ("vuln_scanning", 2),
        ("security_gates", 1),
    ],
    "monitoring": [
        ("centralized_logs", 2),
        ("auth_anomaly_alerts", 2),
        ("transaction_alerts", 2),
        ("escalation_procedures", 2),
        ("credential_leak_monitoring", 1),
    ],
    "governance": [
        ("security_owner", 2),
        ("documented_policies", 2),
        ("regular_reviews", 2),
        ("risk_register", 1),
    ],
    "supply-chain": [
        ("dependency_audit", 2),
        ("lockfiles", 2),
        ("build_pipeline_review", 2),
        ("artifact_signing", 1),
    ],
    "awareness": [
        ("security_training", 2),
        ("phishing_defense", 2),
        ("reporting_culture", 2),
    ],
    "opsec": [
        ("separate_accounts", 2),
        ("encrypted_comms", 2),
        ("opsec_guidelines", 2),
    ],
    "encryption": [
        ("encryption_at_rest", 2),
        ("encryption_in_transit", 2),
        ("key_management", 3),
        ("disk_encryption", 1),
    ],
    "threat-modeling": [
        ("formal_threat_model", 2),
        ("attack_surface_mapping", 2),
        ("regular_review", 2),
    ],
}

BAND_THRESHOLDS = {
    "Critical": 0.0,
    "Developing": 0.4,
    "Established": 0.7,
    "Advanced": 0.9,
}


def score_domain(domain: str, answers: dict) -> dict:
    """Score a domain's readiness based on checklist answers."""
    checklist = DOMAIN_CHECKLISTS.get(domain)
    if not checklist:
        return {"error": f"Unknown domain: {domain}"}

    total_weight = sum(w for _, w in checklist)
    earned_weight = sum(w for control, w in checklist if answers.get(control, False))
    ratio = earned_weight / total_weight if total_weight > 0 else 0

    band = "Critical"
    for b, threshold in sorted(BAND_THRESHOLDS.items(), key=lambda x: x[1], reverse=True):
        if ratio >= threshold:
            band = b
            break

    gaps = [ctrl for ctrl, _ in checklist if not answers.get(ctrl, False)]

    return {
        "domain": domain,
        "score": round(ratio, 2),
        "band": band,
        "controls_met": len(checklist) - len(gaps),
        "controls_total": len(checklist),
        "gaps": gaps,
    }


def score_all(answers_by_domain: dict) -> dict:
    """Score multiple domains."""
    results = {}
    for domain, answers in answers_by_domain.items():
        results[domain] = score_domain(domain, answers)
    return results


def print_summary(results: dict):
    """Print a formatted readiness summary."""
    print("\n=== SEAL Readiness Summary ===\n")
    for domain, result in sorted(results.items(), key=lambda x: x[1].get("score", 0)):
        if "error" in result:
            print(f"  {domain}: ERROR - {result['error']}")
            continue
        bar = "#" * int(result["score"] * 20) + "-" * (20 - int(result["score"] * 20))
        print(f"  {domain:30s} [{bar}] {result['band']:12s} ({result['controls_met']}/{result['controls_total']})")
        if result["gaps"]:
            print(f"    Gaps: {', '.join(result['gaps'])}")

    # Priority recommendation
    critical = [d for d, r in results.items() if r.get("band") == "Critical"]
    developing = [d for d, r in results.items() if r.get("band") == "Developing"]
    if critical:
        print(f"\n  Priority: {', '.join(critical)} (highest risk)")
    elif developing:
        print(f"\n  Focus: {', '.join(developing[:3])} (quick wins available)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="SEAL Readiness Scorer")
    parser.add_argument("--domain", help="Single domain to score")
    parser.add_argument("--answers", help="JSON string of answers")
    parser.add_argument("--all", help="JSON file with all domain answers")
    args = parser.parse_args()

    if args.all:
        with open(args.all) as f:
            data = json.load(f)
        results = score_all(data)
        print_summary(results)
    elif args.domain and args.answers:
        answers = json.loads(args.answers)
        result = score_domain(args.domain, answers)
        print(json.dumps(result, indent=2))
    else:
        print("Usage:")
        print("  --domain wallet-security --answers '{\"multisig_enabled\": true}'")
        print("  --all answers.json")
