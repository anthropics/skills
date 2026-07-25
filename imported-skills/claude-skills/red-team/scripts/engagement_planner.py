#!/usr/bin/env python3
"""
engagement_planner.py — Red Team Engagement Planner

Builds a structured red team engagement plan from target scope, MITRE ATT&CK
technique selection, access level, and crown jewel assets. Scores techniques
by detection risk and effort, assembles kill-chain phases, identifies choke
points, and generates OPSEC risk items.

IMPORTANT: Authorization is required. Use --authorized flag only after obtaining
signed Rules of Engagement (RoE) and written executive authorization.

Usage:
    python3 engagement_planner.py --techniques T1059,T1078,T1003 --access-level external --authorized --json
    python3 engagement_planner.py --techniques T1059,T1078 --crown-jewels "DB,AD" --access-level credentialed --authorized --json
    python3 engagement_planner.py --list-techniques

Exit codes:
    0  Engagement plan generated successfully
    1  Missing authorization or invalid input
    2  Scope violation or technique outside access-level constraints
"""

import argparse
import json
import sys

MITRE_TECHNIQUES = {
    "T1059": {"name": "Command and Scripting Interpreter", "tactic": "execution",
               "detection_risk": 0.7, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1059.001": {"name": "PowerShell", "tactic": "execution",
                   "detection_risk": 0.8, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1078": {"name": "Valid Accounts", "tactic": "initial_access",
               "detection_risk": 0.3, "prerequisites": [], "access_level": "external"},
    "T1078.004": {"name": "Valid Accounts: Cloud Accounts", "tactic": "initial_access",
                   "detection_risk": 0.3, "prerequisites": [], "access_level": "external"},
    "T1003": {"name": "OS Credential Dumping", "tactic": "credential_access",
               "detection_risk": 0.9, "prerequisites": ["initial_access", "privilege_escalation"], "access_level": "internal"},
    "T1003.001": {"name": "LSASS Memory", "tactic": "credential_access",
                   "detection_risk": 0.95, "prerequisites": ["initial_access", "privilege_escalation"], "access_level": "credentialed"},
    "T1021": {"name": "Remote Services", "tactic": "lateral_movement",
               "detection_risk": 0.6, "prerequisites": ["initial_access", "credential_access"], "access_level": "internal"},
    "T1021.002": {"name": "SMB/Windows Admin Shares", "tactic": "lateral_movement",
                   "detection_risk": 0.7, "prerequisites": ["initial_access", "credential_access"], "access_level": "internal"},
    "T1055": {"name": "Process Injection", "tactic": "defense_evasion",
               "detection_risk": 0.85, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1190": {"name": "Exploit Public-Facing Application", "tactic": "initial_access",
               "detection_risk": 0.5, "prerequisites": [], "access_level": "external"},
    "T1566": {"name": "Phishing", "tactic": "initial_access",
               "detection_risk": 0.4, "prerequisites": [], "access_level": "external"},
    "T1566.001": {"name": "Spearphishing Attachment", "tactic": "initial_access",
                   "detection_risk": 0.5, "prerequisites": [], "access_level": "external"},
    "T1098": {"name": "Account Manipulation", "tactic": "persistence",
               "detection_risk": 0.6, "prerequisites": ["initial_access", "privilege_escalation"], "access_level": "credentialed"},
    "T1136": {"name": "Create Account", "tactic": "persistence",
               "detection_risk": 0.7, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1053": {"name": "Scheduled Task/Job", "tactic": "persistence",
               "detection_risk": 0.6, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1486": {"name": "Data Encrypted for Impact", "tactic": "impact",
               "detection_risk": 0.99, "prerequisites": ["initial_access", "lateral_movement"], "access_level": "credentialed"},
    "T1530": {"name": "Data from Cloud Storage", "tactic": "collection",
               "detection_risk": 0.4, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1041": {"name": "Exfiltration Over C2 Channel", "tactic": "exfiltration",
               "detection_risk": 0.65, "prerequisites": ["initial_access", "collection"], "access_level": "internal"},
    "T1048": {"name": "Exfiltration Over Alternative Protocol", "tactic": "exfiltration",
               "detection_risk": 0.5, "prerequisites": ["initial_access", "collection"], "access_level": "internal"},
    "T1083": {"name": "File and Directory Discovery", "tactic": "discovery",
               "detection_risk": 0.3, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1082": {"name": "System Information Discovery", "tactic": "discovery",
               "detection_risk": 0.2, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1057": {"name": "Process Discovery", "tactic": "discovery",
               "detection_risk": 0.25, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1068": {"name": "Exploitation for Privilege Escalation", "tactic": "privilege_escalation",
               "detection_risk": 0.8, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1484": {"name": "Domain Policy Modification", "tactic": "privilege_escalation",
               "detection_risk": 0.85, "prerequisites": ["initial_access", "privilege_escalation"], "access_level": "credentialed"},
    "T1562": {"name": "Impair Defenses", "tactic": "defense_evasion",
               "detection_risk": 0.9, "prerequisites": ["initial_access", "privilege_escalation"], "access_level": "credentialed"},
    "T1070": {"name": "Indicator Removal", "tactic": "defense_evasion",
               "detection_risk": 0.75, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1195": {"name": "Supply Chain Compromise", "tactic": "initial_access",
               "detection_risk": 0.2, "prerequisites": [], "access_level": "external"},
    "T1218": {"name": "System Binary Proxy Execution", "tactic": "defense_evasion",
               "detection_risk": 0.6, "prerequisites": ["initial_access"], "access_level": "internal"},
    "T1105": {"name": "Ingress Tool Transfer", "tactic": "command_and_control",
               "detection_risk": 0.55, "prerequisites": ["initial_access"], "access_level": "internal"},
}

ACCESS_LEVEL_HIERARCHY = {"external": 0, "internal": 1, "credentialed": 2}

OPSEC_RISKS = [
    {"risk": "C2 beacon interval too frequent", "severity": "high",
     "mitigation": "Use jitter (25-50%) on beacon intervals; minimum 30s base interval for stealth",
     "relevant_tactics": ["command_and_control"]},
    {"risk": "Infrastructure reuse across engagements", "severity": "critical",
     "mitigation": "Provision fresh C2 infrastructure per engagement; never reuse domains or IPs",
     "relevant_tactics": ["command_and_control", "initial_access"]},
    {"risk": "Scanning during business hours from non-business IP", "severity": "medium",
     "mitigation": "Schedule active scanning to match target business hours and geographic timezone",
     "relevant_tactics": ["discovery"]},
    {"risk": "Known tool signatures in memory or on disk", "severity": "high",
     "mitigation": "Use custom-compiled tools or obfuscated variants; avoid default Cobalt Strike profiles",
     "relevant_tactics": ["execution", "lateral_movement"]},
    {"risk": "Credential dumping without EDR bypass", "severity": "critical",
     "mitigation": "Assess EDR coverage before credential dumping; use protected-mode aware approaches",
     "relevant_tactics": ["credential_access"]},
    {"risk": "Large data transfer without staging", "severity": "high",
     "mitigation": "Stage data locally, compress and encrypt before exfil; avoid single large transfers",
     "relevant_tactics": ["exfiltration", "collection"]},
    {"risk": "Operating outside authorized time window", "severity": "critical",
     "mitigation": "Confirm maintenance and testing windows with client before operational phases",
     "relevant_tactics": []},
    {"risk": "Leaving artifacts in temp directories", "severity": "medium",
     "mitigation": "Clean up all dropped files and created accounts before disengaging",
     "relevant_tactics": ["execution", "persistence"]},
]

KILL_CHAIN_PHASE_ORDER = [
    "initial_access", "execution", "persistence", "privilege_escalation",
    "defense_evasion", "credential_access", "discovery", "lateral_movement",
    "collection", "command_and_control", "exfiltration", "impact"
]


def list_techniques():
    """Print a formatted table of all MITRE techniques and exit."""
    print(f"{'ID':<12} {'Name':<45} {'Tactic':<25} {'Det.Risk':<10} {'Access'}")
    print("-" * 110)
    for tid, data in sorted(MITRE_TECHNIQUES.items()):
        print(
            f"{tid:<12} {data['name']:<45} {data['tactic']:<25} "
            f"{data['detection_risk']:<10.2f} {data['access_level']}"
        )
    sys.exit(0)


def build_engagement_plan(techniques_input, access_level, crown_jewels, target_count):
    """
    Core planning algorithm. Returns (plan_dict, scope_violations_count).
    """
    provided_level = ACCESS_LEVEL_HIERARCHY[access_level]
    valid_techniques = []
    scope_violations = []
    not_found = []

    for tid in techniques_input:
        tid = tid.strip().upper()
        if tid not in MITRE_TECHNIQUES:
            not_found.append(tid)
            continue
        tech = MITRE_TECHNIQUES[tid]
        required_level = ACCESS_LEVEL_HIERARCHY[tech["access_level"]]
        if required_level > provided_level:
            scope_violations.append({
                "technique_id": tid,
                "technique_name": tech["name"],
                "reason": (
                    f"Requires '{tech['access_level']}' access; "
                    f"provided access level is '{access_level}'"
                ),
            })
            continue
        effort_score = round(tech["detection_risk"] * (len(tech["prerequisites"]) + 1), 4)
        valid_techniques.append({
            "id": tid,
            "name": tech["name"],
            "tactic": tech["tactic"],
            "detection_risk": tech["detection_risk"],
            "prerequisites": tech["prerequisites"],
            "effort_score": effort_score,
        })

    # Group by tactic and order phases by kill chain
    tactic_map = {}
    for t in valid_techniques:
        tactic_map.setdefault(t["tactic"], []).append(t)

    phases = []
    tactics_present = set(tactic_map.keys())
    for phase_name in KILL_CHAIN_PHASE_ORDER:
        if phase_name in tactic_map:
            techniques_in_phase = sorted(
                tactic_map[phase_name], key=lambda x: x["effort_score"], reverse=True
            )
            phases.append({
                "phase": phase_name,
                "techniques": techniques_in_phase,
            })

    # Identify choke points
    # A choke point is a credential_access or privilege_escalation technique
    # that other selected techniques list as a prerequisite dependency,
    # especially relevant when crown jewels are specified.
    choke_tactic_set = {"credential_access", "privilege_escalation"}
    choke_points = []
    for t in valid_techniques:
        if t["tactic"] not in choke_tactic_set:
            continue
        # Count how many other techniques depend on this tactic
        dependents = [
            other["id"]
            for other in valid_techniques
            if t["tactic"] in other["prerequisites"] and other["id"] != t["id"]
        ]
        # If crown jewels are specified, flag anything in those choke tactics
        crown_jewel_relevant = bool(crown_jewels)
        if dependents or crown_jewel_relevant:
            choke_points.append({
                "technique_id": t["id"],
                "technique_name": t["name"],
                "tactic": t["tactic"],
                "dependent_technique_count": len(dependents),
                "dependent_techniques": dependents,
                "crown_jewel_relevant": crown_jewel_relevant,
                "note": (
                    "Blocking this technique disrupts the downstream kill-chain. "
                    "Priority hardening target."
                ),
            })

    # Collect OPSEC risks for tactics present in the selected techniques
    seen_risks = set()
    applicable_opsec = []
    for risk_item in OPSEC_RISKS:
        relevant = risk_item["relevant_tactics"]
        # Include universal risks (empty relevant_tactics list) always
        if not relevant or tactics_present.intersection(relevant):
            key = risk_item["risk"]
            if key not in seen_risks:
                seen_risks.add(key)
                applicable_opsec.append(risk_item)

    # Estimate duration: sum detection_risk * 2 days per phase, minimum 3 days
    raw_duration = sum(
        tech["detection_risk"] * 2
        for t in valid_techniques
        for tech in [t]  # flatten
    )
    # Per-phase minimum: ensure at least 0.5 day per phase
    phase_count = len(phases)
    estimated_days = max(3.0, round(raw_duration + phase_count * 0.5, 1))

    # Scale by target_count (each additional target adds 20% duration)
    if target_count and target_count > 1:
        estimated_days = round(estimated_days * (1 + (target_count - 1) * 0.2), 1)

    # Required authorizations list
    required_authorizations = [
        "Signed Rules of Engagement (RoE) document",
        "Written executive/CISO authorization",
        "Defined scope and out-of-scope assets list",
        "Emergency stop contact and escalation path",
        "Deconfliction process with SOC/Blue Team",
    ]
    if "impact" in tactics_present:
        required_authorizations.append(
            "Specific written authorization for destructive/impact techniques (T14xx)"
        )
    if "credential_access" in tactics_present:
        required_authorizations.append(
            "Written authorization for credential capture and handling procedures"
        )

    plan = {
        "engagement_summary": {
            "access_level": access_level,
            "crown_jewels": crown_jewels,
            "target_count": target_count or 1,
            "techniques_requested": len(techniques_input),
            "techniques_valid": len(valid_techniques),
            "techniques_not_found": not_found,
            "estimated_duration_days": estimated_days,
        },
        "phases": phases,
        "choke_points": choke_points,
        "opsec_risks": applicable_opsec,
        "scope_violations": scope_violations,
        "required_authorizations": required_authorizations,
    }
    return plan, len(scope_violations)


def main():
    parser = argparse.ArgumentParser(
        description="Red Team Engagement Planner — Builds structured engagement plans from MITRE ATT&CK techniques.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Examples:\n"
            "  python3 engagement_planner.py --techniques T1059,T1078,T1003 --access-level external --authorized --json\n"
            "  python3 engagement_planner.py --techniques T1059,T1078 --crown-jewels 'DB,AD' --access-level credentialed --authorized --json\n"
            "  python3 engagement_planner.py --list-techniques\n"
            "\nExit codes:\n"
            "  0  Engagement plan generated successfully\n"
            "  1  Missing authorization or invalid input\n"
            "  2  Scope violation or technique outside access-level constraints"
        ),
    )
    parser.add_argument(
        "--techniques",
        type=str,
        default="",
        help="Comma-separated MITRE ATT&CK technique IDs (e.g. T1059,T1078,T1003)",
    )
    parser.add_argument(
        "--access-level",
        choices=["external", "internal", "credentialed"],
        default="external",
        help="Attacker access level for this engagement (default: external)",
    )
    parser.add_argument(
        "--crown-jewels",
        type=str,
        default="",
        help="Comma-separated crown jewel asset labels (e.g. 'DB,AD,PaymentSystem')",
    )
    parser.add_argument(
        "--target-count",
        type=int,
        default=1,
        help="Number of target systems/segments (affects duration estimate, default: 1)",
    )
    parser.add_argument(
        "--authorized",
        action="store_true",
        help="Confirms signed RoE and executive authorization have been obtained",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="output_json",
        help="Output results as JSON",
    )
    parser.add_argument(
        "--list-techniques",
        action="store_true",
        help="Print all available MITRE techniques and exit",
    )

    args = parser.parse_args()

    if args.list_techniques:
        list_techniques()  # exits internally

    # Authorization gate
    if not args.authorized:
        msg = (
            "Authorization required: obtain signed RoE before planning. "
            "Use --authorized flag only after legal sign-off."
        )
        if args.output_json:
            print(json.dumps({"error": msg, "exit_code": 1}, indent=2))
        else:
            print(f"ERROR: {msg}", file=sys.stderr)
        sys.exit(1)

    if not args.techniques.strip():
        msg = "No techniques specified. Use --techniques T1059,T1078,... or --list-techniques."
        if args.output_json:
            print(json.dumps({"error": msg, "exit_code": 1}, indent=2))
        else:
            print(f"ERROR: {msg}", file=sys.stderr)
        sys.exit(1)

    techniques_input = [t.strip() for t in args.techniques.split(",") if t.strip()]
    crown_jewels = [c.strip() for c in args.crown_jewels.split(",") if c.strip()]

    plan, violation_count = build_engagement_plan(
        techniques_input=techniques_input,
        access_level=args.access_level,
        crown_jewels=crown_jewels,
        target_count=args.target_count,
    )

    if args.output_json:
        print(json.dumps(plan, indent=2))
    else:
        summary = plan["engagement_summary"]
        print("\n=== RED TEAM ENGAGEMENT PLAN ===")
        print(f"Access Level    : {summary['access_level']}")
        print(f"Crown Jewels    : {', '.join(crown_jewels) if crown_jewels else 'Not specified'}")
        print(f"Techniques      : {summary['techniques_valid']}/{summary['techniques_requested']} valid")
        print(f"Est. Duration   : {summary['estimated_duration_days']} days")
        if summary["techniques_not_found"]:
            print(f"Not Found       : {', '.join(summary['techniques_not_found'])}")

        print("\n--- Kill-Chain Phases ---")
        for phase in plan["phases"]:
            print(f"\n  [{phase['phase'].upper()}]")
            for t in phase["techniques"]:
                print(f"    {t['id']:<12} {t['name']:<45} risk={t['detection_risk']:.2f}  effort={t['effort_score']:.3f}")

        print("\n--- Choke Points ---")
        if plan["choke_points"]:
            for cp in plan["choke_points"]:
                print(f"  {cp['technique_id']} {cp['technique_name']} — {cp['note']}")
        else:
            print("  None identified.")

        print("\n--- OPSEC Risks ---")
        for risk in plan["opsec_risks"]:
            print(f"  [{risk['severity'].upper()}] {risk['risk']}")
            print(f"    Mitigation: {risk['mitigation']}")

        if plan["scope_violations"]:
            print("\n--- SCOPE VIOLATIONS ---")
            for sv in plan["scope_violations"]:
                print(f"  {sv['technique_id']}: {sv['reason']}")

        print("\n--- Required Authorizations ---")
        for auth in plan["required_authorizations"]:
            print(f"  - {auth}")
        print()

    if violation_count > 0:
        sys.exit(2)
    sys.exit(0)


if __name__ == "__main__":
    main()
