#!/usr/bin/env python3
"""
HIPAA Risk Assessment Tool

Evaluates HIPAA compliance for medical device software and connected devices
by analyzing code and documentation for security safeguards.

Usage:
    python hipaa_risk_assessment.py <project_dir>
    python hipaa_risk_assessment.py <project_dir> --category technical
    python hipaa_risk_assessment.py <project_dir> --json
"""

import argparse
import json
import os
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple


# HIPAA Security Rule safeguards
HIPAA_SAFEGUARDS = {
    "administrative": {
        "title": "Administrative Safeguards (§164.308)",
        "controls": {
            "security_management": {
                "title": "Security Management Process",
                "requirement": "Risk analysis, risk management, sanction policy",
                "doc_patterns": ["risk_assessment*", "security_policy*", "sanction*"],
                "code_patterns": [],
                "weight": 10
            },
            "security_officer": {
                "title": "Assigned Security Responsibility",
                "requirement": "Designated security official",
                "doc_patterns": ["security_officer*", "hipaa_officer*", "privacy_officer*"],
                "code_patterns": [],
                "weight": 5
            },
            "workforce_security": {
                "title": "Workforce Security",
                "requirement": "Authorization/supervision, clearance, termination procedures",
                "doc_patterns": ["access_control*", "termination*", "hr_security*"],
                "code_patterns": [],
                "weight": 5
            },
            "access_management": {
                "title": "Information Access Management",
                "requirement": "Access authorization, establishment, modification",
                "doc_patterns": ["access_management*", "role_definition*", "access_control*"],
                "code_patterns": [r"role.*based", r"permission", r"authorization"],
                "weight": 8
            },
            "security_training": {
                "title": "Security Awareness and Training",
                "requirement": "Training program, security reminders",
                "doc_patterns": ["training*", "security_awareness*"],
                "code_patterns": [],
                "weight": 5
            },
            "incident_procedures": {
                "title": "Security Incident Procedures",
                "requirement": "Incident response and reporting",
                "doc_patterns": ["incident*", "breach*", "security_event*"],
                "code_patterns": [r"incident.*report", r"security.*alert", r"breach.*notify"],
                "weight": 8
            },
            "contingency_plan": {
                "title": "Contingency Plan",
                "requirement": "Backup, disaster recovery, emergency mode",
                "doc_patterns": ["contingency*", "disaster_recovery*", "backup*", "dr_plan*"],
                "code_patterns": [r"backup", r"recovery", r"failover"],
                "weight": 8
            },
            "evaluation": {
                "title": "Evaluation",
                "requirement": "Periodic security evaluations",
                "doc_patterns": ["security_audit*", "hipaa_audit*", "compliance_review*"],
                "code_patterns": [],
                "weight": 5
            },
            "baa": {
                "title": "Business Associate Contracts",
                "requirement": "Written contracts with business associates",
                "doc_patterns": ["baa*", "business_associate*", "vendor_agreement*"],
                "code_patterns": [],
                "weight": 5
            }
        }
    },
    "physical": {
        "title": "Physical Safeguards (§164.310)",
        "controls": {
            "facility_access": {
                "title": "Facility Access Controls",
                "requirement": "Physical access procedures and controls",
                "doc_patterns": ["facility_access*", "physical_security*", "access_control*"],
                "code_patterns": [],
                "weight": 5
            },
            "workstation_use": {
                "title": "Workstation Use",
                "requirement": "Policies for workstation use and security",
                "doc_patterns": ["workstation*", "endpoint*", "device_policy*"],
                "code_patterns": [],
                "weight": 3
            },
            "device_media": {
                "title": "Device and Media Controls",
                "requirement": "Disposal, media re-use, accountability",
                "doc_patterns": ["media_disposal*", "device_disposal*", "data_sanitization*"],
                "code_patterns": [r"secure.*delete", r"wipe", r"sanitize"],
                "weight": 5
            }
        }
    },
    "technical": {
        "title": "Technical Safeguards (§164.312)",
        "controls": {
            "access_control": {
                "title": "Access Control",
                "requirement": "Unique user ID, emergency access, auto logoff, encryption",
                "doc_patterns": ["access_control*", "authentication*", "session*"],
                "code_patterns": [
                    r"authentication",
                    r"authorize",
                    r"session.*timeout",
                    r"auto.*logout",
                    r"unique.*id",
                    r"user.*id"
                ],
                "weight": 10
            },
            "audit_controls": {
                "title": "Audit Controls",
                "requirement": "Record and examine activity in systems with ePHI",
                "doc_patterns": ["audit_log*", "access_log*", "security_log*"],
                "code_patterns": [
                    r"audit.*log",
                    r"access.*log",
                    r"log.*access",
                    r"security.*event",
                    r"logger"
                ],
                "weight": 10
            },
            "integrity": {
                "title": "Integrity Controls",
                "requirement": "Mechanism to authenticate ePHI",
                "doc_patterns": ["data_integrity*", "checksum*", "hash*"],
                "code_patterns": [
                    r"checksum",
                    r"hash",
                    r"hmac",
                    r"integrity.*check",
                    r"digital.*signature"
                ],
                "weight": 8
            },
            "authentication": {
                "title": "Person or Entity Authentication",
                "requirement": "Verify identity of person or entity seeking access",
                "doc_patterns": ["authentication*", "identity*", "mfa*", "2fa*"],
                "code_patterns": [
                    r"authenticate",
                    r"mfa",
                    r"two.*factor",
                    r"2fa",
                    r"multi.*factor",
                    r"oauth",
                    r"jwt"
                ],
                "weight": 10
            },
            "transmission_security": {
                "title": "Transmission Security",
                "requirement": "Encryption during transmission",
                "doc_patterns": ["encryption*", "tls*", "ssl*", "transport_security*"],
                "code_patterns": [
                    r"https",
                    r"tls",
                    r"ssl",
                    r"encrypt.*transit",
                    r"secure.*connection"
                ],
                "weight": 10
            }
        }
    }
}

# PHI data patterns to detect in code
PHI_PATTERNS = [
    (r"patient.*name", "Patient Name"),
    (r"ssn|social.*security", "Social Security Number"),
    (r"date.*of.*birth|dob", "Date of Birth"),
    (r"medical.*record", "Medical Record Number"),
    (r"health.*plan", "Health Plan ID"),
    (r"diagnosis|icd.*code", "Diagnosis/ICD Code"),
    (r"prescription|medication", "Medication/Prescription"),
    (r"insurance", "Insurance Information"),
    (r"phone.*number|telephone", "Phone Number"),
    (r"email.*address", "Email Address"),
    (r"address|street|city|zip", "Physical Address"),
    (r"biometric", "Biometric Data")
]

# Security vulnerability patterns (dynamic code execution, hardcoded secrets)
VULNERABILITY_PATTERNS = [
    (r"password.*=.*['\"]", "Hardcoded password"),
    (r"api.*key.*=.*['\"]", "Hardcoded API key"),
    (r"secret.*=.*['\"]", "Hardcoded secret"),
    (r"http://(?!localhost)", "Unencrypted HTTP connection"),
    (r"verify.*=.*False", "SSL verification disabled"),
    (r"dynamic.*code.*execution", "Dynamic code execution risk"),
    (r"disable.*ssl", "SSL disabled"),
    (r"insecure", "Insecure configuration")
]


def scan_documentation(project_dir: Path, patterns: List[str]) -> List[str]:
    """Scan for documentation matching patterns."""
    found = []
    doc_dirs = [
        project_dir / "docs",
        project_dir / "documentation",
        project_dir / "policies",
        project_dir / "compliance",
        project_dir / "hipaa",
        project_dir
    ]

    for doc_dir in doc_dirs:
        if not doc_dir.exists():
            continue

        for pattern in patterns:
            for ext in ["*.md", "*.pdf", "*.docx", "*.doc", "*.txt"]:
                try:
                    for match in doc_dir.glob(f"**/{pattern}{ext}"):
                        rel_path = str(match.relative_to(project_dir))
                        if rel_path not in found:
                            found.append(rel_path)
                except Exception:
                    continue

    return found


def scan_code_patterns(project_dir: Path, patterns: List[str]) -> List[Dict]:
    """Scan source code for patterns."""
    matches = []
    code_extensions = ["*.py", "*.js", "*.ts", "*.java", "*.cs", "*.go", "*.rb"]

    src_dirs = [
        project_dir / "src",
        project_dir / "app",
        project_dir / "lib",
        project_dir
    ]

    for src_dir in src_dirs:
        if not src_dir.exists():
            continue

        for ext in code_extensions:
            try:
                for file_path in src_dir.glob(f"**/{ext}"):
                    # Skip node_modules, venv, etc.
                    if any(skip in str(file_path) for skip in ["node_modules", "venv", ".venv", "__pycache__", ".git"]):
                        continue

                    try:
                        content = file_path.read_text(encoding='utf-8', errors='ignore')
                        for pattern in patterns:
                            if re.search(pattern, content, re.IGNORECASE):
                                rel_path = str(file_path.relative_to(project_dir))
                                matches.append({
                                    "file": rel_path,
                                    "pattern": pattern
                                })
                                break  # One match per file per control is enough
                    except Exception:
                        continue
            except Exception:
                continue

    return matches


def detect_phi_handling(project_dir: Path) -> Dict:
    """Detect potential PHI handling in code."""
    phi_found = []
    code_extensions = ["*.py", "*.js", "*.ts", "*.java", "*.cs", "*.go"]

    for ext in code_extensions:
        try:
            for file_path in project_dir.glob(f"**/{ext}"):
                if any(skip in str(file_path) for skip in ["node_modules", "venv", ".venv", "__pycache__", ".git"]):
                    continue

                try:
                    content = file_path.read_text(encoding='utf-8', errors='ignore')
                    rel_path = str(file_path.relative_to(project_dir))

                    for pattern, phi_type in PHI_PATTERNS:
                        if re.search(pattern, content, re.IGNORECASE):
                            phi_found.append({
                                "file": rel_path,
                                "phi_type": phi_type
                            })
                            break
                except Exception:
                    continue
        except Exception:
            continue

    return {
        "phi_detected": len(phi_found) > 0,
        "files_with_phi": phi_found,
        "phi_types": list(set(p["phi_type"] for p in phi_found))
    }


def detect_security_vulnerabilities(project_dir: Path) -> List[Dict]:
    """Scan for security vulnerabilities."""
    vulnerabilities = []
    code_extensions = ["*.py", "*.js", "*.ts", "*.java", "*.cs", "*.go", "*.yaml", "*.yml", "*.json"]

    for ext in code_extensions:
        try:
            for file_path in project_dir.glob(f"**/{ext}"):
                if any(skip in str(file_path) for skip in ["node_modules", "venv", ".venv", "__pycache__", ".git"]):
                    continue

                try:
                    content = file_path.read_text(encoding='utf-8', errors='ignore')
                    rel_path = str(file_path.relative_to(project_dir))

                    for pattern, vuln_type in VULNERABILITY_PATTERNS:
                        matches = re.findall(pattern, content, re.IGNORECASE)
                        if matches:
                            vulnerabilities.append({
                                "file": rel_path,
                                "vulnerability": vuln_type,
                                "count": len(matches)
                            })
                except Exception:
                    continue
        except Exception:
            continue

    return vulnerabilities


def assess_control(project_dir: Path, control_id: str, control_data: Dict) -> Dict:
    """Assess a single HIPAA control."""
    doc_evidence = scan_documentation(project_dir, control_data["doc_patterns"])
    code_evidence = scan_code_patterns(project_dir, control_data["code_patterns"]) if control_data["code_patterns"] else []

    # Determine compliance status
    has_docs = len(doc_evidence) > 0
    has_code = len(code_evidence) > 0

    if has_docs and (has_code or not control_data["code_patterns"]):
        status = "implemented"
        score = 100
    elif has_docs or has_code:
        status = "partial"
        score = 50
    else:
        status = "gap"
        score = 0

    return {
        "control_id": control_id,
        "title": control_data["title"],
        "requirement": control_data["requirement"],
        "status": status,
        "score": score,
        "weight": control_data["weight"],
        "weighted_score": (score * control_data["weight"]) / 100,
        "documentation": doc_evidence,
        "code_evidence": [e["file"] for e in code_evidence]
    }


def assess_category(project_dir: Path, category_id: str, category_data: Dict) -> Dict:
    """Assess a HIPAA safeguard category."""
    control_results = []
    total_weight = 0
    weighted_score = 0

    for control_id, control_data in category_data["controls"].items():
        result = assess_control(project_dir, control_id, control_data)
        control_results.append(result)
        total_weight += control_data["weight"]
        weighted_score += result["weighted_score"]

    category_score = round((weighted_score / total_weight) * 100, 1) if total_weight > 0 else 0

    return {
        "category": category_id,
        "title": category_data["title"],
        "score": category_score,
        "controls": control_results,
        "compliant": sum(1 for c in control_results if c["status"] == "implemented"),
        "partial": sum(1 for c in control_results if c["status"] == "partial"),
        "gaps": sum(1 for c in control_results if c["status"] == "gap")
    }


def calculate_risk_level(overall_score: float, vulnerabilities: List[Dict], phi_data: Dict) -> Dict:
    """Calculate overall HIPAA risk level."""
    # Base risk from compliance score
    if overall_score >= 80:
        base_risk = "LOW"
        base_score = 1
    elif overall_score >= 60:
        base_risk = "MEDIUM"
        base_score = 2
    elif overall_score >= 40:
        base_risk = "HIGH"
        base_score = 3
    else:
        base_risk = "CRITICAL"
        base_score = 4

    # Adjust for vulnerabilities
    critical_vulns = sum(1 for v in vulnerabilities if "password" in v["vulnerability"].lower() or "secret" in v["vulnerability"].lower())
    if critical_vulns > 0:
        base_score = min(4, base_score + 1)

    # Adjust for PHI handling
    if phi_data["phi_detected"] and base_score < 4:
        base_score = min(4, base_score + 0.5)

    # Map back to risk level
    risk_levels = {1: "LOW", 2: "MEDIUM", 3: "HIGH", 4: "CRITICAL"}
    final_risk = risk_levels.get(int(base_score), "HIGH")

    return {
        "risk_level": final_risk,
        "compliance_score": overall_score,
        "vulnerability_count": len(vulnerabilities),
        "phi_handling_detected": phi_data["phi_detected"]
    }


def generate_recommendations(assessment: Dict) -> List[str]:
    """Generate prioritized recommendations."""
    recommendations = []

    # Technical safeguards first (highest priority for software)
    for cat in assessment["categories"]:
        if cat["category"] == "technical":
            for control in cat["controls"]:
                if control["status"] == "gap":
                    recommendations.append(f"CRITICAL: Implement {control['title']} - {control['requirement']}")
                elif control["status"] == "partial":
                    recommendations.append(f"HIGH: Complete {control['title']} implementation")

    # Administrative safeguards
    for cat in assessment["categories"]:
        if cat["category"] == "administrative":
            for control in cat["controls"]:
                if control["status"] == "gap":
                    recommendations.append(f"MEDIUM: Document {control['title']} procedures")

    # Vulnerabilities
    for vuln in assessment.get("vulnerabilities", [])[:5]:
        recommendations.append(f"SECURITY: Fix {vuln['vulnerability']} in {vuln['file']}")

    return recommendations[:10]  # Top 10


def print_text_report(result: Dict) -> None:
    """Print human-readable report."""
    print("=" * 70)
    print("HIPAA SECURITY RULE COMPLIANCE ASSESSMENT")
    print("=" * 70)

    # Risk summary
    risk = result["risk_assessment"]
    print(f"\nRISK LEVEL: {risk['risk_level']}")
    print(f"Compliance Score: {risk['compliance_score']}%")
    print(f"Vulnerabilities Found: {risk['vulnerability_count']}")
    print(f"PHI Handling Detected: {'Yes' if risk['phi_handling_detected'] else 'No'}")

    # Category scores
    print("\n--- SAFEGUARD CATEGORIES ---")
    for cat in result["categories"]:
        status = "OK" if cat["score"] >= 70 else "NEEDS ATTENTION"
        print(f"  {cat['title']}: {cat['score']}% [{status}]")
        print(f"    Implemented: {cat['compliant']}, Partial: {cat['partial']}, Gaps: {cat['gaps']}")

    # Gaps
    print("\n--- COMPLIANCE GAPS ---")
    gap_count = 0
    for cat in result["categories"]:
        for control in cat["controls"]:
            if control["status"] == "gap":
                gap_count += 1
                print(f"  [{cat['category'].upper()}] {control['title']}")
                print(f"    Requirement: {control['requirement']}")
    if gap_count == 0:
        print("  No critical gaps identified")

    # PHI Detection
    if result["phi_detection"]["phi_detected"]:
        print("\n--- PHI HANDLING DETECTED ---")
        print(f"  PHI Types: {', '.join(result['phi_detection']['phi_types'])}")
        print(f"  Files: {len(result['phi_detection']['files_with_phi'])}")

    # Vulnerabilities
    if result["vulnerabilities"]:
        print("\n--- SECURITY VULNERABILITIES ---")
        for vuln in result["vulnerabilities"][:10]:
            print(f"  - {vuln['vulnerability']}: {vuln['file']}")

    # Recommendations
    if result["recommendations"]:
        print("\n--- RECOMMENDATIONS ---")
        for i, rec in enumerate(result["recommendations"], 1):
            print(f"  {i}. {rec}")

    print("\n" + "=" * 70)
    print(f"Assessment Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print("=" * 70)


def main():
    parser = argparse.ArgumentParser(
        description="HIPAA Risk Assessment Tool for Medical Device Software"
    )
    parser.add_argument(
        "project_dir",
        nargs="?",
        default=".",
        help="Project directory to analyze (default: current directory)"
    )
    parser.add_argument(
        "--category",
        choices=["administrative", "physical", "technical"],
        help="Assess specific safeguard category only"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output in JSON format"
    )
    parser.add_argument(
        "--detailed",
        action="store_true",
        help="Include detailed evidence in output"
    )

    args = parser.parse_args()
    project_dir = Path(args.project_dir).resolve()

    if not project_dir.exists():
        print(f"Error: Directory not found: {project_dir}", file=sys.stderr)
        sys.exit(1)

    # Filter categories if specific one requested
    categories_to_assess = HIPAA_SAFEGUARDS
    if args.category:
        categories_to_assess = {args.category: HIPAA_SAFEGUARDS[args.category]}

    # Perform assessment
    category_results = []
    total_weight = 0
    weighted_score = 0

    for cat_id, cat_data in categories_to_assess.items():
        cat_result = assess_category(project_dir, cat_id, cat_data)
        category_results.append(cat_result)

        # Calculate weighted average
        cat_weight = sum(c["weight"] for c in cat_data["controls"].values())
        total_weight += cat_weight
        weighted_score += (cat_result["score"] * cat_weight) / 100

    overall_score = round((weighted_score / total_weight) * 100, 1) if total_weight > 0 else 0

    # Additional scans
    phi_detection = detect_phi_handling(project_dir)
    vulnerabilities = detect_security_vulnerabilities(project_dir)

    # Risk assessment
    risk_assessment = calculate_risk_level(overall_score, vulnerabilities, phi_detection)

    result = {
        "project_dir": str(project_dir),
        "assessment_date": datetime.now().isoformat(),
        "overall_score": overall_score,
        "risk_assessment": risk_assessment,
        "categories": category_results if args.detailed else [
            {
                "category": c["category"],
                "title": c["title"],
                "score": c["score"],
                "compliant": c["compliant"],
                "partial": c["partial"],
                "gaps": c["gaps"]
            }
            for c in category_results
        ],
        "phi_detection": phi_detection,
        "vulnerabilities": vulnerabilities,
        "recommendations": []
    }

    result["recommendations"] = generate_recommendations(result)

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print_text_report(result)


if __name__ == "__main__":
    main()
