#!/usr/bin/env python3
"""
FDA Submission Tracker

Tracks FDA submission status, calculates timelines, and monitors regulatory milestones
for 510(k), De Novo, and PMA submissions.

Usage:
    python fda_submission_tracker.py <project_dir>
    python fda_submission_tracker.py <project_dir> --type 510k
    python fda_submission_tracker.py <project_dir> --json
"""

import argparse
import json
import os
import sys
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Optional, Any


# FDA review timeline targets (calendar days)
FDA_TIMELINES = {
    "510k_traditional": {
        "acceptance_review": 15,
        "substantive_review": 90,
        "total_goal": 90,
        "ai_response": 180  # Days to respond to Additional Information
    },
    "510k_special": {
        "acceptance_review": 15,
        "substantive_review": 30,
        "total_goal": 30,
        "ai_response": 180
    },
    "510k_abbreviated": {
        "acceptance_review": 15,
        "substantive_review": 30,
        "total_goal": 30,
        "ai_response": 180
    },
    "de_novo": {
        "acceptance_review": 60,
        "substantive_review": 150,
        "total_goal": 150,
        "ai_response": 180
    },
    "pma": {
        "acceptance_review": 45,
        "substantive_review": 180,
        "total_goal": 180,
        "ai_response": 180
    },
    "pma_supplement": {
        "acceptance_review": 15,
        "substantive_review": 180,
        "total_goal": 180,
        "ai_response": 180
    }
}

# Submission milestones by type
MILESTONES = {
    "510k": [
        {"id": "predicate_identified", "name": "Predicate Device Identified", "phase": "planning"},
        {"id": "testing_complete", "name": "Performance Testing Complete", "phase": "preparation"},
        {"id": "documentation_complete", "name": "Submission Documentation Complete", "phase": "preparation"},
        {"id": "submission_sent", "name": "Submission Sent to FDA", "phase": "submission"},
        {"id": "acknowledgment_received", "name": "FDA Acknowledgment Received", "phase": "review"},
        {"id": "acceptance_decision", "name": "Acceptance Review Complete", "phase": "review"},
        {"id": "ai_request", "name": "Additional Information Request", "phase": "review", "optional": True},
        {"id": "ai_response", "name": "AI Response Submitted", "phase": "review", "optional": True},
        {"id": "se_decision", "name": "Substantial Equivalence Decision", "phase": "decision"},
        {"id": "clearance_letter", "name": "510(k) Clearance Letter Received", "phase": "decision"}
    ],
    "de_novo": [
        {"id": "classification_determined", "name": "Classification Determination", "phase": "planning"},
        {"id": "special_controls_defined", "name": "Special Controls Defined", "phase": "preparation"},
        {"id": "risk_assessment_complete", "name": "Risk Assessment Complete", "phase": "preparation"},
        {"id": "testing_complete", "name": "Performance Testing Complete", "phase": "preparation"},
        {"id": "submission_sent", "name": "Submission Sent to FDA", "phase": "submission"},
        {"id": "acknowledgment_received", "name": "FDA Acknowledgment Received", "phase": "review"},
        {"id": "acceptance_decision", "name": "Acceptance Review Complete", "phase": "review"},
        {"id": "ai_request", "name": "Additional Information Request", "phase": "review", "optional": True},
        {"id": "ai_response", "name": "AI Response Submitted", "phase": "review", "optional": True},
        {"id": "classification_decision", "name": "De Novo Classification Decision", "phase": "decision"}
    ],
    "pma": [
        {"id": "ide_approved", "name": "IDE Approval (if required)", "phase": "planning", "optional": True},
        {"id": "clinical_complete", "name": "Clinical Study Complete", "phase": "preparation"},
        {"id": "clinical_report_complete", "name": "Clinical Study Report Complete", "phase": "preparation"},
        {"id": "documentation_complete", "name": "PMA Documentation Complete", "phase": "preparation"},
        {"id": "submission_sent", "name": "PMA Submission Sent to FDA", "phase": "submission"},
        {"id": "acknowledgment_received", "name": "FDA Acknowledgment Received", "phase": "review"},
        {"id": "filing_decision", "name": "Filing Decision", "phase": "review"},
        {"id": "ai_request", "name": "Major Deficiency Letter", "phase": "review", "optional": True},
        {"id": "ai_response", "name": "Deficiency Response Submitted", "phase": "review", "optional": True},
        {"id": "panel_meeting", "name": "Advisory Committee Meeting", "phase": "review", "optional": True},
        {"id": "approval_decision", "name": "PMA Approval Decision", "phase": "decision"}
    ]
}


def find_submission_config(project_dir: Path) -> Optional[Dict]:
    """Find and load submission configuration file."""
    config_paths = [
        project_dir / "fda_submission.json",
        project_dir / "regulatory" / "fda_submission.json",
        project_dir / ".fda" / "submission.json"
    ]

    for config_path in config_paths:
        if config_path.exists():
            try:
                with open(config_path) as f:
                    return json.load(f)
            except json.JSONDecodeError:
                continue

    return None


def calculate_timeline_status(submission_type: str, milestones: Dict[str, str]) -> Dict:
    """Calculate timeline status based on submission type and milestone dates."""
    timeline_config = FDA_TIMELINES.get(submission_type, FDA_TIMELINES["510k_traditional"])

    result = {
        "submission_type": submission_type,
        "timeline_config": timeline_config,
        "status": "not_started",
        "days_elapsed": 0,
        "days_remaining": None,
        "projected_decision_date": None,
        "on_track": None
    }

    # Check if submission has been sent
    if "submission_sent" in milestones:
        try:
            submission_date = datetime.strptime(milestones["submission_sent"], "%Y-%m-%d")
            today = datetime.now()
            result["days_elapsed"] = (today - submission_date).days

            # Check for AI hold
            ai_hold_days = 0
            if "ai_request" in milestones and "ai_response" in milestones:
                ai_request_date = datetime.strptime(milestones["ai_request"], "%Y-%m-%d")
                ai_response_date = datetime.strptime(milestones["ai_response"], "%Y-%m-%d")
                ai_hold_days = (ai_response_date - ai_request_date).days
            elif "ai_request" in milestones and "ai_response" not in milestones:
                ai_request_date = datetime.strptime(milestones["ai_request"], "%Y-%m-%d")
                ai_hold_days = (today - ai_request_date).days
                result["status"] = "ai_hold"

            # Calculate review days (excluding AI hold)
            review_days = result["days_elapsed"] - ai_hold_days

            # Determine status
            if "se_decision" in milestones or "approval_decision" in milestones or "classification_decision" in milestones:
                result["status"] = "complete"
            elif "acceptance_decision" in milestones:
                result["status"] = "substantive_review"
            elif "acknowledgment_received" in milestones:
                result["status"] = "acceptance_review"
            else:
                result["status"] = "submitted"

            # Calculate projected decision date
            if result["status"] not in ["complete", "ai_hold"]:
                goal_days = timeline_config["total_goal"]
                result["days_remaining"] = max(0, goal_days - review_days)
                result["projected_decision_date"] = (submission_date + timedelta(days=goal_days + ai_hold_days)).strftime("%Y-%m-%d")
                result["on_track"] = review_days <= goal_days

        except ValueError:
            pass

    return result


def analyze_milestone_status(submission_type: str, completed_milestones: Dict[str, str]) -> List[Dict]:
    """Analyze milestone completion status."""
    milestone_list = MILESTONES.get(submission_type.split("_")[0], MILESTONES["510k"])

    results = []
    for milestone in milestone_list:
        status = {
            "id": milestone["id"],
            "name": milestone["name"],
            "phase": milestone["phase"],
            "optional": milestone.get("optional", False),
            "completed": milestone["id"] in completed_milestones,
            "completion_date": completed_milestones.get(milestone["id"])
        }
        results.append(status)

    return results


def calculate_submission_readiness(project_dir: Path, submission_type: str) -> Dict:
    """Check submission readiness by looking for required documentation."""

    required_docs = {
        "510k": [
            {"name": "Device Description", "patterns": ["device_description*", "device_desc*"]},
            {"name": "Indications for Use", "patterns": ["indications*", "ifu*"]},
            {"name": "Substantial Equivalence", "patterns": ["substantial_equiv*", "se_comparison*", "predicate*"]},
            {"name": "Performance Testing", "patterns": ["performance*", "test_report*", "bench_test*"]},
            {"name": "Biocompatibility", "patterns": ["biocompat*", "iso_10993*"]},
            {"name": "Labeling", "patterns": ["label*", "ifu*", "instructions*"]},
            {"name": "Software Documentation", "patterns": ["software*", "iec_62304*"], "optional": True},
            {"name": "Sterilization Validation", "patterns": ["steriliz*", "sterility*"], "optional": True}
        ],
        "de_novo": [
            {"name": "Device Description", "patterns": ["device_description*", "device_desc*"]},
            {"name": "Risk Assessment", "patterns": ["risk*", "hazard*"]},
            {"name": "Special Controls", "patterns": ["special_control*"]},
            {"name": "Performance Testing", "patterns": ["performance*", "test_report*"]},
            {"name": "Labeling", "patterns": ["label*", "ifu*"]}
        ],
        "pma": [
            {"name": "Device Description", "patterns": ["device_description*"]},
            {"name": "Manufacturing Information", "patterns": ["manufacturing*", "production*"]},
            {"name": "Clinical Study Report", "patterns": ["clinical*", "csr*"]},
            {"name": "Nonclinical Testing", "patterns": ["nonclinical*", "bench*", "preclinical*"]},
            {"name": "Risk Analysis", "patterns": ["risk*", "fmea*"]},
            {"name": "Labeling", "patterns": ["label*", "ifu*"]}
        ]
    }

    docs_to_check = required_docs.get(submission_type.split("_")[0], required_docs["510k"])

    # Search common documentation directories
    doc_dirs = [
        project_dir / "regulatory",
        project_dir / "regulatory" / "fda",
        project_dir / "docs",
        project_dir / "documentation",
        project_dir / "dhf",
        project_dir
    ]

    results = []
    for doc in docs_to_check:
        found = False
        found_path = None

        for doc_dir in doc_dirs:
            if not doc_dir.exists():
                continue

            for pattern in doc["patterns"]:
                matches = list(doc_dir.glob(f"**/{pattern}"))
                matches.extend(list(doc_dir.glob(f"**/{pattern.upper()}")))
                if matches:
                    found = True
                    found_path = str(matches[0].relative_to(project_dir))
                    break

            if found:
                break

        results.append({
            "name": doc["name"],
            "required": not doc.get("optional", False),
            "found": found,
            "path": found_path
        })

    required_found = sum(1 for r in results if r["required"] and r["found"])
    required_total = sum(1 for r in results if r["required"])

    return {
        "documents": results,
        "required_complete": required_found,
        "required_total": required_total,
        "readiness_percentage": round((required_found / required_total) * 100, 1) if required_total > 0 else 0
    }


def generate_sample_config() -> Dict:
    """Generate sample submission configuration."""
    return {
        "submission_type": "510k_traditional",
        "device_name": "Example Medical Device",
        "product_code": "ABC",
        "predicate_device": {
            "name": "Predicate Device Name",
            "k_number": "K123456"
        },
        "milestones": {
            "predicate_identified": "2024-01-15",
            "testing_complete": "2024-03-01",
            "documentation_complete": "2024-03-15"
        },
        "contacts": {
            "regulatory_lead": "Name",
            "quality_lead": "Name"
        },
        "notes": "Add milestone dates as they are completed"
    }


def print_text_report(result: Dict) -> None:
    """Print human-readable report."""
    print("=" * 60)
    print("FDA SUBMISSION TRACKER REPORT")
    print("=" * 60)

    if "error" in result:
        print(f"\nError: {result['error']}")
        print(f"\nTo create a configuration file, run with --init")
        return

    # Basic info
    print(f"\nDevice: {result.get('device_name', 'Unknown')}")
    print(f"Submission Type: {result['submission_type']}")
    print(f"Product Code: {result.get('product_code', 'N/A')}")

    # Timeline status
    timeline = result["timeline_status"]
    print(f"\n--- Timeline Status ---")
    print(f"Status: {timeline['status'].upper()}")
    print(f"Days Elapsed: {timeline['days_elapsed']}")
    if timeline["days_remaining"] is not None:
        print(f"Days Remaining (FDA goal): {timeline['days_remaining']}")
    if timeline["projected_decision_date"]:
        print(f"Projected Decision Date: {timeline['projected_decision_date']}")
    if timeline["on_track"] is not None:
        status = "ON TRACK" if timeline["on_track"] else "BEHIND SCHEDULE"
        print(f"Timeline Status: {status}")

    # Milestones
    print(f"\n--- Milestones ---")
    for ms in result["milestones"]:
        status = "[X]" if ms["completed"] else "[ ]"
        optional = " (optional)" if ms["optional"] else ""
        date = f" - {ms['completion_date']}" if ms["completion_date"] else ""
        print(f"  {status} {ms['name']}{optional}{date}")

    # Readiness
    if "readiness" in result:
        print(f"\n--- Submission Readiness ---")
        readiness = result["readiness"]
        print(f"Readiness: {readiness['readiness_percentage']}% ({readiness['required_complete']}/{readiness['required_total']} required docs)")

        print("\n  Documents:")
        for doc in readiness["documents"]:
            status = "[X]" if doc["found"] else "[ ]"
            req = "(required)" if doc["required"] else "(optional)"
            path = f" - {doc['path']}" if doc["path"] else ""
            print(f"    {status} {doc['name']} {req}{path}")

    # Recommendations
    if result.get("recommendations"):
        print(f"\n--- Recommendations ---")
        for i, rec in enumerate(result["recommendations"], 1):
            print(f"  {i}. {rec}")

    print("\n" + "=" * 60)


def generate_recommendations(result: Dict) -> List[str]:
    """Generate actionable recommendations based on status."""
    recommendations = []

    timeline = result["timeline_status"]

    # Timeline recommendations
    if timeline["status"] == "ai_hold":
        recommendations.append("Priority: Respond to FDA Additional Information request within 180 days")
    elif timeline["on_track"] is False:
        recommendations.append("Warning: Submission is behind FDA review schedule - consider contacting FDA")

    # Milestone recommendations
    completed_phases = set()
    for ms in result["milestones"]:
        if ms["completed"]:
            completed_phases.add(ms["phase"])

    if "submission" not in completed_phases and "preparation" in completed_phases:
        recommendations.append("Ready for submission: Documentation complete, proceed with FDA submission")

    # Readiness recommendations
    if "readiness" in result:
        missing_required = [d for d in result["readiness"]["documents"] if d["required"] and not d["found"]]
        if missing_required:
            docs = ", ".join(d["name"] for d in missing_required[:3])
            recommendations.append(f"Missing required documentation: {docs}")

    return recommendations


def analyze_submission(project_dir: Path, submission_type: Optional[str] = None) -> Dict:
    """Main analysis function."""

    # Try to find existing configuration
    config = find_submission_config(project_dir)

    if config is None:
        # No config found - do basic analysis
        sub_type = submission_type or "510k_traditional"
        result = {
            "submission_type": sub_type,
            "config_found": False,
            "timeline_status": calculate_timeline_status(sub_type, {}),
            "milestones": analyze_milestone_status(sub_type, {}),
            "readiness": calculate_submission_readiness(project_dir, sub_type)
        }
    else:
        # Config found - full analysis
        sub_type = config.get("submission_type", submission_type or "510k_traditional")
        milestones = config.get("milestones", {})

        result = {
            "submission_type": sub_type,
            "device_name": config.get("device_name"),
            "product_code": config.get("product_code"),
            "predicate_device": config.get("predicate_device"),
            "config_found": True,
            "timeline_status": calculate_timeline_status(sub_type, milestones),
            "milestones": analyze_milestone_status(sub_type, milestones),
            "readiness": calculate_submission_readiness(project_dir, sub_type)
        }

    # Generate recommendations
    result["recommendations"] = generate_recommendations(result)

    return result


def main():
    parser = argparse.ArgumentParser(
        description="FDA Submission Tracker - Monitor 510(k), De Novo, and PMA submissions"
    )
    parser.add_argument(
        "project_dir",
        nargs="?",
        default=".",
        help="Project directory to analyze (default: current directory)"
    )
    parser.add_argument(
        "--type",
        choices=["510k", "510k_traditional", "510k_special", "510k_abbreviated",
                 "de_novo", "pma", "pma_supplement"],
        help="Submission type (overrides config file)"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output in JSON format"
    )
    parser.add_argument(
        "--init",
        action="store_true",
        help="Create sample configuration file"
    )

    args = parser.parse_args()
    project_dir = Path(args.project_dir).resolve()

    if not project_dir.exists():
        print(f"Error: Directory not found: {project_dir}", file=sys.stderr)
        sys.exit(1)

    if args.init:
        config_path = project_dir / "fda_submission.json"
        if config_path.exists():
            print(f"Configuration file already exists: {config_path}")
            sys.exit(1)

        sample = generate_sample_config()
        if args.type:
            sample["submission_type"] = args.type

        with open(config_path, "w") as f:
            json.dump(sample, f, indent=2)

        print(f"Created sample configuration: {config_path}")
        print("Edit this file with your submission details and milestone dates.")
        return

    result = analyze_submission(project_dir, args.type)

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print_text_report(result)


if __name__ == "__main__":
    main()
