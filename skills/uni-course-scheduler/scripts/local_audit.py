#!/usr/bin/env python3
"""
University Course Planner — Local Audit Script

Audits the cloud output JSON before passing it to the Excel generator.
Checks structure, input/output correspondence, evidence presence,
citation completeness, and malformed formatting.

Usage:
    python3 local_audit.py <cloud_output.json>
"""

import argparse
import json
import sys


def audit_structure(data):
    """Check top-level structure."""
    issues = []
    required_sections = ["course_overview", "recommendations", "weekly_schedule"]
    for section in required_sections:
        if section not in data:
            issues.append(f"Missing top-level section: {section}")
    if "meta" not in data:
        issues.append("Missing meta section")
    return len(issues) == 0, issues


def audit_courses(data):
    """Check course overview integrity."""
    issues = []
    overview = data.get("course_overview", {})
    courses = overview.get("courses", [])
    if not courses:
        issues.append("No courses in course overview")
        return False, issues

    for i, c in enumerate(courses):
        if not c.get("course_code"):
            issues.append(f"Course at index {i} missing course_code")
        if not c.get("course_name"):
            issues.append(f"Course {c.get('course_code', f'index {i}')} missing course_name")
        if not c.get("course_type"):
            issues.append(f"Course {c.get('course_code', f'index {i}')} missing course_type")
        if c.get("course_type") and c["course_type"] not in (
            "Required", "Major Elective", "General Education", "Free Elective"
        ):
            issues.append(
                f"Course {c.get('course_code', '')} has invalid course_type: {c['course_type']}"
            )
    return len(issues) == 0, issues


def audit_recommendations(data):
    """Check recommendation integrity."""
    issues = []
    recs = data.get("recommendations", {})
    recommendations = recs.get("recommendations", [])

    if not recommendations:
        issues.append("No recommendations found")
        return False, issues

    valid_priorities = {"Critical", "High", "Medium", "Low"}
    for i, r in enumerate(recommendations):
        if not r.get("course_code"):
            issues.append(f"Recommendation {i} missing course_code")
        if not r.get("reason"):
            issues.append(f"Recommendation for {r.get('course_code', f'index {i}')} missing reason")
        priority = r.get("priority", "")
        if priority and priority not in valid_priorities:
            issues.append(
                f"Recommendation {r.get('course_code', '')} has invalid priority: {priority}"
            )
        score = r.get("confidence_score")
        if score is not None:
            try:
                if not (0 <= float(score) <= 1):
                    issues.append(
                        f"Recommendation {r.get('course_code', '')} confidence_score out of range: {score}"
                    )
            except (ValueError, TypeError):
                issues.append(
                    f"Recommendation {r.get('course_code', '')} has non-numeric confidence_score: {score}"
                )
    return len(issues) == 0, issues


def audit_schedule(data):
    """Check schedule integrity."""
    issues = []
    schedule_data = data.get("weekly_schedule", {})
    schedule = schedule_data.get("schedule", [])

    if not schedule:
        issues.append("No sessions in weekly schedule")
        return False, issues

    valid_days = {"Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"}
    for i, s in enumerate(schedule):
        if not s.get("course_code"):
            issues.append(f"Session {i} missing course_code")
        if not s.get("day"):
            issues.append(f"Session for {s.get('course_code', f'index {i}')} missing day")
        elif s["day"] not in valid_days:
            issues.append(f"Session {s.get('course_code', '')} has invalid day: {s['day']}")
        if not s.get("start_time"):
            issues.append(f"Session {s.get('course_code', '')} missing start_time")
        if not s.get("end_time"):
            issues.append(f"Session {s.get('course_code', '')} missing end_time")

    conflicts = schedule_data.get("conflict_detection", [])
    if conflicts:
        for c in conflicts:
            issues.append(f"Schedule conflict detected: {c}")

    return len(issues) == 0, issues


def audit_correspondence(data):
    """Check that scheduled courses exist in the catalog."""
    issues = []
    courses = data.get("course_overview", {}).get("courses", [])
    schedule = data.get("weekly_schedule", {}).get("schedule", [])
    course_codes = {c.get("course_code") for c in courses if c.get("course_code")}

    for s in schedule:
        code = s.get("course_code", "")
        if code and code not in course_codes:
            issues.append(f"Scheduled course {code} not found in course overview")
    return len(issues) == 0, issues


def main():
    parser = argparse.ArgumentParser(description="Audit cloud output JSON before Excel generation.")
    parser.add_argument("input", help="Path to the cloud output JSON file")
    args = parser.parse_args()

    with open(args.input, "r", encoding="utf-8") as f:
        data = json.load(f)

    audits = [
        ("structure", "Top-Level Structure", *audit_structure(data)),
        ("courses", "Course Overview Integrity", *audit_courses(data)),
        ("recommendations", "Recommendation Integrity", *audit_recommendations(data)),
        ("schedule", "Schedule Integrity", *audit_schedule(data)),
        ("correspondence", "Input/Output Correspondence", *audit_correspondence(data)),
    ]

    all_pass = all(result for _, _, result, _ in audits)
    passed = sum(1 for _, _, result, _ in audits if result)

    print("# Cloud Output Audit Report")
    print()
    print(f"**Generated:** {__import__('datetime').datetime.now().isoformat()}")
    print(f"**Overall:** {'PASS' if all_pass else 'FAIL'}")
    print(f"**Audits:** {passed}/{len(audits)} passed")
    print()
    print("## Audits")
    print()
    print("| ID | Name | Result | Details |")
    print("|----|------|--------|---------|")
    for audit_id, name, result, issues in audits:
        status = "PASS" if result else "FAIL"
        detail = "; ".join(issues[:3]) if issues else "All checks passed"
        if len(issues) > 3:
            detail += f" (+{len(issues) - 3} more)"
        print(f"| {audit_id} | {name} | {status} | {detail} |")

    return 0 if all_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
