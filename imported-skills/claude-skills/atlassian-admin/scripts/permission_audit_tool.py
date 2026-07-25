#!/usr/bin/env python3
"""
Permission Audit Tool

Analyzes Atlassian permission schemes for security issues. Checks for
over-permissioned groups, direct user permissions, missing restrictions on
sensitive actions, inconsistencies across projects, and compliance gaps.

Usage:
    python permission_audit_tool.py permissions.json
    python permission_audit_tool.py permissions.json --format json
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Optional, Set


# ---------------------------------------------------------------------------
# Audit Configuration
# ---------------------------------------------------------------------------

SENSITIVE_PERMISSIONS = {
    "administer_project",
    "administer_jira",
    "delete_issues",
    "delete_all_comments",
    "delete_all_attachments",
    "manage_watchers",
    "modify_reporter",
    "bulk_change",
    "system_admin",
    "manage_group_filter_subscriptions",
}

RECOMMENDED_GROUP_ONLY_PERMISSIONS = {
    "browse_projects",
    "create_issues",
    "edit_issues",
    "transition_issues",
    "assign_issues",
    "resolve_issues",
    "close_issues",
    "add_comments",
    "edit_all_comments",
}

SEVERITY_WEIGHTS = {
    "critical": 25,
    "high": 15,
    "medium": 8,
    "low": 3,
    "info": 1,
}


# ---------------------------------------------------------------------------
# Audit Checks
# ---------------------------------------------------------------------------

def check_over_permissioned_groups(
    schemes: List[Dict[str, Any]],
) -> List[Dict[str, str]]:
    """Check for groups with overly broad admin access."""
    findings = []

    for scheme in schemes:
        scheme_name = scheme.get("name", "Unknown Scheme")
        grants = scheme.get("grants", [])

        group_permissions = {}
        for grant in grants:
            group = grant.get("group", "")
            permission = grant.get("permission", "").lower()
            if group:
                if group not in group_permissions:
                    group_permissions[group] = set()
                group_permissions[group].add(permission)

        for group, perms in group_permissions.items():
            admin_perms = perms & SENSITIVE_PERMISSIONS
            if len(admin_perms) >= 3:
                findings.append({
                    "rule": "over_permissioned_group",
                    "severity": "high",
                    "scheme": scheme_name,
                    "group": group,
                    "message": f"Group '{group}' has {len(admin_perms)} sensitive permissions "
                               f"in scheme '{scheme_name}': {', '.join(sorted(admin_perms))}. "
                               f"Review if all are necessary.",
                })

            if "system_admin" in perms or "administer_jira" in perms:
                findings.append({
                    "rule": "admin_access_warning",
                    "severity": "critical",
                    "scheme": scheme_name,
                    "group": group,
                    "message": f"Group '{group}' has system/Jira admin access in '{scheme_name}'. "
                               f"Ensure this is strictly necessary and membership is limited.",
                })

    return findings


def check_direct_user_permissions(
    schemes: List[Dict[str, Any]],
) -> List[Dict[str, str]]:
    """Check for permissions granted directly to users instead of groups."""
    findings = []

    for scheme in schemes:
        scheme_name = scheme.get("name", "Unknown Scheme")
        grants = scheme.get("grants", [])

        for grant in grants:
            user = grant.get("user", "")
            permission = grant.get("permission", "")

            if user and not grant.get("group"):
                severity = "high" if permission.lower() in SENSITIVE_PERMISSIONS else "medium"
                findings.append({
                    "rule": "direct_user_permission",
                    "severity": severity,
                    "scheme": scheme_name,
                    "user": user,
                    "message": f"User '{user}' has direct permission '{permission}' in '{scheme_name}'. "
                               f"Use groups instead for maintainability and audit clarity.",
                })

    return findings


def check_missing_restrictions(
    schemes: List[Dict[str, Any]],
) -> List[Dict[str, str]]:
    """Check for missing restrictions on sensitive actions."""
    findings = []

    for scheme in schemes:
        scheme_name = scheme.get("name", "Unknown Scheme")
        grants = scheme.get("grants", [])

        granted_permissions = set()
        for grant in grants:
            granted_permissions.add(grant.get("permission", "").lower())

        # Check if delete permissions are unrestricted
        delete_perms = {"delete_issues", "delete_all_comments", "delete_all_attachments"}
        unrestricted_deletes = delete_perms & granted_permissions

        for grant in grants:
            perm = grant.get("permission", "").lower()
            group = grant.get("group", "")
            if perm in delete_perms and group:
                # Check if granted to broad groups
                broad_groups = {"users", "everyone", "all-users", "jira-users", "jira-software-users"}
                if group.lower() in broad_groups:
                    findings.append({
                        "rule": "unrestricted_delete",
                        "severity": "critical",
                        "scheme": scheme_name,
                        "message": f"Delete permission '{perm}' granted to broad group '{group}' "
                                   f"in '{scheme_name}'. Restrict to admins or leads only.",
                    })

        # Check if admin permissions exist
        admin_perms = {"administer_project", "administer_jira", "system_admin"}
        if not (admin_perms & granted_permissions):
            findings.append({
                "rule": "no_admin_defined",
                "severity": "medium",
                "scheme": scheme_name,
                "message": f"No explicit admin permission defined in '{scheme_name}'. "
                           f"Ensure project administration is properly assigned.",
            })

    return findings


def check_scheme_consistency(
    schemes: List[Dict[str, Any]],
) -> List[Dict[str, str]]:
    """Check for inconsistencies across permission schemes."""
    findings = []

    if len(schemes) < 2:
        return findings

    # Compare permission sets across schemes
    scheme_perms = {}
    for scheme in schemes:
        name = scheme.get("name", "Unknown")
        perms = set()
        for grant in scheme.get("grants", []):
            perms.add(grant.get("permission", "").lower())
        scheme_perms[name] = perms

    # Find schemes with significantly different permission sets
    all_perms = set()
    for perms in scheme_perms.values():
        all_perms |= perms

    scheme_names = list(scheme_perms.keys())
    for i in range(len(scheme_names)):
        for j in range(i + 1, len(scheme_names)):
            name_a = scheme_names[i]
            name_b = scheme_names[j]
            diff = scheme_perms[name_a].symmetric_difference(scheme_perms[name_b])
            if len(diff) > 5:
                findings.append({
                    "rule": "scheme_inconsistency",
                    "severity": "medium",
                    "message": f"Schemes '{name_a}' and '{name_b}' differ significantly "
                               f"({len(diff)} different permissions). Review for intentional differences.",
                })

    return findings


def check_compliance_gaps(
    schemes: List[Dict[str, Any]],
) -> List[Dict[str, str]]:
    """Check for common compliance gaps."""
    findings = []

    for scheme in schemes:
        scheme_name = scheme.get("name", "Unknown Scheme")
        grants = scheme.get("grants", [])

        groups_used = set()
        users_used = set()
        for grant in grants:
            if grant.get("group"):
                groups_used.add(grant["group"])
            if grant.get("user"):
                users_used.add(grant["user"])

        # Check for separation of duties
        admin_groups = set()
        for grant in grants:
            if grant.get("permission", "").lower() in SENSITIVE_PERMISSIONS and grant.get("group"):
                admin_groups.add(grant["group"])

        if len(admin_groups) == 1 and len(groups_used) > 1:
            findings.append({
                "rule": "separation_of_duties",
                "severity": "info",
                "scheme": scheme_name,
                "message": f"Only one group ('{next(iter(admin_groups))}') holds all sensitive permissions "
                           f"in '{scheme_name}'. Consider separating duties across multiple groups.",
            })

        # Check user count
        if len(users_used) > 5:
            findings.append({
                "rule": "too_many_direct_users",
                "severity": "high",
                "scheme": scheme_name,
                "message": f"Scheme '{scheme_name}' has {len(users_used)} direct user grants. "
                           f"Migrate to group-based permissions for better governance.",
            })

    return findings


# ---------------------------------------------------------------------------
# Main Analysis
# ---------------------------------------------------------------------------

def audit_permissions(data: Dict[str, Any]) -> Dict[str, Any]:
    """Run full permission audit."""
    schemes = data.get("schemes", [])

    if not schemes:
        # Try treating the entire input as a single scheme
        if data.get("grants") or data.get("name"):
            schemes = [data]
        else:
            return {
                "risk_score": 0,
                "grade": "invalid",
                "error": "No permission schemes found in input",
                "findings": [],
                "summary": {},
            }

    all_findings = []
    all_findings.extend(check_over_permissioned_groups(schemes))
    all_findings.extend(check_direct_user_permissions(schemes))
    all_findings.extend(check_missing_restrictions(schemes))
    all_findings.extend(check_scheme_consistency(schemes))
    all_findings.extend(check_compliance_gaps(schemes))

    # Calculate risk score (higher = more risk)
    summary = {"critical": 0, "high": 0, "medium": 0, "low": 0, "info": 0}
    total_penalty = 0
    for finding in all_findings:
        severity = finding["severity"]
        summary[severity] = summary.get(severity, 0) + 1
        total_penalty += SEVERITY_WEIGHTS.get(severity, 0)

    risk_score = min(100, total_penalty)
    health_score = max(0, 100 - risk_score)

    if health_score >= 85:
        grade = "excellent"
    elif health_score >= 70:
        grade = "good"
    elif health_score >= 50:
        grade = "fair"
    else:
        grade = "poor"

    # Generate remediation recommendations
    remediations = _generate_remediations(all_findings)

    return {
        "risk_score": risk_score,
        "health_score": health_score,
        "grade": grade,
        "schemes_analyzed": len(schemes),
        "findings": all_findings,
        "summary": summary,
        "remediations": remediations,
    }


def _generate_remediations(findings: List[Dict[str, str]]) -> List[str]:
    """Generate remediation recommendations."""
    remediations = []
    rules_seen = set()

    for finding in findings:
        rule = finding["rule"]
        if rule in rules_seen:
            continue
        rules_seen.add(rule)

        if rule == "over_permissioned_group":
            remediations.append("Review and reduce sensitive permissions for over-permissioned groups. Apply principle of least privilege.")
        elif rule == "admin_access_warning":
            remediations.append("Audit admin group membership. Limit system/Jira admin access to essential personnel only.")
        elif rule == "direct_user_permission":
            remediations.append("Migrate direct user permissions to group-based grants. Create functional groups for common permission sets.")
        elif rule == "unrestricted_delete":
            remediations.append("Restrict delete permissions to project admins or leads. Remove from broad user groups.")
        elif rule == "scheme_inconsistency":
            remediations.append("Standardize permission schemes across projects. Document intentional differences.")
        elif rule == "too_many_direct_users":
            remediations.append("Create groups for users with direct permissions. This simplifies onboarding/offboarding.")
        elif rule == "separation_of_duties":
            remediations.append("Consider splitting admin responsibilities across multiple groups for better separation of duties.")
        elif rule == "no_admin_defined":
            remediations.append("Define explicit admin permissions in each scheme to ensure proper project governance.")

    return remediations


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def format_text_output(result: Dict[str, Any]) -> str:
    """Format results as readable text report."""
    lines = []
    lines.append("=" * 60)
    lines.append("PERMISSION AUDIT REPORT")
    lines.append("=" * 60)
    lines.append("")

    if "error" in result:
        lines.append(f"ERROR: {result['error']}")
        return "\n".join(lines)

    lines.append("AUDIT SUMMARY")
    lines.append("-" * 30)
    lines.append(f"Risk Score: {result['risk_score']}/100 (lower is better)")
    lines.append(f"Health Score: {result['health_score']}/100")
    lines.append(f"Grade: {result['grade'].title()}")
    lines.append(f"Schemes Analyzed: {result['schemes_analyzed']}")
    lines.append("")

    summary = result.get("summary", {})
    lines.append("FINDINGS BY SEVERITY")
    lines.append("-" * 30)
    lines.append(f"Critical: {summary.get('critical', 0)}")
    lines.append(f"High: {summary.get('high', 0)}")
    lines.append(f"Medium: {summary.get('medium', 0)}")
    lines.append(f"Low: {summary.get('low', 0)}")
    lines.append(f"Info: {summary.get('info', 0)}")
    lines.append("")

    findings = result.get("findings", [])
    if findings:
        lines.append("DETAILED FINDINGS")
        lines.append("-" * 30)
        for i, finding in enumerate(findings, 1):
            severity = finding["severity"].upper()
            lines.append(f"{i}. [{severity}] {finding['message']}")
            lines.append(f"   Rule: {finding['rule']}")
            if finding.get("scheme"):
                lines.append(f"   Scheme: {finding['scheme']}")
            lines.append("")

    remediations = result.get("remediations", [])
    if remediations:
        lines.append("REMEDIATION RECOMMENDATIONS")
        lines.append("-" * 30)
        for i, rem in enumerate(remediations, 1):
            lines.append(f"{i}. {rem}")

    return "\n".join(lines)


def format_json_output(result: Dict[str, Any]) -> Dict[str, Any]:
    """Format results as JSON."""
    return result


# ---------------------------------------------------------------------------
# CLI Interface
# ---------------------------------------------------------------------------

def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Audit Atlassian permission schemes for security issues"
    )
    parser.add_argument(
        "permissions_file",
        help="JSON file with permission scheme data",
    )
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )

    args = parser.parse_args()

    try:
        with open(args.permissions_file, "r") as f:
            data = json.load(f)

        result = audit_permissions(data)

        if args.format == "json":
            print(json.dumps(format_json_output(result), indent=2))
        else:
            print(format_text_output(result))

        return 0

    except FileNotFoundError:
        print(f"Error: File '{args.permissions_file}' not found", file=sys.stderr)
        return 1
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in '{args.permissions_file}': {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
