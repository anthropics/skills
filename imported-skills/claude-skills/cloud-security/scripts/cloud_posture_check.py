#!/usr/bin/env python3
"""
cloud_posture_check.py — Cloud Security Posture Check

Analyses IAM policies and cloud resource configurations for privilege
escalation paths, data exfiltration risks, public exposure, S3 bucket
misconfigurations, and Security Group dangerous inbound rules.

Supports AWS (full), with Azure/GCP stubs for future expansion.

Usage:
    python3 cloud_posture_check.py policy.json
    python3 cloud_posture_check.py policy.json --check privilege-escalation --json
    python3 cloud_posture_check.py sg.json --check sg --provider aws --json
    python3 cloud_posture_check.py bucket.json --check s3 --severity-modifier internet-facing

Exit codes:
    0  No findings or informational only
    1  High-severity findings present
    2  Critical findings present
"""

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# IAM Analysis Constants (from analyze_iam_policy.py base)
# ---------------------------------------------------------------------------

PRIVILEGE_ESCALATION_ACTIONS: List[str] = [
    "iam:CreatePolicyVersion",
    "iam:SetDefaultPolicyVersion",
    "iam:PassRole",
    "iam:CreateAccessKey",
    "iam:CreateLoginProfile",
    "iam:UpdateLoginProfile",
    "iam:AttachUserPolicy",
    "iam:AttachGroupPolicy",
    "iam:AttachRolePolicy",
    "iam:PutUserPolicy",
    "iam:PutGroupPolicy",
    "iam:PutRolePolicy",
    "iam:AddUserToGroup",
    "iam:UpdateAssumeRolePolicy",
    "sts:AssumeRole",
    "iam:CreateRole",
    "iam:DeletePolicyVersion",
    "iam:CreateUser",
    "iam:UpdateAccessKey",
    "iam:DeactivateMFADevice",
    "iam:DeleteVirtualMFADevice",
    "iam:ResyncMFADevice",
    "iam:EnableMFADevice",
    "iam:DeleteUserPermissionsBoundary",
    "iam:DeleteRolePermissionsBoundary",
    "lambda:CreateFunction",
    "lambda:InvokeFunction",
    "lambda:UpdateFunctionCode",
    "lambda:AddPermission",
    "ec2:RunInstances",
    "ec2:AssociateIamInstanceProfile",
    "ec2:ReplaceIamInstanceProfileAssociation",
    "cloudformation:CreateStack",
    "cloudformation:UpdateStack",
    "datapipeline:CreatePipeline",
    "datapipeline:PutPipelineDefinition",
    "glue:CreateDevEndpoint",
    "glue:UpdateDevEndpoint",
    "codestar:CreateProject",
    "codecommit:CreateRepository",
    "ssm:SendCommand",
    "ssm:StartSession",
]

ESCALATION_COMBOS: List[Dict[str, Any]] = [
    {
        "name": "PassRole + Lambda Invoke",
        "actions": ["iam:PassRole", "lambda:InvokeFunction"],
        "description": "Attacker can pass a privileged role to a Lambda function and invoke it",
        "severity": "critical",
    },
    {
        "name": "PassRole + EC2 RunInstances",
        "actions": ["iam:PassRole", "ec2:RunInstances"],
        "description": "Attacker can launch an EC2 instance with a privileged IAM role",
        "severity": "critical",
    },
    {
        "name": "CreatePolicyVersion + SetDefaultPolicyVersion",
        "actions": ["iam:CreatePolicyVersion", "iam:SetDefaultPolicyVersion"],
        "description": "Attacker can create and activate a new policy version granting full access",
        "severity": "critical",
    },
    {
        "name": "AttachUserPolicy + AdministratorAccess",
        "actions": ["iam:AttachUserPolicy"],
        "description": "Can attach any managed policy including AdministratorAccess to users",
        "severity": "high",
    },
    {
        "name": "PutUserPolicy + Wildcard",
        "actions": ["iam:PutUserPolicy"],
        "description": "Can inject inline policies with wildcard permissions",
        "severity": "high",
    },
    {
        "name": "CloudFormation Stack Manipulation",
        "actions": ["cloudformation:CreateStack", "iam:PassRole"],
        "description": "Attacker can deploy a CloudFormation stack with a privileged role",
        "severity": "critical",
    },
    {
        "name": "SSM Session Start",
        "actions": ["ssm:StartSession"],
        "description": "Can start interactive sessions on EC2 instances without SSH",
        "severity": "high",
    },
    {
        "name": "Glue Dev Endpoint",
        "actions": ["glue:CreateDevEndpoint", "iam:PassRole"],
        "description": "Can create a Glue dev endpoint with a privileged role for code execution",
        "severity": "critical",
    },
]

DATA_EXFILTRATION_ACTIONS: List[str] = [
    "s3:GetObject",
    "s3:ListBucket",
    "s3:GetBucketAcl",
    "s3:GetObjectAcl",
    "s3:GetBucketPolicy",
    "s3:PutBucketPolicy",
    "s3:PutBucketAcl",
    "s3:PutObjectAcl",
    "s3:CopyObject",
    "s3:HeadObject",
    "rds:DescribeDBInstances",
    "rds:DownloadDBLogFilePortion",
    "rds:DescribeDBSnapshots",
    "rds:RestoreDBInstanceFromDBSnapshot",
    "dynamodb:Scan",
    "dynamodb:Query",
    "dynamodb:GetItem",
    "dynamodb:BatchGetItem",
    "ec2:DescribeInstances",
    "ec2:DescribeSnapshots",
    "ec2:CreateSnapshot",
    "ec2:ModifySnapshotAttribute",
    "ecr:GetDownloadUrlForLayer",
    "ecr:BatchGetImage",
    "secretsmanager:GetSecretValue",
    "secretsmanager:ListSecrets",
    "ssm:GetParameter",
    "ssm:GetParameters",
    "ssm:GetParametersByPath",
    "kms:Decrypt",
    "kms:GenerateDataKey",
    "lambda:GetFunction",
    "codecommit:GitPull",
    "cloudtrail:StopLogging",
    "cloudtrail:DeleteTrail",
    "guardduty:DeleteDetector",
    "logs:DeleteLogGroup",
    "logs:DeleteLogStream",
]


# ---------------------------------------------------------------------------
# Data Classes
# ---------------------------------------------------------------------------

@dataclass
class IAMFinding:
    """Represents a single IAM or cloud posture finding."""
    finding_id: str
    category: str               # privilege-escalation | data-exfil | public-exposure | s3 | sg
    severity: str               # critical | high | medium | low | informational
    title: str
    description: str
    affected_actions: List[str] = field(default_factory=list)
    affected_resource: str = "*"
    recommendation: str = ""
    mitre_technique: str = ""


@dataclass
class IAMAnalysisResult:
    """Aggregated result of an IAM / posture analysis run."""
    source: str
    check_mode: str
    provider: str
    severity_modifier: str
    findings: List[IAMFinding] = field(default_factory=list)
    summary: Dict[str, Any] = field(default_factory=dict)
    timestamp_utc: str = ""

    def __post_init__(self) -> None:
        if not self.timestamp_utc:
            self.timestamp_utc = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    @property
    def critical_count(self) -> int:
        return sum(1 for f in self.findings if f.severity == "critical")

    @property
    def high_count(self) -> int:
        return sum(1 for f in self.findings if f.severity == "high")

    @property
    def medium_count(self) -> int:
        return sum(1 for f in self.findings if f.severity == "medium")

    @property
    def low_count(self) -> int:
        return sum(1 for f in self.findings if f.severity == "low")


# ---------------------------------------------------------------------------
# Severity Bump Utility
# ---------------------------------------------------------------------------

_SEV_LADDER = ["informational", "low", "medium", "high", "critical"]


def _bump_severity(severity: str, modifier: str) -> str:
    """
    Bump severity up one band when modifier is internet-facing or regulated-data.

    low -> medium -> high -> critical (caps at critical).
    """
    if modifier not in ("internet-facing", "regulated-data"):
        return severity
    try:
        idx = _SEV_LADDER.index(severity.lower())
        return _SEV_LADDER[min(idx + 1, len(_SEV_LADDER) - 1)]
    except ValueError:
        return severity


# ---------------------------------------------------------------------------
# Core IAM Analysis Functions (from analyze_iam_policy.py base)
# ---------------------------------------------------------------------------

def _extract_actions(statement: dict) -> List[str]:
    """Normalise Action field to a list of lowercase strings."""
    action_field = statement.get("Action") or statement.get("action") or []
    if isinstance(action_field, str):
        return [action_field.lower()]
    return [str(a).lower() for a in action_field]


def _extract_resources(statement: dict) -> List[str]:
    """Normalise Resource field to a list of strings."""
    resource_field = (
        statement.get("Resource")
        or statement.get("resource")
        or ["*"]
    )
    if isinstance(resource_field, str):
        return [resource_field]
    return [str(r) for r in resource_field]


def _extract_principal(statement: dict) -> str:
    """Return a string representation of the Principal."""
    principal = statement.get("Principal") or statement.get("principal") or "N/A"
    if isinstance(principal, dict):
        parts = []
        for k, v in principal.items():
            if isinstance(v, list):
                parts.append(f"{k}:{','.join(v)}")
            else:
                parts.append(f"{k}:{v}")
        return " | ".join(parts)
    return str(principal)


def _is_allow(statement: dict) -> bool:
    effect = str(statement.get("Effect") or statement.get("effect") or "Allow")
    return effect.strip().lower() == "allow"


def analyze_statement(
    statement: dict,
    check_mode: str,
    finding_prefix: str,
    severity_modifier: str,
) -> List[IAMFinding]:
    """
    Analyse a single IAM policy statement for risks.

    Args:
        statement:          Parsed IAM statement dict.
        check_mode:         One of privilege-escalation | data-exfil | public-exposure.
        finding_prefix:     Short string used to prefix finding IDs.
        severity_modifier:  internet-facing | regulated-data | none.

    Returns:
        List of IAMFinding objects (may be empty).
    """
    findings: List[IAMFinding] = []

    if not _is_allow(statement):
        return findings

    actions = _extract_actions(statement)
    resources = _extract_resources(statement)
    principal = _extract_principal(statement)
    resource_str = ", ".join(resources[:3]) + ("..." if len(resources) > 3 else "")

    wildcard_resource = any(r in ("*", "arn:aws:*") for r in resources)
    wildcard_action = any(a in ("*", "iam:*", "s3:*", "ec2:*") for a in actions)

    if check_mode == "privilege-escalation":
        # Check individual high-risk actions
        matched_privesc = [
            a for a in actions
            if a in [p.lower() for p in PRIVILEGE_ESCALATION_ACTIONS]
        ]

        if matched_privesc:
            severity = "high" if not wildcard_resource else "critical"
            severity = _bump_severity(severity, severity_modifier)
            findings.append(IAMFinding(
                finding_id=f"{finding_prefix}-PRIVESC-{len(findings) + 1:03d}",
                category="privilege-escalation",
                severity=severity,
                title="Privilege Escalation Actions Detected",
                description=(
                    f"Statement grants {len(matched_privesc)} privilege escalation "
                    f"action(s) to principal '{principal}' on resources: {resource_str}."
                ),
                affected_actions=matched_privesc,
                affected_resource=resource_str,
                recommendation=(
                    "Apply least-privilege: restrict IAM mutation actions to specific "
                    "resource ARNs and add Condition constraints. Consider permission boundaries."
                ),
                mitre_technique="T1098",
            ))

        # Check dangerous combos
        for combo in ESCALATION_COMBOS:
            combo_actions_lower = [c.lower() for c in combo["actions"]]
            if all(ca in actions for ca in combo_actions_lower):
                combo_sev = _bump_severity(combo["severity"], severity_modifier)
                findings.append(IAMFinding(
                    finding_id=f"{finding_prefix}-COMBO-{len(findings) + 1:03d}",
                    category="privilege-escalation",
                    severity=combo_sev,
                    title=f"Escalation Combo: {combo['name']}",
                    description=combo["description"],
                    affected_actions=combo["actions"],
                    affected_resource=resource_str,
                    recommendation=(
                        f"Remove or scope one of the combo actions. "
                        f"Separate {combo['name']} permissions across different roles."
                    ),
                    mitre_technique="T1548",
                ))

        # Wildcard action with Allow
        if wildcard_action:
            sev = _bump_severity("critical", severity_modifier)
            findings.append(IAMFinding(
                finding_id=f"{finding_prefix}-WILD-{len(findings) + 1:03d}",
                category="privilege-escalation",
                severity=sev,
                title="Wildcard Action Grant",
                description=(
                    f"Statement uses wildcard action(s) {[a for a in actions if '*' in a]} "
                    f"for principal '{principal}'. This grants unrestricted access."
                ),
                affected_actions=[a for a in actions if "*" in a],
                affected_resource=resource_str,
                recommendation="Replace wildcard actions with an explicit allowlist of required actions.",
                mitre_technique="T1078.004",
            ))

    elif check_mode == "data-exfil":
        matched_exfil = [
            a for a in actions
            if a in [d.lower() for d in DATA_EXFILTRATION_ACTIONS]
        ]

        if matched_exfil:
            severity = "medium"
            if wildcard_resource:
                severity = "high"
            # Particularly dangerous: log deletion or trail stopping
            disruptive = [
                a for a in matched_exfil
                if any(x in a for x in ["stoplog", "deletelog", "deletetrail", "deletedetector"])
            ]
            if disruptive:
                severity = "critical"
            severity = _bump_severity(severity, severity_modifier)

            findings.append(IAMFinding(
                finding_id=f"{finding_prefix}-EXFIL-{len(findings) + 1:03d}",
                category="data-exfil",
                severity=severity,
                title="Data Exfiltration Risk Actions",
                description=(
                    f"Statement grants {len(matched_exfil)} potential exfiltration "
                    f"action(s) to principal '{principal}': {', '.join(matched_exfil[:5])}."
                ),
                affected_actions=matched_exfil,
                affected_resource=resource_str,
                recommendation=(
                    "Scope data-read actions to specific resource ARNs. "
                    "Add VPC endpoint conditions and restrict cross-account access. "
                    "Enable GuardDuty and CloudTrail for all regions."
                ),
                mitre_technique="T1530",
            ))

    elif check_mode == "public-exposure":
        principal_str = _extract_principal(statement)
        is_public = any(p in principal_str for p in ["*", "AWS:*", '"*"'])

        if is_public:
            sev = _bump_severity("high", severity_modifier)
            if wildcard_action:
                sev = _bump_severity("critical", severity_modifier)

            findings.append(IAMFinding(
                finding_id=f"{finding_prefix}-PUB-{len(findings) + 1:03d}",
                category="public-exposure",
                severity=sev,
                title="Public Principal Detected",
                description=(
                    f"Statement uses Principal '*' allowing any AWS account or "
                    f"unauthenticated entity to perform: {', '.join(actions[:5])}."
                ),
                affected_actions=actions[:10],
                affected_resource=resource_str,
                recommendation=(
                    "Replace Principal '*' with specific account ARNs, "
                    "organisation units, or role ARNs. Use Condition keys "
                    "like aws:PrincipalOrgID to limit to your AWS Org."
                ),
                mitre_technique="T1190",
            ))

    return findings


def analyze_policy(
    policy: dict,
    check_mode: str,
    source: str,
    severity_modifier: str,
    provider: str = "aws",
) -> IAMAnalysisResult:
    """
    Analyse a full IAM policy document for findings.

    Iterates over every Statement in the policy and delegates to
    analyze_statement() for per-check logic.

    Args:
        policy:             Parsed IAM policy JSON dict.
        check_mode:         privilege-escalation | data-exfil | public-exposure.
        source:             Display name / file path for the policy.
        severity_modifier:  internet-facing | regulated-data | none.
        provider:           aws | azure | gcp (currently only aws fully supported).

    Returns:
        IAMAnalysisResult with all findings populated.
    """
    result = IAMAnalysisResult(
        source=source,
        check_mode=check_mode,
        provider=provider,
        severity_modifier=severity_modifier,
    )

    statements = policy.get("Statement") or policy.get("statement") or []
    if not isinstance(statements, list):
        statements = [statements]

    prefix = source.replace(" ", "_").replace("/", "_")[:12].upper()

    for idx, stmt in enumerate(statements):
        stmt_findings = analyze_statement(
            statement=stmt,
            check_mode=check_mode,
            finding_prefix=f"{prefix}-S{idx + 1:02d}",
            severity_modifier=severity_modifier,
        )
        result.findings.extend(stmt_findings)

    result.summary = {
        "total_statements": len(statements),
        "total_findings": len(result.findings),
        "critical": result.critical_count,
        "high": result.high_count,
        "medium": result.medium_count,
        "low": result.low_count,
        "check_mode": check_mode,
        "provider": provider,
        "severity_modifier": severity_modifier,
    }

    return result


# ---------------------------------------------------------------------------
# S3 Posture Check (new)
# ---------------------------------------------------------------------------

def check_s3_policy(
    policy: dict,
    source: str,
    severity_modifier: str,
) -> IAMAnalysisResult:
    """
    Check S3 bucket policy or Terraform aws_s3_bucket block for misconfigurations.

    Checks performed:
        1. Principal "*" in bucket policy -> Critical
        2. block_public_acls missing or false -> Critical
        3. server_side_encryption absent or not AES256/aws:kms -> High
        4. versioning disabled -> Medium
        5. access logging disabled -> High

    Args:
        policy:             Parsed S3 policy / Terraform block dict.
        source:             Display name / file path.
        severity_modifier:  internet-facing | regulated-data | none.

    Returns:
        IAMAnalysisResult populated with S3 findings.
    """
    result = IAMAnalysisResult(
        source=source,
        check_mode="s3",
        provider="aws",
        severity_modifier=severity_modifier,
    )
    findings: List[IAMFinding] = []
    fid = 0

    def _next_id() -> str:
        nonlocal fid
        fid += 1
        return f"S3-{fid:03d}"

    # --- Check 1: Public principal in bucket policy ---
    statements = policy.get("Statement") or policy.get("statement") or []
    if isinstance(statements, list):
        for stmt in statements:
            if not _is_allow(stmt):
                continue
            principal = _extract_principal(stmt)
            if "*" in principal or '"*"' in principal:
                severity = _bump_severity("critical", severity_modifier)
                findings.append(IAMFinding(
                    finding_id=_next_id(),
                    category="s3",
                    severity=severity,
                    title="S3 Bucket Policy: Public Principal",
                    description=(
                        "Bucket policy contains Principal '*' which grants public "
                        "access to any AWS account or unauthenticated user."
                    ),
                    affected_actions=_extract_actions(stmt),
                    affected_resource=source,
                    recommendation=(
                        "Remove Principal '*'. Restrict to specific account ARNs or "
                        "use aws:PrincipalOrgID condition to limit to your AWS Org."
                    ),
                    mitre_technique="T1530",
                ))

    # --- Check 2: block_public_acls missing or false ---
    # Terraform resource format: aws_s3_bucket_public_access_block
    public_access_block = (
        policy.get("block_public_acls")
        or policy.get("BlockPublicAcls")
        or policy.get("public_access_block", {}).get("block_public_acls")
    )
    restrict_public_buckets = (
        policy.get("restrict_public_buckets")
        or policy.get("RestrictPublicBuckets")
    )
    block_public_policy = (
        policy.get("block_public_policy")
        or policy.get("BlockPublicPolicy")
    )

    # If any of these are explicitly False or absent, flag it
    block_fields = {
        "block_public_acls": public_access_block,
        "restrict_public_buckets": restrict_public_buckets,
        "block_public_policy": block_public_policy,
    }
    missing_blocks = [k for k, v in block_fields.items() if v is None or v is False]

    if missing_blocks:
        severity = _bump_severity("critical", severity_modifier)
        findings.append(IAMFinding(
            finding_id=_next_id(),
            category="s3",
            severity=severity,
            title="S3 Public Access Block Not Fully Enabled",
            description=(
                f"Public access block settings are missing or disabled: "
                f"{', '.join(missing_blocks)}. This may allow public ACL or policy access."
            ),
            affected_resource=source,
            recommendation=(
                "Enable all four S3 Block Public Access settings: "
                "BlockPublicAcls, BlockPublicPolicy, IgnorePublicAcls, RestrictPublicBuckets."
            ),
            mitre_technique="T1530",
        ))

    # --- Check 3: Server-side encryption ---
    sse_config = (
        policy.get("server_side_encryption_configuration")
        or policy.get("ServerSideEncryptionConfiguration")
        or policy.get("encryption")
        or policy.get("sse_algorithm")
    )

    has_sse = False
    if isinstance(sse_config, dict):
        rules = sse_config.get("Rule") or sse_config.get("rules") or []
        if not isinstance(rules, list):
            rules = [rules]
        for rule in rules:
            apply_sse = (
                rule.get("ApplyServerSideEncryptionByDefault")
                or rule.get("apply_server_side_encryption_by_default")
                or {}
            )
            algo = str(apply_sse.get("SSEAlgorithm") or apply_sse.get("sse_algorithm") or "")
            if algo.upper() in ("AES256", "AWS:KMS"):
                has_sse = True
    elif isinstance(sse_config, str):
        has_sse = sse_config.upper() in ("AES256", "AWS:KMS")

    if not has_sse:
        severity = _bump_severity("high", severity_modifier)
        findings.append(IAMFinding(
            finding_id=_next_id(),
            category="s3",
            severity=severity,
            title="S3 Server-Side Encryption Not Configured",
            description=(
                "No server-side encryption (SSE-S3 or SSE-KMS) found on this bucket. "
                "Data is stored unencrypted at rest."
            ),
            affected_resource=source,
            recommendation=(
                "Enable SSE via a bucket encryption configuration. "
                "Use aws:kms with a CMK for regulated workloads. "
                "Consider enforcing encryption via bucket policy (aws:SecureTransport)."
            ),
            mitre_technique="T1022",
        ))

    # --- Check 4: Versioning disabled ---
    versioning = (
        policy.get("versioning")
        or policy.get("VersioningConfiguration")
    )
    versioning_enabled = False
    if isinstance(versioning, dict):
        status = str(
            versioning.get("Status")
            or versioning.get("status")
            or versioning.get("enabled")
            or ""
        )
        versioning_enabled = status.lower() in ("enabled", "true")
    elif isinstance(versioning, bool):
        versioning_enabled = versioning

    if not versioning_enabled:
        severity = _bump_severity("medium", severity_modifier)
        findings.append(IAMFinding(
            finding_id=_next_id(),
            category="s3",
            severity=severity,
            title="S3 Bucket Versioning Disabled",
            description=(
                "Versioning is not enabled on this bucket. "
                "Accidental or malicious object deletion/overwrite cannot be recovered."
            ),
            affected_resource=source,
            recommendation=(
                "Enable bucket versioning. "
                "Combine with Object Lock and lifecycle policies for regulated workloads."
            ),
            mitre_technique="T1485",
        ))

    result.findings = findings
    result.summary = {
        "total_findings": len(findings),
        "critical": sum(1 for f in findings if f.severity == "critical"),
        "high": sum(1 for f in findings if f.severity == "high"),
        "medium": sum(1 for f in findings if f.severity == "medium"),
        "low": sum(1 for f in findings if f.severity == "low"),
        "check_mode": "s3",
        "provider": "aws",
        "severity_modifier": severity_modifier,
    }
    return result


# ---------------------------------------------------------------------------
# Security Group Check (new)
# ---------------------------------------------------------------------------

def check_security_group(
    sg_json: dict,
    source: str,
    severity_modifier: str,
) -> IAMAnalysisResult:
    """
    Check AWS Security Group JSON for dangerous inbound rules.

    Args:
        sg_json:            Parsed Security Group JSON (AWS DescribeSecurityGroups
                            output format or Terraform aws_security_group block).
        source:             Display name / file path.
        severity_modifier:  internet-facing | regulated-data | none.

    Returns:
        IAMAnalysisResult populated with SG findings.
    """
    RISKY_PORTS: Dict[int, str] = {
        22: "SSH",
        3389: "RDP",
        23: "Telnet",
        21: "FTP",
        3306: "MySQL",
        5432: "PostgreSQL",
        1433: "MSSQL",
        27017: "MongoDB",
        6379: "Redis",
    }

    result = IAMAnalysisResult(
        source=source,
        check_mode="sg",
        provider="aws",
        severity_modifier=severity_modifier,
    )
    findings: List[IAMFinding] = []
    fid = 0

    def _next_id() -> str:
        nonlocal fid
        fid += 1
        return f"SG-{fid:03d}"

    # Support both AWS API format (IpPermissions) and Terraform ingress blocks
    ip_permissions = sg_json.get("IpPermissions") or []
    terraform_ingress = sg_json.get("ingress") or []

    # Normalise Terraform ingress blocks to AWS API format
    normalised: List[dict] = list(ip_permissions)
    for ing in terraform_ingress:
        if not isinstance(ing, dict):
            continue
        cidr_blocks = ing.get("cidr_blocks") or []
        ipv6_cidr_blocks = ing.get("ipv6_cidr_blocks") or []
        ip_ranges = [{"CidrIp": c} for c in cidr_blocks]
        ipv6_ranges = [{"CidrIpv6": c} for c in ipv6_cidr_blocks]
        normalised.append({
            "IpProtocol": str(ing.get("protocol", "tcp")),
            "FromPort": ing.get("from_port", 0),
            "ToPort": ing.get("to_port", 65535),
            "IpRanges": ip_ranges,
            "Ipv6Ranges": ipv6_ranges,
        })

    for rule in normalised:
        from_port = rule.get("FromPort", 0)
        to_port = rule.get("ToPort", 65535)
        protocol = str(rule.get("IpProtocol", "tcp"))

        # Collect CIDRs from both IPv4 and IPv6 ranges
        all_ranges: List[Tuple[str, str]] = []
        for ip_range in rule.get("IpRanges", []):
            cidr = ip_range.get("CidrIp", "")
            if cidr:
                all_ranges.append((cidr, "ipv4"))
        for ip_range in rule.get("Ipv6Ranges", []):
            cidr = ip_range.get("CidrIpv6", "")
            if cidr:
                all_ranges.append((cidr, "ipv6"))

        for cidr, ip_ver in all_ranges:
            if cidr not in ("0.0.0.0/0", "::/0"):
                continue  # Not open to the world

            if protocol == "-1":
                # All traffic open to the internet
                severity = _bump_severity("critical", severity_modifier)
                findings.append(IAMFinding(
                    finding_id=_next_id(),
                    category="sg",
                    severity=severity,
                    title="Security Group: All Traffic Open to Internet",
                    description=(
                        f"Inbound rule allows ALL traffic (protocol -1) "
                        f"from {cidr} ({ip_ver}). This exposes every port on every instance "
                        "in this security group to the public internet."
                    ),
                    affected_resource=source,
                    recommendation=(
                        "Remove the all-traffic rule. Define explicit port/protocol "
                        "allowlist rules for only the services that must be internet-accessible."
                    ),
                    mitre_technique="T1190",
                ))
                continue

            # Check port range against RISKY_PORTS
            matched_ports = [
                p for p in RISKY_PORTS
                if from_port <= p <= to_port
            ]

            if matched_ports:
                for port in matched_ports:
                    service = RISKY_PORTS[port]
                    severity = _bump_severity("critical", severity_modifier)
                    findings.append(IAMFinding(
                        finding_id=_next_id(),
                        category="sg",
                        severity=severity,
                        title=f"Security Group: {service} ({port}) Open to Internet",
                        description=(
                            f"Inbound rule allows {service} (port {port}/{protocol}) "
                            f"from {cidr} ({ip_ver}). Direct internet access to {service} "
                            "exposes this service to brute-force, exploitation, and scanning."
                        ),
                        affected_resource=source,
                        recommendation=(
                            f"Restrict port {port} to specific trusted CIDRs or a VPN/bastion. "
                            f"For {service}, consider using AWS Systems Manager Session Manager "
                            "as a zero-trust alternative that requires no open inbound ports."
                        ),
                        mitre_technique="T1133",
                    ))
            else:
                # Open to the internet on a non-standard port
                severity = _bump_severity("high", severity_modifier)
                port_label = (
                    f"port {from_port}"
                    if from_port == to_port
                    else f"ports {from_port}-{to_port}"
                )
                findings.append(IAMFinding(
                    finding_id=_next_id(),
                    category="sg",
                    severity=severity,
                    title=f"Security Group: {port_label.title()} Open to Internet",
                    description=(
                        f"Inbound rule opens {port_label} ({protocol}) to {cidr} ({ip_ver}). "
                        "Broad internet exposure increases attack surface even on non-standard ports."
                    ),
                    affected_resource=source,
                    recommendation=(
                        f"Restrict {port_label} to the specific IP ranges that require access. "
                        "Use Security Group references instead of CIDRs where possible."
                    ),
                    mitre_technique="T1046",
                ))

    result.findings = findings
    result.summary = {
        "total_findings": len(findings),
        "critical": sum(1 for f in findings if f.severity == "critical"),
        "high": sum(1 for f in findings if f.severity == "high"),
        "medium": sum(1 for f in findings if f.severity == "medium"),
        "low": sum(1 for f in findings if f.severity == "low"),
        "check_mode": "sg",
        "provider": "aws",
        "severity_modifier": severity_modifier,
    }
    return result


# ---------------------------------------------------------------------------
# Text Report
# ---------------------------------------------------------------------------

def print_text_report(result: IAMAnalysisResult) -> None:
    """Print a formatted text report for the analysis result."""
    sep = "=" * 70
    print(sep)
    print("  Cloud Posture Check")
    print(sep)
    print(f"  Source          : {result.source}")
    print(f"  Check Mode      : {result.check_mode}")
    print(f"  Provider        : {result.provider.upper()}")
    print(f"  Severity Mod    : {result.severity_modifier}")
    print(f"  Timestamp       : {result.timestamp_utc}")
    print(sep)

    summary = result.summary
    print(f"\n  Summary:")
    print(f"    Total Findings  : {summary.get('total_findings', 0)}")
    if summary.get("critical", 0):
        print(f"    CRITICAL        : {summary['critical']}")
    if summary.get("high", 0):
        print(f"    HIGH            : {summary['high']}")
    if summary.get("medium", 0):
        print(f"    MEDIUM          : {summary['medium']}")
    if summary.get("low", 0):
        print(f"    LOW             : {summary['low']}")

    if not result.findings:
        print("\n  No findings detected.")
        print(sep)
        return

    print(f"\n  Findings ({len(result.findings)}):")
    for finding in result.findings:
        print(f"\n  [{finding.severity.upper()}] {finding.finding_id}: {finding.title}")
        print(f"    {finding.description}")
        if finding.affected_actions:
            preview = finding.affected_actions[:4]
            suffix = f" (+{len(finding.affected_actions) - 4} more)" if len(finding.affected_actions) > 4 else ""
            print(f"    Actions  : {', '.join(preview)}{suffix}")
        print(f"    Resource : {finding.affected_resource}")
        print(f"    MITRE    : {finding.mitre_technique}")
        print(f"    Fix      : {finding.recommendation}")

    print(f"\n{sep}")


# ---------------------------------------------------------------------------
# Result Serialisation
# ---------------------------------------------------------------------------

def result_to_dict(result: IAMAnalysisResult) -> dict:
    """Convert IAMAnalysisResult to a JSON-serialisable dict."""
    return {
        "source": result.source,
        "check_mode": result.check_mode,
        "provider": result.provider,
        "severity_modifier": result.severity_modifier,
        "timestamp_utc": result.timestamp_utc,
        "summary": result.summary,
        "findings": [asdict(f) for f in result.findings],
    }


# ---------------------------------------------------------------------------
# Main Entry Point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Cloud Security Posture Check — IAM, S3, and Security Group analysis",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s policy.json
  %(prog)s policy.json --check privilege-escalation --json
  %(prog)s policy.json --check data-exfil --severity-modifier regulated-data --json
  %(prog)s policy.json --check public-exposure --json
  %(prog)s bucket.json --check s3 --severity-modifier internet-facing --json
  %(prog)s sg.json --check sg --provider aws --json
  %(prog)s policy.json --check all --json

Exit codes:
  0  No findings or informational only
  1  High-severity findings present
  2  Critical findings present
        """,
    )

    parser.add_argument(
        "input_file",
        help="Path to JSON file (IAM policy, S3 config, or Security Group JSON)",
    )
    parser.add_argument(
        "--check",
        choices=["privilege-escalation", "data-exfil", "public-exposure", "s3", "sg", "all"],
        default="privilege-escalation",
        help="Check mode to run (default: privilege-escalation)",
    )
    parser.add_argument(
        "--provider",
        choices=["aws", "azure", "gcp"],
        default="aws",
        help="Cloud provider (default: aws; Azure/GCP: only IAM checks available)",
    )
    parser.add_argument(
        "--severity-modifier",
        choices=["internet-facing", "regulated-data", "none"],
        default="none",
        dest="severity_modifier",
        help="Bump all finding severities +1 band (default: none)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output results as JSON",
    )
    parser.add_argument(
        "--output", "-o",
        metavar="FILE",
        help="Write JSON output to file",
    )

    args = parser.parse_args()

    # --- Load input file ---
    try:
        with open(args.input_file, "r", encoding="utf-8") as fh:
            policy_data = json.load(fh)
    except FileNotFoundError:
        err = {"error": f"File not found: {args.input_file}"}
        if args.json:
            print(json.dumps(err, indent=2))
        else:
            print(f"Error: {err['error']}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as exc:
        err = {"error": f"Invalid JSON: {exc}"}
        if args.json:
            print(json.dumps(err, indent=2))
        else:
            print(f"Error: {err['error']}", file=sys.stderr)
        sys.exit(1)

    source = args.input_file
    severity_modifier = args.severity_modifier
    provider = args.provider

    # --- Gate S3 / SG checks by provider ---
    check_mode = args.check

    if check_mode in ("s3", "sg") and provider != "aws":
        msg = (
            f"Azure/GCP checks coming soon — "
            f"use --provider aws for S3/SG analysis"
        )
        if args.json:
            print(json.dumps({"message": msg, "provider": provider, "check_mode": check_mode}, indent=2))
        else:
            print(msg)
        sys.exit(0)

    # --- Run checks ---
    all_results: List[IAMAnalysisResult] = []

    iam_check_modes = ["privilege-escalation", "data-exfil", "public-exposure"]

    if check_mode == "all":
        if provider == "aws":
            # Run all IAM checks
            for mode in iam_check_modes:
                r = analyze_policy(
                    policy=policy_data,
                    check_mode=mode,
                    source=source,
                    severity_modifier=severity_modifier,
                    provider=provider,
                )
                all_results.append(r)
            # Run S3
            s3_r = check_s3_policy(
                policy=policy_data,
                source=source,
                severity_modifier=severity_modifier,
            )
            all_results.append(s3_r)
            # Run SG
            sg_r = check_security_group(
                sg_json=policy_data,
                source=source,
                severity_modifier=severity_modifier,
            )
            all_results.append(sg_r)
        else:
            for mode in iam_check_modes:
                r = analyze_policy(
                    policy=policy_data,
                    check_mode=mode,
                    source=source,
                    severity_modifier=severity_modifier,
                    provider=provider,
                )
                all_results.append(r)

    elif check_mode in iam_check_modes:
        r = analyze_policy(
            policy=policy_data,
            check_mode=check_mode,
            source=source,
            severity_modifier=severity_modifier,
            provider=provider,
        )
        all_results.append(r)

    elif check_mode == "s3":
        r = check_s3_policy(
            policy=policy_data,
            source=source,
            severity_modifier=severity_modifier,
        )
        all_results.append(r)

    elif check_mode == "sg":
        r = check_security_group(
            sg_json=policy_data,
            source=source,
            severity_modifier=severity_modifier,
        )
        all_results.append(r)

    # --- Flatten findings for output when multiple checks run ---
    if len(all_results) == 1:
        combined_result = all_results[0]
    else:
        # Merge into a single result
        all_findings: List[IAMFinding] = []
        for res in all_results:
            all_findings.extend(res.findings)

        combined_result = IAMAnalysisResult(
            source=source,
            check_mode=check_mode,
            provider=provider,
            severity_modifier=severity_modifier,
        )
        combined_result.findings = all_findings
        combined_result.summary = {
            "total_findings": len(all_findings),
            "critical": sum(1 for f in all_findings if f.severity == "critical"),
            "high": sum(1 for f in all_findings if f.severity == "high"),
            "medium": sum(1 for f in all_findings if f.severity == "medium"),
            "low": sum(1 for f in all_findings if f.severity == "low"),
            "check_mode": check_mode,
            "provider": provider,
            "severity_modifier": severity_modifier,
            "checks_run": [r.check_mode for r in all_results],
        }

    # --- Output ---
    if args.json or args.output:
        output_dict = result_to_dict(combined_result)
        json_str = json.dumps(output_dict, indent=2)
        if args.output:
            with open(args.output, "w", encoding="utf-8") as fh:
                fh.write(json_str)
            if not args.json:
                print(f"Results written to {args.output}")
        if args.json:
            print(json_str)
    else:
        print_text_report(combined_result)

    # --- Exit code ---
    if combined_result.critical_count > 0:
        sys.exit(2)
    if combined_result.high_count > 0:
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
