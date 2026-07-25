#!/usr/bin/env python3
"""
terraform-patterns: Terraform Security Scanner

Scan .tf files for common security issues including hardcoded secrets,
overly permissive IAM policies, open security groups, missing encryption,
and sensitive variable misuse.

Usage:
    python scripts/tf_security_scanner.py ./terraform
    python scripts/tf_security_scanner.py ./terraform --output json
    python scripts/tf_security_scanner.py ./terraform --strict
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path


# --- Demo Terraform File ---

DEMO_TF = """
provider "aws" {
  region     = "us-east-1"
  access_key = "AKIAIOSFODNN7EXAMPLE"
  secret_key = "wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY"
}

variable "db_password" {
  type    = string
  default = "supersecret123"
}

resource "aws_instance" "web" {
  ami           = "ami-12345678"
  instance_type = "t3.micro"

  tags = {
    Name = "web-server"
  }
}

resource "aws_security_group" "web" {
  name = "web-sg"

  ingress {
    from_port   = 22
    to_port     = 22
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ingress {
    from_port   = 0
    to_port     = 65535
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }

  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
}

resource "aws_iam_policy" "admin" {
  name = "admin-policy"

  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Effect   = "Allow"
        Action   = "*"
        Resource = "*"
      }
    ]
  })
}

resource "aws_s3_bucket" "data" {
  bucket = "my-data-bucket"
}

resource "aws_db_instance" "main" {
  engine               = "mysql"
  instance_class       = "db.t3.micro"
  password             = "hardcoded-password"
  publicly_accessible  = true
  skip_final_snapshot  = true
}
"""

# --- Security Rules ---

SECRET_PATTERNS = [
    {
        "id": "SEC001",
        "name": "aws_access_key",
        "severity": "critical",
        "pattern": r'(?:access_key|aws_access_key_id)\s*=\s*"(AKIA[A-Z0-9]{16})"',
        "message": "AWS access key hardcoded in configuration",
        "fix": "Use environment variables, AWS profiles, or IAM roles instead",
    },
    {
        "id": "SEC002",
        "name": "aws_secret_key",
        "severity": "critical",
        "pattern": r'(?:secret_key|aws_secret_access_key)\s*=\s*"[A-Za-z0-9/+=]{40}"',
        "message": "AWS secret key hardcoded in configuration",
        "fix": "Use environment variables, AWS profiles, or IAM roles instead",
    },
    {
        "id": "SEC003",
        "name": "generic_password",
        "severity": "critical",
        "pattern": r'(?:password|passwd)\s*=\s*"[^"]{4,}"',
        "message": "Password hardcoded in resource or provider configuration",
        "fix": "Use a variable with sensitive = true, or fetch from Vault/SSM/Secrets Manager",
    },
    {
        "id": "SEC004",
        "name": "generic_secret",
        "severity": "critical",
        "pattern": r'(?:secret|token|api_key)\s*=\s*"[^"]{8,}"',
        "message": "Secret or token hardcoded in configuration",
        "fix": "Use a sensitive variable or secrets manager",
    },
    {
        "id": "SEC005",
        "name": "private_key",
        "severity": "critical",
        "pattern": r'-----BEGIN (?:RSA |EC |DSA )?PRIVATE KEY-----',
        "message": "Private key embedded in Terraform configuration",
        "fix": "Reference key file with file() function or use secrets manager",
    },
]

IAM_PATTERNS = [
    {
        "id": "SEC010",
        "name": "iam_wildcard_action",
        "severity": "critical",
        "pattern": r'Action\s*=\s*"\*"',
        "message": "IAM policy with wildcard Action = \"*\" — grants all permissions",
        "fix": "Scope Action to specific services and operations",
    },
    {
        "id": "SEC011",
        "name": "iam_wildcard_resource",
        "severity": "high",
        "pattern": r'Resource\s*=\s*"\*"',
        "message": "IAM policy with wildcard Resource = \"*\" — applies to all resources",
        "fix": "Scope Resource to specific ARN patterns",
    },
    {
        "id": "SEC012",
        "name": "iam_star_star",
        "severity": "critical",
        "pattern": r'Action\s*=\s*"\*"[^}]*Resource\s*=\s*"\*"',
        "message": "IAM policy with Action=* AND Resource=* — effectively admin access",
        "fix": "Follow least-privilege: grant only the specific actions and resources needed",
    },
]

NETWORK_PATTERNS = [
    {
        "id": "SEC020",
        "name": "sg_ssh_open",
        "severity": "critical",
        "pattern": None,  # Custom check
        "message": "Security group allows SSH (port 22) from 0.0.0.0/0",
        "fix": "Restrict to known CIDR blocks, or use SSM Session Manager instead",
    },
    {
        "id": "SEC021",
        "name": "sg_rdp_open",
        "severity": "critical",
        "pattern": None,  # Custom check
        "message": "Security group allows RDP (port 3389) from 0.0.0.0/0",
        "fix": "Restrict to known CIDR blocks, or use a bastion host",
    },
    {
        "id": "SEC022",
        "name": "sg_all_ports",
        "severity": "critical",
        "pattern": None,  # Custom check
        "message": "Security group allows all ports (0-65535) from 0.0.0.0/0",
        "fix": "Open only the specific ports your application needs",
    },
]

ENCRYPTION_PATTERNS = [
    {
        "id": "SEC030",
        "name": "s3_no_encryption",
        "severity": "high",
        "pattern": None,  # Custom check
        "message": "S3 bucket without server-side encryption configuration",
        "fix": "Add aws_s3_bucket_server_side_encryption_configuration resource",
    },
    {
        "id": "SEC031",
        "name": "rds_no_encryption",
        "severity": "high",
        "pattern": None,  # Custom check
        "message": "RDS instance without storage encryption",
        "fix": "Set storage_encrypted = true on aws_db_instance",
    },
    {
        "id": "SEC032",
        "name": "ebs_no_encryption",
        "severity": "medium",
        "pattern": None,  # Custom check
        "message": "EBS volume without encryption",
        "fix": "Set encrypted = true on aws_ebs_volume or enable account-level default encryption",
    },
]

ACCESS_PATTERNS = [
    {
        "id": "SEC040",
        "name": "rds_public",
        "severity": "high",
        "pattern": r'publicly_accessible\s*=\s*true',
        "message": "RDS instance is publicly accessible",
        "fix": "Set publicly_accessible = false and access via VPC/bastion",
    },
    {
        "id": "SEC041",
        "name": "s3_public_acl",
        "severity": "high",
        "pattern": r'acl\s*=\s*"public-read(?:-write)?"',
        "message": "S3 bucket with public ACL",
        "fix": "Remove public ACL and add aws_s3_bucket_public_access_block",
    },
]


def find_tf_files(directory):
    """Find all .tf files in a directory (non-recursive)."""
    tf_files = {}
    for entry in sorted(os.listdir(directory)):
        if entry.endswith(".tf"):
            filepath = os.path.join(directory, entry)
            with open(filepath, encoding="utf-8") as f:
                tf_files[entry] = f.read()
    return tf_files


def check_regex_rules(content, rules):
    """Run regex-based security rules against content."""
    findings = []
    for rule in rules:
        if rule["pattern"] is None:
            continue
        for match in re.finditer(rule["pattern"], content, re.MULTILINE | re.IGNORECASE):
            findings.append({
                "id": rule["id"],
                "severity": rule["severity"],
                "message": rule["message"],
                "fix": rule["fix"],
                "line": match.group(0).strip()[:80],
            })
    return findings


def check_security_groups(content):
    """Custom check for open security groups."""
    findings = []

    # Parse ingress blocks within security group resources
    sg_blocks = re.finditer(
        r'resource\s+"aws_security_group"[^{]*\{(.*?)\n\}',
        content,
        re.DOTALL,
    )

    for sg_match in sg_blocks:
        sg_body = sg_match.group(1)
        ingress_blocks = re.finditer(
            r'ingress\s*\{(.*?)\}', sg_body, re.DOTALL
        )

        for ingress in ingress_blocks:
            block = ingress.group(1)
            has_open_cidr = '0.0.0.0/0' in block or '::/0' in block

            if not has_open_cidr:
                continue

            from_port_match = re.search(r'from_port\s*=\s*(\d+)', block)
            to_port_match = re.search(r'to_port\s*=\s*(\d+)', block)

            if from_port_match and to_port_match:
                from_port = int(from_port_match.group(1))
                to_port = int(to_port_match.group(1))

                # SSH open
                if from_port <= 22 <= to_port:
                    rule = next(r for r in NETWORK_PATTERNS if r["id"] == "SEC020")
                    findings.append({
                        "id": rule["id"],
                        "severity": rule["severity"],
                        "message": rule["message"],
                        "fix": rule["fix"],
                        "line": f"ingress port 22, cidr 0.0.0.0/0",
                    })

                # RDP open
                if from_port <= 3389 <= to_port:
                    rule = next(r for r in NETWORK_PATTERNS if r["id"] == "SEC021")
                    findings.append({
                        "id": rule["id"],
                        "severity": rule["severity"],
                        "message": rule["message"],
                        "fix": rule["fix"],
                        "line": f"ingress port 3389, cidr 0.0.0.0/0",
                    })

                # All ports open
                if from_port == 0 and to_port >= 65535:
                    rule = next(r for r in NETWORK_PATTERNS if r["id"] == "SEC022")
                    findings.append({
                        "id": rule["id"],
                        "severity": rule["severity"],
                        "message": rule["message"],
                        "fix": rule["fix"],
                        "line": f"ingress ports 0-65535, cidr 0.0.0.0/0",
                    })

    return findings


def check_encryption(content):
    """Custom check for missing encryption on storage resources."""
    findings = []

    # S3 buckets without encryption
    s3_buckets = re.findall(
        r'resource\s+"aws_s3_bucket"\s+"([^"]+)"', content
    )
    s3_encryption = re.findall(
        r'resource\s+"aws_s3_bucket_server_side_encryption_configuration"', content
    )
    # Also check inline encryption (older format)
    inline_encryption = re.findall(
        r'server_side_encryption_configuration', content
    )
    if s3_buckets and not s3_encryption and not inline_encryption:
        rule = next(r for r in ENCRYPTION_PATTERNS if r["id"] == "SEC030")
        for bucket in s3_buckets:
            findings.append({
                "id": rule["id"],
                "severity": rule["severity"],
                "message": f"{rule['message']} (bucket: {bucket})",
                "fix": rule["fix"],
                "line": f'aws_s3_bucket.{bucket}',
            })

    # RDS without encryption
    rds_blocks = re.finditer(
        r'resource\s+"aws_db_instance"\s+"([^"]+)"\s*\{(.*?)\n\}',
        content,
        re.DOTALL,
    )
    for rds_match in rds_blocks:
        name = rds_match.group(1)
        body = rds_match.group(2)
        if 'storage_encrypted' not in body or re.search(
            r'storage_encrypted\s*=\s*false', body
        ):
            rule = next(r for r in ENCRYPTION_PATTERNS if r["id"] == "SEC031")
            findings.append({
                "id": rule["id"],
                "severity": rule["severity"],
                "message": f"{rule['message']} (instance: {name})",
                "fix": rule["fix"],
                "line": f'aws_db_instance.{name}',
            })

    # EBS volumes without encryption
    ebs_blocks = re.finditer(
        r'resource\s+"aws_ebs_volume"\s+"([^"]+)"\s*\{(.*?)\n\}',
        content,
        re.DOTALL,
    )
    for ebs_match in ebs_blocks:
        name = ebs_match.group(1)
        body = ebs_match.group(2)
        if 'encrypted' not in body or re.search(
            r'encrypted\s*=\s*false', body
        ):
            rule = next(r for r in ENCRYPTION_PATTERNS if r["id"] == "SEC032")
            findings.append({
                "id": rule["id"],
                "severity": rule["severity"],
                "message": f"{rule['message']} (volume: {name})",
                "fix": rule["fix"],
                "line": f'aws_ebs_volume.{name}',
            })

    return findings


def check_sensitive_variables(content):
    """Check if variables that look like secrets are marked sensitive."""
    findings = []
    var_blocks = re.finditer(
        r'variable\s+"([^"]+)"\s*\{(.*?)\n\}',
        content,
        re.DOTALL,
    )
    secret_names = ["password", "secret", "token", "api_key", "private_key", "credentials"]

    for var_match in var_blocks:
        name = var_match.group(1)
        body = var_match.group(2)
        name_lower = name.lower()

        if any(s in name_lower for s in secret_names):
            if not re.search(r'sensitive\s*=\s*true', body):
                findings.append({
                    "id": "SEC050",
                    "severity": "medium",
                    "message": f"Variable '{name}' appears to be a secret but is not marked sensitive = true",
                    "fix": "Add sensitive = true to prevent the value from appearing in logs and plan output",
                    "line": f'variable "{name}"',
                })

            # Check for hardcoded default
            default_match = re.search(r'default\s*=\s*"([^"]+)"', body)
            if default_match and len(default_match.group(1)) > 0:
                findings.append({
                    "id": "SEC051",
                    "severity": "critical",
                    "message": f"Variable '{name}' has a hardcoded default value for a secret",
                    "fix": "Remove the default value — require it to be passed at runtime via tfvars or env",
                    "line": f'variable "{name}" default = "{default_match.group(1)[:20]}..."',
                })

    return findings


def scan_content(content, strict=False):
    """Run all security checks on content."""
    findings = []

    findings.extend(check_regex_rules(content, SECRET_PATTERNS))
    findings.extend(check_regex_rules(content, IAM_PATTERNS))
    findings.extend(check_regex_rules(content, ACCESS_PATTERNS))
    findings.extend(check_security_groups(content))
    findings.extend(check_encryption(content))
    findings.extend(check_sensitive_variables(content))

    if strict:
        for f in findings:
            if f["severity"] == "medium":
                f["severity"] = "high"
            elif f["severity"] == "low":
                f["severity"] = "medium"

    # Deduplicate by (id, line)
    seen = set()
    unique = []
    for f in findings:
        key = (f["id"], f.get("line", ""))
        if key not in seen:
            seen.add(key)
            unique.append(f)
    findings = unique

    # Sort by severity
    severity_order = {"critical": 0, "high": 1, "medium": 2, "low": 3}
    findings.sort(key=lambda f: severity_order.get(f["severity"], 4))

    return findings


def generate_report(content, output_format="text", strict=False):
    """Generate security scan report."""
    findings = scan_content(content, strict)

    # Score
    deductions = {"critical": 25, "high": 15, "medium": 5, "low": 2}
    score = max(0, 100 - sum(deductions.get(f["severity"], 0) for f in findings))

    counts = {
        "critical": sum(1 for f in findings if f["severity"] == "critical"),
        "high": sum(1 for f in findings if f["severity"] == "high"),
        "medium": sum(1 for f in findings if f["severity"] == "medium"),
        "low": sum(1 for f in findings if f["severity"] == "low"),
    }

    result = {
        "score": score,
        "findings": findings,
        "finding_counts": counts,
        "total_findings": len(findings),
    }

    if output_format == "json":
        print(json.dumps(result, indent=2))
        return result

    # Text output
    print(f"\n{'=' * 60}")
    print(f"  Terraform Security Scan Report")
    print(f"{'=' * 60}")
    print(f"  Score: {score}/100")
    print()
    print(f"  Findings: {counts['critical']} critical | {counts['high']} high | {counts['medium']} medium | {counts['low']} low")
    print(f"{'─' * 60}")

    for f in findings:
        icon = {"critical": "!!!", "high": "!!", "medium": "!", "low": "~"}.get(f["severity"], "?")
        print(f"\n  [{f['id']}] {icon} {f['severity'].upper()}")
        print(f"  {f['message']}")
        if f.get("line"):
            print(f"  Match: {f['line']}")
        print(f"  Fix:   {f['fix']}")

    if not findings:
        print("\n  No security issues found. Configuration looks clean.")

    print(f"\n{'=' * 60}\n")
    return result


def main():
    parser = argparse.ArgumentParser(
        description="terraform-patterns: Terraform security scanner"
    )
    parser.add_argument(
        "target", nargs="?",
        help="Path to Terraform directory or .tf file (omit for demo)",
    )
    parser.add_argument(
        "--output", "-o",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Strict mode — elevate warnings to higher severity",
    )
    args = parser.parse_args()

    if args.target:
        target = Path(args.target)
        if target.is_dir():
            tf_files = find_tf_files(str(target))
            if not tf_files:
                print(f"Error: No .tf files found in {args.target}", file=sys.stderr)
                sys.exit(1)
            content = "\n".join(tf_files.values())
        elif target.is_file() and target.suffix == ".tf":
            content = target.read_text(encoding="utf-8")
        else:
            print(f"Error: {args.target} is not a directory or .tf file", file=sys.stderr)
            sys.exit(1)
    else:
        print("No target provided. Running demo scan...\n")
        content = DEMO_TF

    generate_report(content, args.output, args.strict)


if __name__ == "__main__":
    main()
