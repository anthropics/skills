#!/usr/bin/env python3
"""
terraform-patterns: Terraform Module Analyzer

Analyze a Terraform directory structure for module quality, resource counts,
naming conventions, and structural best practices. Reports variable/output
coverage, file organization, and actionable recommendations.

Usage:
    python scripts/tf_module_analyzer.py ./terraform
    python scripts/tf_module_analyzer.py ./terraform --output json
    python scripts/tf_module_analyzer.py ./modules/vpc
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path


# --- Demo Terraform Files ---

DEMO_FILES = {
    "main.tf": """
resource "aws_instance" "web_server" {
  ami           = var.ami_id
  instance_type = var.instance_type

  tags = {
    Name = "web-server"
  }
}

resource "aws_s3_bucket" "data" {
  bucket = "my-data-bucket-12345"
}

resource "aws_security_group" "web" {
  name = "web-sg"

  ingress {
    from_port   = 80
    to_port     = 80
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ingress {
    from_port   = 22
    to_port     = 22
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }
}

data "aws_ami" "ubuntu" {
  most_recent = true
  owners      = ["099720109477"]
}

module "vpc" {
  source = "./modules/vpc"
  cidr   = var.vpc_cidr
}
""",
    "variables.tf": """
variable "ami_id" {
  type = string
}

variable "instance_type" {
  default = "t3.micro"
}

variable "vpc_cidr" {
  description = "CIDR block for the VPC"
  type        = string
  default     = "10.0.0.0/16"
}

variable "environment" {
  description = "Deployment environment"
  type        = string
  validation {
    condition     = contains(["dev", "staging", "prod"], var.environment)
    error_message = "Environment must be dev, staging, or prod."
  }
}
""",
    "outputs.tf": """
output "instance_id" {
  value = aws_instance.web_server.id
}

output "bucket_arn" {
  value       = aws_s3_bucket.data.arn
  description = "ARN of the data S3 bucket"
}
""",
}

# --- Naming convention patterns ---

# Terraform resource naming: lowercase, underscores, alphanumeric
VALID_RESOURCE_NAME = re.compile(r'^[a-z][a-z0-9_]*$')

# Expected files in a well-structured module
EXPECTED_FILES = {
    "main.tf": "Primary resources",
    "variables.tf": "Input variables",
    "outputs.tf": "Output values",
    "versions.tf": "Provider and Terraform version requirements",
}

OPTIONAL_FILES = {
    "locals.tf": "Computed local values",
    "data.tf": "Data sources",
    "backend.tf": "Remote state backend configuration",
    "providers.tf": "Provider configuration",
    "README.md": "Module documentation",
}


def find_tf_files(directory):
    """Find all .tf files in a directory (non-recursive)."""
    tf_files = {}
    for entry in sorted(os.listdir(directory)):
        if entry.endswith(".tf"):
            filepath = os.path.join(directory, entry)
            with open(filepath, encoding="utf-8") as f:
                tf_files[entry] = f.read()
    return tf_files


def parse_resources(content):
    """Extract resource declarations from HCL content."""
    resources = []
    for match in re.finditer(
        r'^resource\s+"([^"]+)"\s+"([^"]+)"', content, re.MULTILINE
    ):
        resources.append({
            "type": match.group(1),
            "name": match.group(2),
            "provider": match.group(1).split("_")[0],
        })
    return resources


def parse_data_sources(content):
    """Extract data source declarations."""
    sources = []
    for match in re.finditer(
        r'^data\s+"([^"]+)"\s+"([^"]+)"', content, re.MULTILINE
    ):
        sources.append({"type": match.group(1), "name": match.group(2)})
    return sources


def parse_variables(content):
    """Extract variable declarations with metadata."""
    variables = []
    # Match variable blocks
    for match in re.finditer(
        r'^variable\s+"([^"]+)"\s*\{(.*?)\n\}',
        content,
        re.MULTILINE | re.DOTALL,
    ):
        name = match.group(1)
        body = match.group(2)
        var = {
            "name": name,
            "has_description": "description" in body,
            "has_type": bool(re.search(r'\btype\s*=', body)),
            "has_default": bool(re.search(r'\bdefault\s*=', body)),
            "has_validation": "validation" in body,
            "is_sensitive": "sensitive" in body and bool(
                re.search(r'\bsensitive\s*=\s*true', body)
            ),
        }
        variables.append(var)
    return variables


def parse_outputs(content):
    """Extract output declarations with metadata."""
    outputs = []
    for match in re.finditer(
        r'^output\s+"([^"]+)"\s*\{(.*?)\n\}',
        content,
        re.MULTILINE | re.DOTALL,
    ):
        name = match.group(1)
        body = match.group(2)
        out = {
            "name": name,
            "has_description": "description" in body,
            "is_sensitive": "sensitive" in body and bool(
                re.search(r'\bsensitive\s*=\s*true', body)
            ),
        }
        outputs.append(out)
    return outputs


def parse_modules(content):
    """Extract module calls."""
    modules = []
    for match in re.finditer(
        r'^module\s+"([^"]+)"\s*\{(.*?)\n\}',
        content,
        re.MULTILINE | re.DOTALL,
    ):
        name = match.group(1)
        body = match.group(2)
        source_match = re.search(r'source\s*=\s*"([^"]+)"', body)
        source = source_match.group(1) if source_match else "unknown"
        modules.append({"name": name, "source": source})
    return modules


def check_naming(resources, data_sources):
    """Check naming conventions."""
    issues = []
    for r in resources:
        if not VALID_RESOURCE_NAME.match(r["name"]):
            issues.append({
                "severity": "medium",
                "message": f"Resource '{r['type']}.{r['name']}' uses non-standard naming — use lowercase with underscores",
            })
        if r["name"].startswith(r["provider"] + "_"):
            issues.append({
                "severity": "low",
                "message": f"Resource '{r['type']}.{r['name']}' name repeats the provider prefix — redundant",
            })
    for d in data_sources:
        if not VALID_RESOURCE_NAME.match(d["name"]):
            issues.append({
                "severity": "medium",
                "message": f"Data source '{d['type']}.{d['name']}' uses non-standard naming",
            })
    return issues


def check_variables(variables):
    """Check variable quality."""
    issues = []
    for v in variables:
        if not v["has_description"]:
            issues.append({
                "severity": "medium",
                "message": f"Variable '{v['name']}' missing description — consumers won't know what to provide",
            })
        if not v["has_type"]:
            issues.append({
                "severity": "high",
                "message": f"Variable '{v['name']}' missing type constraint — accepts any value",
            })
        # Check if name suggests a secret
        secret_patterns = ["password", "secret", "token", "key", "api_key", "credentials"]
        name_lower = v["name"].lower()
        if any(p in name_lower for p in secret_patterns) and not v["is_sensitive"]:
            issues.append({
                "severity": "high",
                "message": f"Variable '{v['name']}' looks like a secret but is not marked sensitive = true",
            })
    return issues


def check_outputs(outputs):
    """Check output quality."""
    issues = []
    for o in outputs:
        if not o["has_description"]:
            issues.append({
                "severity": "low",
                "message": f"Output '{o['name']}' missing description",
            })
    return issues


def check_file_structure(tf_files):
    """Check if expected files are present."""
    issues = []
    filenames = set(tf_files.keys())
    for expected, purpose in EXPECTED_FILES.items():
        if expected not in filenames:
            issues.append({
                "severity": "medium" if expected != "versions.tf" else "high",
                "message": f"Missing '{expected}' — {purpose}",
            })
    return issues


def analyze_directory(tf_files):
    """Run full analysis on a set of .tf files."""
    all_content = "\n".join(tf_files.values())

    resources = parse_resources(all_content)
    data_sources = parse_data_sources(all_content)
    variables = parse_variables(all_content)
    outputs = parse_outputs(all_content)
    modules = parse_modules(all_content)

    # Collect findings
    findings = []
    findings.extend(check_file_structure(tf_files))
    findings.extend(check_naming(resources, data_sources))
    findings.extend(check_variables(variables))
    findings.extend(check_outputs(outputs))

    # Check for backend configuration
    has_backend = any(
        re.search(r'\bbackend\s+"', content)
        for content in tf_files.values()
    )
    if not has_backend:
        findings.append({
            "severity": "high",
            "message": "No remote backend configured — state is stored locally",
        })

    # Check for terraform required_version
    has_tf_version = any(
        re.search(r'required_version\s*=', content)
        for content in tf_files.values()
    )
    if not has_tf_version:
        findings.append({
            "severity": "medium",
            "message": "No required_version constraint — any Terraform version can be used",
        })

    # Providers in child modules check
    for filename, content in tf_files.items():
        if filename not in ("providers.tf", "versions.tf", "backend.tf"):
            if re.search(r'^provider\s+"', content, re.MULTILINE):
                findings.append({
                    "severity": "medium",
                    "message": f"Provider configuration found in '{filename}' — keep providers in root module only",
                })

    # Sort findings
    severity_order = {"critical": 0, "high": 1, "medium": 2, "low": 3}
    findings.sort(key=lambda f: severity_order.get(f["severity"], 4))

    # Unique providers
    providers = sorted(set(r["provider"] for r in resources))

    return {
        "files": sorted(tf_files.keys()),
        "file_count": len(tf_files),
        "resources": resources,
        "resource_count": len(resources),
        "data_sources": data_sources,
        "data_source_count": len(data_sources),
        "variables": variables,
        "variable_count": len(variables),
        "outputs": outputs,
        "output_count": len(outputs),
        "modules": modules,
        "module_count": len(modules),
        "providers": providers,
        "findings": findings,
    }


def generate_report(analysis, output_format="text"):
    """Generate analysis report."""
    findings = analysis["findings"]

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
        "files": analysis["files"],
        "resource_count": analysis["resource_count"],
        "data_source_count": analysis["data_source_count"],
        "variable_count": analysis["variable_count"],
        "output_count": analysis["output_count"],
        "module_count": analysis["module_count"],
        "providers": analysis["providers"],
        "findings": findings,
        "finding_counts": counts,
    }

    if output_format == "json":
        print(json.dumps(result, indent=2))
        return result

    # Text output
    print(f"\n{'=' * 60}")
    print(f"  Terraform Module Analysis Report")
    print(f"{'=' * 60}")
    print(f"  Score: {score}/100")
    print(f"  Files: {', '.join(analysis['files'])}")
    print(f"  Providers: {', '.join(analysis['providers']) if analysis['providers'] else 'none detected'}")
    print()
    print(f"  Resources: {analysis['resource_count']} | Data Sources: {analysis['data_source_count']}")
    print(f"  Variables: {analysis['variable_count']} | Outputs: {analysis['output_count']} | Modules: {analysis['module_count']}")
    print()
    print(f"  Findings: {counts['critical']} critical | {counts['high']} high | {counts['medium']} medium | {counts['low']} low")
    print(f"{'─' * 60}")

    for f in findings:
        icon = {"critical": "!!!", "high": "!!", "medium": "!", "low": "~"}.get(f["severity"], "?")
        print(f"\n  {icon} {f['severity'].upper()}")
        print(f"  {f['message']}")

    if not findings:
        print("\n  No issues found. Module structure looks good.")

    print(f"\n{'=' * 60}\n")
    return result


def main():
    parser = argparse.ArgumentParser(
        description="terraform-patterns: Terraform module analyzer"
    )
    parser.add_argument(
        "directory", nargs="?",
        help="Path to Terraform directory (omit for demo)",
    )
    parser.add_argument(
        "--output", "-o",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    args = parser.parse_args()

    if args.directory:
        dirpath = Path(args.directory)
        if not dirpath.is_dir():
            print(f"Error: Not a directory: {args.directory}", file=sys.stderr)
            sys.exit(1)
        tf_files = find_tf_files(str(dirpath))
        if not tf_files:
            print(f"Error: No .tf files found in {args.directory}", file=sys.stderr)
            sys.exit(1)
    else:
        print("No directory provided. Running demo analysis...\n")
        tf_files = DEMO_FILES

    analysis = analyze_directory(tf_files)
    generate_report(analysis, args.output)


if __name__ == "__main__":
    main()
