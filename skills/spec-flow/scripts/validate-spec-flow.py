#!/usr/bin/env python3
"""
validate-spec-flow.py - Validate spec-flow completeness and consistency

Usage:
    python validate-spec-flow.py <spec-flow-directory>
    python validate-spec-flow.py .spec-flow/active/user-authentication

Exit codes:
    0 - All validations passed
    1 - Validation errors found
    2 - Invalid arguments or spec-flow not found
"""

import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional


@dataclass
class ValidationResult:
    """Result of a single validation check."""
    passed: bool
    message: str
    severity: str = "error"  # error, warning, info


@dataclass
class SpecValidation:
    """Complete validation results for a spec."""
    spec_path: Path
    results: List[ValidationResult]

    @property
    def has_errors(self) -> bool:
        return any(r.severity == "error" and not r.passed for r in self.results)

    @property
    def has_warnings(self) -> bool:
        return any(r.severity == "warning" and not r.passed for r in self.results)


def read_file(path: Path) -> Optional[str]:
    """Read file contents, return None if not found."""
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        return None
    except Exception as e:
        print(f"Error reading {path}: {e}", file=sys.stderr)
        return None


def validate_file_exists(spec_path: Path, filename: str) -> ValidationResult:
    """Check if a required file exists."""
    file_path = spec_path / filename
    if file_path.exists():
        return ValidationResult(True, f"✓ {filename} exists")
    return ValidationResult(False, f"✗ {filename} is missing", "error")


def validate_not_empty(spec_path: Path, filename: str) -> ValidationResult:
    """Check if a file has content beyond template placeholders."""
    file_path = spec_path / filename
    content = read_file(file_path)

    if content is None:
        return ValidationResult(False, f"✗ {filename} cannot be read", "error")

    # Remove comments and whitespace
    clean = re.sub(r'<!--.*?-->', '', content, flags=re.DOTALL)
    clean = re.sub(r'{{.*?}}', '', clean)  # Remove template placeholders
    clean = clean.strip()

    # Check if there's substantial content
    lines = [l for l in clean.split('\n') if l.strip() and not l.strip().startswith('#')]

    if len(lines) < 3:
        return ValidationResult(False, f"⚠ {filename} appears to have only template content", "warning")

    return ValidationResult(True, f"✓ {filename} has content")


def validate_proposal_sections(spec_path: Path) -> List[ValidationResult]:
    """Validate proposal.md has required sections."""
    results = []
    content = read_file(spec_path / "proposal.md")

    if content is None:
        return [ValidationResult(False, "✗ proposal.md cannot be read", "error")]

    required_sections = ["Background", "Goals", "Non-Goals", "Scope", "Risks"]

    for section in required_sections:
        if f"## {section}" in content or f"# {section}" in content:
            results.append(ValidationResult(True, f"✓ Proposal has {section} section"))
        else:
            results.append(ValidationResult(False, f"✗ Proposal missing {section} section", "error"))

    return results


def validate_requirements_format(spec_path: Path) -> List[ValidationResult]:
    """Validate requirements.md uses EARS format."""
    results = []
    content = read_file(spec_path / "requirements.md")

    if content is None:
        return [ValidationResult(False, "✗ requirements.md cannot be read", "error")]

    # Check for requirement IDs
    fr_pattern = r'FR-\d+'
    nfr_pattern = r'NFR-\d+'
    ac_pattern = r'AC-\d+'

    fr_count = len(re.findall(fr_pattern, content))
    nfr_count = len(re.findall(nfr_pattern, content))
    ac_count = len(re.findall(ac_pattern, content))

    if fr_count > 0:
        results.append(ValidationResult(True, f"✓ Found {fr_count} functional requirements"))
    else:
        results.append(ValidationResult(False, "✗ No functional requirements (FR-XXX) found", "warning"))

    if nfr_count > 0:
        results.append(ValidationResult(True, f"✓ Found {nfr_count} non-functional requirements"))
    else:
        results.append(ValidationResult(False, "⚠ No non-functional requirements (NFR-XXX) found", "warning"))

    if ac_count > 0:
        results.append(ValidationResult(True, f"✓ Found {ac_count} acceptance criteria"))
    else:
        results.append(ValidationResult(False, "✗ No acceptance criteria (AC-XXX) found", "error"))

    # Check for EARS keywords
    ears_keywords = ["shall", "When", "While", "If"]
    found_ears = any(kw in content for kw in ears_keywords)

    if found_ears:
        results.append(ValidationResult(True, "✓ Requirements use EARS format keywords"))
    else:
        results.append(ValidationResult(False, "⚠ Requirements may not follow EARS format", "warning"))

    return results


def validate_design_diagrams(spec_path: Path) -> List[ValidationResult]:
    """Validate design.md has diagrams."""
    results = []
    content = read_file(spec_path / "design.md")

    if content is None:
        return [ValidationResult(False, "✗ design.md cannot be read", "error")]

    # Check for Mermaid diagrams
    if "```mermaid" in content:
        mermaid_count = content.count("```mermaid")
        results.append(ValidationResult(True, f"✓ Found {mermaid_count} Mermaid diagram(s)"))
    else:
        results.append(ValidationResult(False, "⚠ No Mermaid diagrams found", "warning"))

    # Check for API section
    if "## API" in content or "### API" in content:
        results.append(ValidationResult(True, "✓ Design has API section"))
    else:
        results.append(ValidationResult(False, "⚠ Design may be missing API section", "warning"))

    return results


def validate_tasks_format(spec_path: Path) -> List[ValidationResult]:
    """Validate tasks.md has proper task format."""
    results = []
    content = read_file(spec_path / "tasks.md")

    if content is None:
        return [ValidationResult(False, "✗ tasks.md cannot be read", "error")]

    # Check for task IDs
    task_pattern = r'T-\d+'
    tasks = re.findall(task_pattern, content)

    if len(tasks) > 0:
        results.append(ValidationResult(True, f"✓ Found {len(tasks)} tasks"))
    else:
        results.append(ValidationResult(False, "✗ No tasks (T-XXX) found", "error"))

    # Check for complexity markers
    if "Complexity:" in content:
        results.append(ValidationResult(True, "✓ Tasks include complexity estimates"))
    else:
        results.append(ValidationResult(False, "⚠ Tasks may be missing complexity estimates", "warning"))

    # Check for dependencies
    if "Dependencies:" in content:
        results.append(ValidationResult(True, "✓ Tasks include dependency information"))
    else:
        results.append(ValidationResult(False, "⚠ Tasks may be missing dependencies", "warning"))

    # Check for progress tracking
    status_markers = ["⏳", "🔄", "✅", "❌", "Pending", "In Progress", "Done", "Blocked"]
    has_status = any(marker in content for marker in status_markers)

    if has_status:
        results.append(ValidationResult(True, "✓ Tasks have status markers"))
    else:
        results.append(ValidationResult(False, "⚠ Tasks may be missing status markers", "warning"))

    return results


def validate_meta_json(spec_path: Path) -> List[ValidationResult]:
    """Validate .meta.json file."""
    results = []
    meta_path = spec_path / ".meta.json"

    if not meta_path.exists():
        return [ValidationResult(False, "⚠ .meta.json not found (optional)", "info")]

    try:
        with open(meta_path) as f:
            meta = json.load(f)

        required_fields = ["feature", "status", "created", "phase"]
        for field in required_fields:
            if field in meta:
                results.append(ValidationResult(True, f"✓ .meta.json has {field}"))
            else:
                results.append(ValidationResult(False, f"⚠ .meta.json missing {field}", "warning"))

    except json.JSONDecodeError as e:
        results.append(ValidationResult(False, f"✗ .meta.json is invalid JSON: {e}", "error"))

    return results


def validate_spec(spec_path: Path) -> SpecValidation:
    """Run all validations on a spec directory."""
    results = []

    # Required files
    required_files = ["proposal.md", "requirements.md", "design.md", "tasks.md"]
    for filename in required_files:
        results.append(validate_file_exists(spec_path, filename))

    # Content checks
    for filename in required_files:
        results.append(validate_not_empty(spec_path, filename))

    # Structure checks
    results.extend(validate_proposal_sections(spec_path))
    results.extend(validate_requirements_format(spec_path))
    results.extend(validate_design_diagrams(spec_path))
    results.extend(validate_tasks_format(spec_path))
    results.extend(validate_meta_json(spec_path))

    return SpecValidation(spec_path, results)


def print_results(validation: SpecValidation) -> None:
    """Print validation results with colors."""
    # ANSI colors
    RED = "\033[0;31m"
    GREEN = "\033[0;32m"
    YELLOW = "\033[1;33m"
    BLUE = "\033[0;34m"
    NC = "\033[0m"

    print(f"\n{BLUE}Validating spec: {validation.spec_path}{NC}\n")

    errors = 0
    warnings = 0

    for result in validation.results:
        if result.passed:
            print(f"  {GREEN}{result.message}{NC}")
        elif result.severity == "error":
            print(f"  {RED}{result.message}{NC}")
            errors += 1
        elif result.severity == "warning":
            print(f"  {YELLOW}{result.message}{NC}")
            warnings += 1
        else:
            print(f"  {result.message}")

    print()
    if errors == 0 and warnings == 0:
        print(f"{GREEN}✅ All validations passed!{NC}")
    elif errors == 0:
        print(f"{YELLOW}⚠ Passed with {warnings} warning(s){NC}")
    else:
        print(f"{RED}❌ Failed with {errors} error(s) and {warnings} warning(s){NC}")


def main():
    if len(sys.argv) < 2:
        print("Usage: python validate-spec-flow.py <spec-flow-directory>")
        print("Example: python validate-spec-flow.py .spec-flow/active/user-authentication")
        sys.exit(2)

    spec_path = Path(sys.argv[1])

    if not spec_path.exists():
        print(f"Error: Spec-flow directory not found: {spec_path}", file=sys.stderr)
        sys.exit(2)

    if not spec_path.is_dir():
        print(f"Error: Not a directory: {spec_path}", file=sys.stderr)
        sys.exit(2)

    validation = validate_spec(spec_path)
    print_results(validation)

    sys.exit(1 if validation.has_errors else 0)


if __name__ == "__main__":
    main()
