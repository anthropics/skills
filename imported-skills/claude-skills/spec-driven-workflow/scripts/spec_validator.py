#!/usr/bin/env python3
"""
Spec Validator - Validates a feature specification for completeness and quality.

Checks that a spec document contains all required sections, uses RFC 2119 keywords
correctly, has acceptance criteria in Given/When/Then format, and scores overall
completeness from 0-100.

Sections checked:
- Context, Functional Requirements, Non-Functional Requirements
- Acceptance Criteria, Edge Cases, API Contracts, Data Models, Out of Scope

Exit codes: 0 = pass, 1 = warnings, 2 = critical (or --strict with score < 80)

No external dependencies - uses only Python standard library.
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Any, Tuple


# Section definitions: (key, display_name, required_header_patterns, weight)
SECTIONS = [
    ("context", "Context", [r"^##\s+Context"], 10),
    ("functional_requirements", "Functional Requirements", [r"^##\s+Functional\s+Requirements"], 15),
    ("non_functional_requirements", "Non-Functional Requirements", [r"^##\s+Non-Functional\s+Requirements"], 10),
    ("acceptance_criteria", "Acceptance Criteria", [r"^##\s+Acceptance\s+Criteria"], 20),
    ("edge_cases", "Edge Cases", [r"^##\s+Edge\s+Cases"], 10),
    ("api_contracts", "API Contracts", [r"^##\s+API\s+Contracts"], 10),
    ("data_models", "Data Models", [r"^##\s+Data\s+Models"], 10),
    ("out_of_scope", "Out of Scope", [r"^##\s+Out\s+of\s+Scope"], 10),
    ("metadata", "Metadata (Author/Date/Status)", [r"\*\*Author:\*\*", r"\*\*Date:\*\*", r"\*\*Status:\*\*"], 5),
]

RFC_KEYWORDS = ["MUST", "MUST NOT", "SHOULD", "SHOULD NOT", "MAY"]

# Patterns that indicate placeholder/unfilled content
PLACEHOLDER_PATTERNS = [
    r"\[your\s+name\]",
    r"\[list\s+reviewers\]",
    r"\[describe\s+",
    r"\[input/condition\]",
    r"\[precondition\]",
    r"\[action\]",
    r"\[expected\s+result\]",
    r"\[feature/capability\]",
    r"\[operation\]",
    r"\[threshold\]",
    r"\[UI\s+component\]",
    r"\[service\]",
    r"\[percentage\]",
    r"\[number\]",
    r"\[METHOD\]",
    r"\[endpoint\]",
    r"\[Name\]",
    r"\[Entity\s+Name\]",
    r"\[type\]",
    r"\[constraints\]",
    r"\[field\]",
    r"\[reason\]",
]


class SpecValidator:
    """Validates a spec document for completeness and quality."""

    def __init__(self, content: str, file_path: str = ""):
        self.content = content
        self.file_path = file_path
        self.lines = content.split("\n")
        self.findings: List[Dict[str, Any]] = []
        self.section_scores: Dict[str, Dict[str, Any]] = {}

    def validate(self) -> Dict[str, Any]:
        """Run all validation checks and return results."""
        self._check_sections_present()
        self._check_functional_requirements()
        self._check_acceptance_criteria()
        self._check_edge_cases()
        self._check_rfc_keywords()
        self._check_api_contracts()
        self._check_data_models()
        self._check_out_of_scope()
        self._check_placeholders()
        self._check_traceability()

        total_score = self._calculate_score()

        return {
            "file": self.file_path,
            "score": total_score,
            "grade": self._score_to_grade(total_score),
            "sections": self.section_scores,
            "findings": self.findings,
            "summary": self._build_summary(total_score),
        }

    def _add_finding(self, severity: str, section: str, message: str):
        """Record a validation finding."""
        self.findings.append({
            "severity": severity,  # "error", "warning", "info"
            "section": section,
            "message": message,
        })

    def _find_section_content(self, header_pattern: str) -> str:
        """Extract content between a section header and the next ## header."""
        in_section = False
        section_lines = []
        for line in self.lines:
            if re.match(header_pattern, line, re.IGNORECASE):
                in_section = True
                continue
            if in_section and re.match(r"^##\s+", line):
                break
            if in_section:
                section_lines.append(line)
        return "\n".join(section_lines)

    def _check_sections_present(self):
        """Check that all required sections exist."""
        for key, name, patterns, weight in SECTIONS:
            found = False
            for pattern in patterns:
                for line in self.lines:
                    if re.search(pattern, line, re.IGNORECASE):
                        found = True
                        break
                if found:
                    break

            if found:
                self.section_scores[key] = {"name": name, "present": True, "score": weight, "max": weight}
            else:
                self.section_scores[key] = {"name": name, "present": False, "score": 0, "max": weight}
                self._add_finding("error", key, f"Missing section: {name}")

    def _check_functional_requirements(self):
        """Validate functional requirements format and content."""
        content = self._find_section_content(r"^##\s+Functional\s+Requirements")
        if not content.strip():
            return

        fr_pattern = re.compile(r"-\s+FR-(\d+):")
        matches = fr_pattern.findall(content)

        if not matches:
            self._add_finding("error", "functional_requirements", "No numbered requirements found (expected FR-N: format)")
            if "functional_requirements" in self.section_scores:
                self.section_scores["functional_requirements"]["score"] = max(
                    0, self.section_scores["functional_requirements"]["score"] - 10
                )
            return

        fr_count = len(matches)
        if fr_count < 3:
            self._add_finding("warning", "functional_requirements", f"Only {fr_count} requirements found. Most features need 3+.")

        # Check for RFC keywords
        has_keyword = False
        for kw in RFC_KEYWORDS:
            if kw in content:
                has_keyword = True
                break
        if not has_keyword:
            self._add_finding("warning", "functional_requirements", "No RFC 2119 keywords (MUST/SHOULD/MAY) found.")

    def _check_acceptance_criteria(self):
        """Validate acceptance criteria use Given/When/Then format."""
        content = self._find_section_content(r"^##\s+Acceptance\s+Criteria")
        if not content.strip():
            return

        ac_pattern = re.compile(r"###\s+AC-(\d+):")
        matches = ac_pattern.findall(content)

        if not matches:
            self._add_finding("error", "acceptance_criteria", "No numbered acceptance criteria found (expected ### AC-N: format)")
            if "acceptance_criteria" in self.section_scores:
                self.section_scores["acceptance_criteria"]["score"] = max(
                    0, self.section_scores["acceptance_criteria"]["score"] - 15
                )
            return

        ac_count = len(matches)

        # Check Given/When/Then
        given_count = len(re.findall(r"(?i)\bgiven\b", content))
        when_count = len(re.findall(r"(?i)\bwhen\b", content))
        then_count = len(re.findall(r"(?i)\bthen\b", content))

        if given_count < ac_count:
            self._add_finding("warning", "acceptance_criteria",
                              f"Found {ac_count} criteria but only {given_count} 'Given' clauses. Each AC needs Given/When/Then.")
        if when_count < ac_count:
            self._add_finding("warning", "acceptance_criteria",
                              f"Found {ac_count} criteria but only {when_count} 'When' clauses.")
        if then_count < ac_count:
            self._add_finding("warning", "acceptance_criteria",
                              f"Found {ac_count} criteria but only {then_count} 'Then' clauses.")

        # Check for FR references
        fr_refs = re.findall(r"\(FR-\d+", content)
        if not fr_refs:
            self._add_finding("warning", "acceptance_criteria",
                              "No acceptance criteria reference functional requirements (expected (FR-N) in title).")

    def _check_edge_cases(self):
        """Validate edge cases section."""
        content = self._find_section_content(r"^##\s+Edge\s+Cases")
        if not content.strip():
            return

        ec_pattern = re.compile(r"-\s+EC-(\d+):")
        matches = ec_pattern.findall(content)

        if not matches:
            self._add_finding("warning", "edge_cases", "No numbered edge cases found (expected EC-N: format)")
        elif len(matches) < 3:
            self._add_finding("warning", "edge_cases", f"Only {len(matches)} edge cases. Consider failure modes for each external dependency.")

    def _check_rfc_keywords(self):
        """Check RFC 2119 keywords are used consistently (capitalized)."""
        # Look for lowercase must/should/may that might be intended as RFC keywords
        context_content = self._find_section_content(r"^##\s+Functional\s+Requirements")
        context_content += self._find_section_content(r"^##\s+Non-Functional\s+Requirements")

        for kw in ["must", "should", "may"]:
            # Find lowercase usage in requirement-like sentences
            pattern = rf"(?:system|service|API|endpoint)\s+{kw}\s+"
            if re.search(pattern, context_content):
                self._add_finding("warning", "rfc_keywords",
                                  f"Found lowercase '{kw}' in requirements. RFC 2119 keywords should be UPPERCASE: {kw.upper()}")

    def _check_api_contracts(self):
        """Validate API contracts section."""
        content = self._find_section_content(r"^##\s+API\s+Contracts")
        if not content.strip():
            return

        # Check for at least one endpoint definition
        has_endpoint = bool(re.search(r"(GET|POST|PUT|PATCH|DELETE)\s+/", content))
        if not has_endpoint:
            self._add_finding("warning", "api_contracts", "No HTTP method + path found (expected e.g., POST /api/endpoint)")

        # Check for request/response definitions
        has_interface = bool(re.search(r"interface\s+\w+", content))
        if not has_interface:
            self._add_finding("info", "api_contracts", "No TypeScript interfaces found. Consider defining request/response shapes.")

    def _check_data_models(self):
        """Validate data models section."""
        content = self._find_section_content(r"^##\s+Data\s+Models")
        if not content.strip():
            return

        # Check for table format
        has_table = bool(re.search(r"\|.*\|.*\|", content))
        if not has_table:
            self._add_finding("warning", "data_models", "No table-formatted data models found. Use | Field | Type | Constraints | format.")

    def _check_out_of_scope(self):
        """Validate out of scope section."""
        content = self._find_section_content(r"^##\s+Out\s+of\s+Scope")
        if not content.strip():
            return

        os_pattern = re.compile(r"-\s+OS-(\d+):")
        matches = os_pattern.findall(content)

        if not matches:
            self._add_finding("warning", "out_of_scope", "No numbered exclusions found (expected OS-N: format)")
        elif len(matches) < 2:
            self._add_finding("info", "out_of_scope", "Only 1 exclusion listed. Consider what was deliberately left out.")

    def _check_placeholders(self):
        """Check for unfilled placeholder text."""
        placeholder_count = 0
        for pattern in PLACEHOLDER_PATTERNS:
            matches = re.findall(pattern, self.content, re.IGNORECASE)
            placeholder_count += len(matches)

        if placeholder_count > 0:
            self._add_finding("warning", "placeholders",
                              f"Found {placeholder_count} placeholder(s) that need to be filled in (e.g., [your name], [describe ...]).")
            # Deduct from overall score proportionally
            for key in self.section_scores:
                if self.section_scores[key]["present"]:
                    deduction = min(3, self.section_scores[key]["score"])
                    self.section_scores[key]["score"] = max(0, self.section_scores[key]["score"] - deduction)

    def _check_traceability(self):
        """Check that acceptance criteria reference functional requirements."""
        ac_content = self._find_section_content(r"^##\s+Acceptance\s+Criteria")
        fr_content = self._find_section_content(r"^##\s+Functional\s+Requirements")

        if not ac_content.strip() or not fr_content.strip():
            return

        # Extract FR IDs
        fr_ids = set(re.findall(r"FR-(\d+)", fr_content))
        # Extract FR references from AC
        ac_fr_refs = set(re.findall(r"FR-(\d+)", ac_content))

        unreferenced = fr_ids - ac_fr_refs
        if unreferenced:
            unreferenced_list = ", ".join(f"FR-{i}" for i in sorted(unreferenced))
            self._add_finding("warning", "traceability",
                              f"Functional requirements without acceptance criteria: {unreferenced_list}")

    def _calculate_score(self) -> int:
        """Calculate the total completeness score."""
        total = sum(s["score"] for s in self.section_scores.values())
        maximum = sum(s["max"] for s in self.section_scores.values())

        if maximum == 0:
            return 0

        # Apply finding-based deductions
        error_count = sum(1 for f in self.findings if f["severity"] == "error")
        warning_count = sum(1 for f in self.findings if f["severity"] == "warning")

        base_score = round((total / maximum) * 100)
        deduction = (error_count * 5) + (warning_count * 2)

        return max(0, min(100, base_score - deduction))

    @staticmethod
    def _score_to_grade(score: int) -> str:
        """Convert score to letter grade."""
        if score >= 90:
            return "A"
        if score >= 80:
            return "B"
        if score >= 70:
            return "C"
        if score >= 60:
            return "D"
        return "F"

    def _build_summary(self, score: int) -> str:
        """Build human-readable summary."""
        errors = [f for f in self.findings if f["severity"] == "error"]
        warnings = [f for f in self.findings if f["severity"] == "warning"]
        infos = [f for f in self.findings if f["severity"] == "info"]

        lines = [
            f"Spec Completeness Score: {score}/100 (Grade: {self._score_to_grade(score)})",
            f"Errors: {len(errors)}, Warnings: {len(warnings)}, Info: {len(infos)}",
            "",
        ]

        if errors:
            lines.append("ERRORS (must fix):")
            for e in errors:
                lines.append(f"  [{e['section']}] {e['message']}")
            lines.append("")

        if warnings:
            lines.append("WARNINGS (should fix):")
            for w in warnings:
                lines.append(f"  [{w['section']}] {w['message']}")
            lines.append("")

        if infos:
            lines.append("INFO:")
            for i in infos:
                lines.append(f"  [{i['section']}] {i['message']}")
            lines.append("")

        # Section breakdown
        lines.append("Section Breakdown:")
        for key, data in self.section_scores.items():
            status = "PRESENT" if data["present"] else "MISSING"
            lines.append(f"  {data['name']}: {data['score']}/{data['max']} ({status})")

        return "\n".join(lines)


def format_human(result: Dict[str, Any]) -> str:
    """Format validation result for human reading."""
    lines = [
        "=" * 60,
        "SPEC VALIDATION REPORT",
        "=" * 60,
        "",
    ]
    if result["file"]:
        lines.append(f"File: {result['file']}")
        lines.append("")

    lines.append(result["summary"])

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Validate a feature specification for completeness and quality.",
        epilog="Example: python spec_validator.py --file spec.md --strict",
    )
    parser.add_argument(
        "--file",
        "-f",
        required=True,
        help="Path to the spec markdown file",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Exit with code 2 if score is below 80",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="json_flag",
        help="Output results as JSON",
    )

    args = parser.parse_args()

    file_path = Path(args.file)
    if not file_path.exists():
        print(f"Error: File not found: {file_path}", file=sys.stderr)
        sys.exit(2)

    content = file_path.read_text(encoding="utf-8")

    if not content.strip():
        print(f"Error: File is empty: {file_path}", file=sys.stderr)
        sys.exit(2)

    validator = SpecValidator(content, str(file_path))
    result = validator.validate()

    if args.json_flag:
        print(json.dumps(result, indent=2))
    else:
        print(format_human(result))

    # Determine exit code
    score = result["score"]
    has_errors = any(f["severity"] == "error" for f in result["findings"])
    has_warnings = any(f["severity"] == "warning" for f in result["findings"])

    if args.strict and score < 80:
        sys.exit(2)
    elif has_errors:
        sys.exit(2)
    elif has_warnings:
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()
