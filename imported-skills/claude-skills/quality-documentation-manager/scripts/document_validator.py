#!/usr/bin/env python3
"""
Document Validator - Quality Documentation Compliance Checker

Validates document metadata, numbering conventions, and control requirements
for ISO 13485 and 21 CFR Part 11 compliance.

Usage:
    python document_validator.py --doc document.json
    python document_validator.py --interactive
    python document_validator.py --doc document.json --output json
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta
from typing import List, Dict, Optional, Tuple
from enum import Enum


class DocumentType(Enum):
    QM = "Quality Manual"
    SOP = "Standard Operating Procedure"
    WI = "Work Instruction"
    TF = "Template/Form"
    POL = "Policy"
    SPEC = "Specification"
    PLN = "Plan"
    RPT = "Report"


class DocumentStatus(Enum):
    DRAFT = "Draft"
    REVIEW = "Under Review"
    APPROVED = "Approved"
    EFFECTIVE = "Effective"
    SUPERSEDED = "Superseded"
    OBSOLETE = "Obsolete"


class Severity(Enum):
    CRITICAL = "Critical"
    MAJOR = "Major"
    MINOR = "Minor"
    INFO = "Info"


@dataclass
class ValidationFinding:
    rule: str
    severity: Severity
    message: str
    recommendation: str


@dataclass
class Document:
    number: str
    title: str
    doc_type: str
    revision: str
    status: str
    effective_date: Optional[str] = None
    review_date: Optional[str] = None
    author: Optional[str] = None
    approver: Optional[str] = None
    approval_date: Optional[str] = None
    change_history: List[Dict] = field(default_factory=list)
    has_audit_trail: bool = False
    has_electronic_signature: bool = False
    signature_components: int = 0


@dataclass
class ValidationResult:
    document_number: str
    validation_date: str
    total_findings: int
    critical_findings: int
    major_findings: int
    minor_findings: int
    compliance_score: float
    findings: List[Dict]
    recommendations: List[str]


class DocumentValidator:
    """Validator for quality documentation compliance."""

    # Document number pattern: PREFIX-CATEGORY-SEQUENCE-REVISION
    DOC_NUMBER_PATTERN = r'^([A-Z]{2,4})-(\d{2,3})-(\d{3,4})(?:-([A-Z]|\d{2}))?$'

    # Valid document type prefixes
    VALID_PREFIXES = ['QM', 'SOP', 'WI', 'TF', 'POL', 'SPEC', 'PLN', 'RPT']

    # Category codes
    VALID_CATEGORIES = ['01', '02', '03', '04', '05', '06', '07', '08', '09', '10']

    def __init__(self, document: Document):
        self.document = document
        self.today = datetime.now()
        self.findings: List[ValidationFinding] = []

    def validate(self) -> ValidationResult:
        """Run all validation checks."""
        self._validate_document_number()
        self._validate_title()
        self._validate_status_lifecycle()
        self._validate_dates()
        self._validate_approvals()
        self._validate_change_history()
        self._validate_electronic_controls()

        # Calculate compliance score
        score = self._calculate_compliance_score()

        # Generate recommendations
        recommendations = self._generate_recommendations()

        # Count findings by severity
        critical = len([f for f in self.findings if f.severity == Severity.CRITICAL])
        major = len([f for f in self.findings if f.severity == Severity.MAJOR])
        minor = len([f for f in self.findings if f.severity == Severity.MINOR])

        return ValidationResult(
            document_number=self.document.number,
            validation_date=self.today.strftime("%Y-%m-%d"),
            total_findings=len(self.findings),
            critical_findings=critical,
            major_findings=major,
            minor_findings=minor,
            compliance_score=round(score, 1),
            findings=[asdict(f) for f in self.findings],
            recommendations=recommendations
        )

    def _validate_document_number(self):
        """Validate document numbering convention."""
        number = self.document.number

        if not number:
            self.findings.append(ValidationFinding(
                rule="DOC-NUM-001",
                severity=Severity.CRITICAL,
                message="Document number is missing",
                recommendation="Assign document number per numbering procedure"
            ))
            return

        match = re.match(self.DOC_NUMBER_PATTERN, number)
        if not match:
            self.findings.append(ValidationFinding(
                rule="DOC-NUM-002",
                severity=Severity.MAJOR,
                message=f"Document number '{number}' does not match standard format",
                recommendation="Use format: PREFIX-CATEGORY-SEQUENCE[-REVISION] (e.g., SOP-02-001-A)"
            ))
            return

        prefix, category, sequence, revision = match.groups()

        if prefix not in self.VALID_PREFIXES:
            self.findings.append(ValidationFinding(
                rule="DOC-NUM-003",
                severity=Severity.MAJOR,
                message=f"Invalid document type prefix: {prefix}",
                recommendation=f"Use one of: {', '.join(self.VALID_PREFIXES)}"
            ))

        if category not in self.VALID_CATEGORIES:
            self.findings.append(ValidationFinding(
                rule="DOC-NUM-004",
                severity=Severity.MINOR,
                message=f"Non-standard category code: {category}",
                recommendation=f"Standard categories are: {', '.join(self.VALID_CATEGORIES)}"
            ))

    def _validate_title(self):
        """Validate document title."""
        title = self.document.title

        if not title:
            self.findings.append(ValidationFinding(
                rule="DOC-TTL-001",
                severity=Severity.MAJOR,
                message="Document title is missing",
                recommendation="Provide descriptive document title"
            ))
            return

        if len(title) < 10:
            self.findings.append(ValidationFinding(
                rule="DOC-TTL-002",
                severity=Severity.MINOR,
                message="Document title is very short",
                recommendation="Use descriptive title that clearly identifies content"
            ))

        if len(title) > 100:
            self.findings.append(ValidationFinding(
                rule="DOC-TTL-003",
                severity=Severity.MINOR,
                message="Document title exceeds recommended length",
                recommendation="Keep title under 100 characters"
            ))

    def _validate_status_lifecycle(self):
        """Validate document status and lifecycle."""
        status = self.document.status

        if not status:
            self.findings.append(ValidationFinding(
                rule="DOC-STS-001",
                severity=Severity.MAJOR,
                message="Document status is missing",
                recommendation="Assign appropriate document status"
            ))
            return

        valid_statuses = [s.value for s in DocumentStatus]
        if status not in valid_statuses:
            self.findings.append(ValidationFinding(
                rule="DOC-STS-002",
                severity=Severity.MAJOR,
                message=f"Invalid document status: {status}",
                recommendation=f"Use one of: {', '.join(valid_statuses)}"
            ))

        # Check status-specific requirements
        if status == DocumentStatus.EFFECTIVE.value:
            if not self.document.effective_date:
                self.findings.append(ValidationFinding(
                    rule="DOC-STS-003",
                    severity=Severity.MAJOR,
                    message="Effective document missing effective date",
                    recommendation="Add effective date for effective documents"
                ))

        if status == DocumentStatus.APPROVED.value:
            if not self.document.approval_date:
                self.findings.append(ValidationFinding(
                    rule="DOC-STS-004",
                    severity=Severity.MAJOR,
                    message="Approved document missing approval date",
                    recommendation="Add approval date for approved documents"
                ))

    def _validate_dates(self):
        """Validate document dates."""
        # Check effective date
        if self.document.effective_date:
            try:
                eff_date = datetime.strptime(self.document.effective_date, "%Y-%m-%d")
                if eff_date > self.today:
                    self.findings.append(ValidationFinding(
                        rule="DOC-DTE-001",
                        severity=Severity.INFO,
                        message="Effective date is in the future",
                        recommendation="Verify planned effective date is correct"
                    ))
            except ValueError:
                self.findings.append(ValidationFinding(
                    rule="DOC-DTE-002",
                    severity=Severity.MINOR,
                    message="Invalid effective date format",
                    recommendation="Use YYYY-MM-DD format for dates"
                ))

        # Check review date
        if self.document.review_date:
            try:
                review_date = datetime.strptime(self.document.review_date, "%Y-%m-%d")
                if review_date < self.today:
                    self.findings.append(ValidationFinding(
                        rule="DOC-DTE-003",
                        severity=Severity.MAJOR,
                        message="Document is overdue for review",
                        recommendation="Initiate periodic review process"
                    ))
                elif review_date < self.today + timedelta(days=30):
                    self.findings.append(ValidationFinding(
                        rule="DOC-DTE-004",
                        severity=Severity.MINOR,
                        message="Document review due within 30 days",
                        recommendation="Plan for upcoming review"
                    ))
            except ValueError:
                self.findings.append(ValidationFinding(
                    rule="DOC-DTE-005",
                    severity=Severity.MINOR,
                    message="Invalid review date format",
                    recommendation="Use YYYY-MM-DD format for dates"
                ))
        else:
            if self.document.status == DocumentStatus.EFFECTIVE.value:
                self.findings.append(ValidationFinding(
                    rule="DOC-DTE-006",
                    severity=Severity.MINOR,
                    message="Effective document missing review date",
                    recommendation="Add next review date (typically 1-3 years from effective)"
                ))

    def _validate_approvals(self):
        """Validate document approval information."""
        if self.document.status in [DocumentStatus.APPROVED.value, DocumentStatus.EFFECTIVE.value]:
            if not self.document.author:
                self.findings.append(ValidationFinding(
                    rule="DOC-APR-001",
                    severity=Severity.MAJOR,
                    message="Document author not identified",
                    recommendation="Document author on signature page"
                ))

            if not self.document.approver:
                self.findings.append(ValidationFinding(
                    rule="DOC-APR-002",
                    severity=Severity.CRITICAL,
                    message="Document approver not identified",
                    recommendation="Obtain required approval signatures"
                ))

    def _validate_change_history(self):
        """Validate change history completeness."""
        history = self.document.change_history

        if not history:
            self.findings.append(ValidationFinding(
                rule="DOC-CHG-001",
                severity=Severity.MAJOR,
                message="Document change history is missing",
                recommendation="Include change history table with revision descriptions"
            ))
            return

        for i, entry in enumerate(history):
            if not entry.get('revision'):
                self.findings.append(ValidationFinding(
                    rule="DOC-CHG-002",
                    severity=Severity.MINOR,
                    message=f"Change history entry {i+1} missing revision number",
                    recommendation="Include revision number for each history entry"
                ))

            if not entry.get('description'):
                self.findings.append(ValidationFinding(
                    rule="DOC-CHG-003",
                    severity=Severity.MINOR,
                    message=f"Change history entry {i+1} missing description",
                    recommendation="Include description of changes for each revision"
                ))

            if not entry.get('date'):
                self.findings.append(ValidationFinding(
                    rule="DOC-CHG-004",
                    severity=Severity.MINOR,
                    message=f"Change history entry {i+1} missing date",
                    recommendation="Include date for each history entry"
                ))

    def _validate_electronic_controls(self):
        """Validate 21 CFR Part 11 requirements for electronic documents."""
        # Audit trail check
        if not self.document.has_audit_trail:
            self.findings.append(ValidationFinding(
                rule="P11-AUD-001",
                severity=Severity.MAJOR,
                message="Electronic document lacks audit trail",
                recommendation="Enable audit trail for 21 CFR Part 11 compliance"
            ))

        # Electronic signature check
        if self.document.has_electronic_signature:
            if self.document.signature_components < 2:
                self.findings.append(ValidationFinding(
                    rule="P11-SIG-001",
                    severity=Severity.CRITICAL,
                    message="Electronic signature uses fewer than 2 identification components",
                    recommendation="Use at least 2 components (e.g., user ID + password)"
                ))
        else:
            if self.document.status in [DocumentStatus.APPROVED.value, DocumentStatus.EFFECTIVE.value]:
                self.findings.append(ValidationFinding(
                    rule="P11-SIG-002",
                    severity=Severity.INFO,
                    message="Document uses handwritten signatures",
                    recommendation="Consider electronic signatures for efficiency"
                ))

    def _calculate_compliance_score(self) -> float:
        """Calculate compliance score based on findings."""
        if not self.findings:
            return 100.0

        # Weight by severity
        deductions = {
            Severity.CRITICAL: 25,
            Severity.MAJOR: 10,
            Severity.MINOR: 3,
            Severity.INFO: 0
        }

        total_deduction = sum(deductions[f.severity] for f in self.findings)
        score = max(0, 100 - total_deduction)

        return score

    def _generate_recommendations(self) -> List[str]:
        """Generate prioritized recommendations."""
        recommendations = []

        # Critical findings
        critical = [f for f in self.findings if f.severity == Severity.CRITICAL]
        if critical:
            recommendations.append(
                f"URGENT: {len(critical)} critical finding(s) require immediate attention"
            )

        # Major findings
        major = [f for f in self.findings if f.severity == Severity.MAJOR]
        if major:
            recommendations.append(
                f"ACTION: {len(major)} major finding(s) should be addressed within 30 days"
            )

        # Review overdue
        review_overdue = [f for f in self.findings if f.rule == "DOC-DTE-003"]
        if review_overdue:
            recommendations.append(
                "REVIEW: Document is overdue for periodic review. Initiate review process."
            )

        # Part 11 gaps
        p11_findings = [f for f in self.findings if f.rule.startswith("P11")]
        if p11_findings:
            recommendations.append(
                f"COMPLIANCE: {len(p11_findings)} 21 CFR Part 11 gap(s) identified"
            )

        if not recommendations:
            recommendations.append("Document passes validation checks")

        return recommendations


def format_text_output(result: ValidationResult) -> str:
    """Format validation result as text report."""
    lines = [
        "=" * 70,
        "DOCUMENT VALIDATION REPORT",
        "=" * 70,
        f"Document: {result.document_number}",
        f"Validation Date: {result.validation_date}",
        f"Compliance Score: {result.compliance_score}%",
        "",
        "FINDINGS SUMMARY",
        "-" * 40,
        f"  Critical: {result.critical_findings}",
        f"  Major:    {result.major_findings}",
        f"  Minor:    {result.minor_findings}",
        f"  Total:    {result.total_findings}",
    ]

    if result.findings:
        lines.extend([
            "",
            "DETAILED FINDINGS",
            "-" * 40,
        ])

        for finding in result.findings:
            severity = finding['severity']
            lines.append(f"\n[{severity}] {finding['rule']}")
            lines.append(f"  Issue: {finding['message']}")
            lines.append(f"  Action: {finding['recommendation']}")

    lines.extend([
        "",
        "RECOMMENDATIONS",
        "-" * 40,
    ])

    for i, rec in enumerate(result.recommendations, 1):
        lines.append(f"{i}. {rec}")

    lines.append("=" * 70)
    return "\n".join(lines)


def interactive_mode():
    """Run interactive document validation."""
    print("=" * 60)
    print("Document Validator - Interactive Mode")
    print("=" * 60)

    print("\nEnter document information:\n")

    number = input("Document Number (e.g., SOP-02-001): ").strip()
    title = input("Document Title: ").strip()

    print("\nDocument Types: QM, SOP, WI, TF, POL, SPEC, PLN, RPT")
    doc_type = input("Document Type: ").strip().upper()

    revision = input("Revision (e.g., 01 or A): ").strip()

    print("\nStatuses: Draft, Under Review, Approved, Effective, Superseded, Obsolete")
    status = input("Status: ").strip()

    effective_date = input("Effective Date (YYYY-MM-DD, or Enter to skip): ").strip() or None
    review_date = input("Next Review Date (YYYY-MM-DD, or Enter to skip): ").strip() or None

    author = input("Author Name (or Enter to skip): ").strip() or None
    approver = input("Approver Name (or Enter to skip): ").strip() or None

    has_audit = input("Has Audit Trail? (y/n): ").strip().lower() == 'y'
    has_esig = input("Uses Electronic Signatures? (y/n): ").strip().lower() == 'y'

    sig_components = 0
    if has_esig:
        sig_input = input("Number of signature components (e.g., 2): ").strip()
        sig_components = int(sig_input) if sig_input.isdigit() else 0

    doc = Document(
        number=number,
        title=title,
        doc_type=doc_type,
        revision=revision,
        status=status,
        effective_date=effective_date,
        review_date=review_date,
        author=author,
        approver=approver,
        has_audit_trail=has_audit,
        has_electronic_signature=has_esig,
        signature_components=sig_components
    )

    validator = DocumentValidator(doc)
    result = validator.validate()
    print("\n" + format_text_output(result))


def main():
    parser = argparse.ArgumentParser(
        description="Quality Documentation Validator"
    )
    parser.add_argument(
        "--doc",
        type=str,
        help="JSON file with document metadata"
    )
    parser.add_argument(
        "--output",
        choices=["text", "json"],
        default="text",
        help="Output format"
    )
    parser.add_argument(
        "--interactive",
        action="store_true",
        help="Run in interactive mode"
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Generate sample document JSON"
    )

    args = parser.parse_args()

    if args.interactive:
        interactive_mode()
        return

    if args.sample:
        sample = {
            "number": "SOP-02-001",
            "title": "Document Control Procedure",
            "doc_type": "SOP",
            "revision": "03",
            "status": "Effective",
            "effective_date": "2024-01-15",
            "review_date": "2025-01-15",
            "author": "J. Smith",
            "approver": "M. Jones",
            "approval_date": "2024-01-10",
            "change_history": [
                {"revision": "01", "date": "2022-01-01", "description": "Initial release"},
                {"revision": "02", "date": "2023-01-15", "description": "Updated approval workflow"},
                {"revision": "03", "date": "2024-01-15", "description": "Added electronic signature requirements"}
            ],
            "has_audit_trail": True,
            "has_electronic_signature": True,
            "signature_components": 2
        }
        print(json.dumps(sample, indent=2))
        return

    if args.doc:
        with open(args.doc, "r") as f:
            data = json.load(f)

        doc = Document(
            number=data.get("number", ""),
            title=data.get("title", ""),
            doc_type=data.get("doc_type", ""),
            revision=data.get("revision", ""),
            status=data.get("status", ""),
            effective_date=data.get("effective_date"),
            review_date=data.get("review_date"),
            author=data.get("author"),
            approver=data.get("approver"),
            approval_date=data.get("approval_date"),
            change_history=data.get("change_history", []),
            has_audit_trail=data.get("has_audit_trail", False),
            has_electronic_signature=data.get("has_electronic_signature", False),
            signature_components=data.get("signature_components", 0)
        )
    else:
        # Demo document
        doc = Document(
            number="SOP-02-001",
            title="Document Control",
            doc_type="SOP",
            revision="01",
            status="Effective",
            effective_date="2024-01-15",
            author="J. Smith",
            has_audit_trail=True,
            has_electronic_signature=True,
            signature_components=2
        )

    validator = DocumentValidator(doc)
    result = validator.validate()

    if args.output == "json":
        print(json.dumps(asdict(result), indent=2))
    else:
        print(format_text_output(result))


if __name__ == "__main__":
    main()
