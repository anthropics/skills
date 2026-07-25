#!/usr/bin/env python3
"""
MDR Gap Analyzer - EU MDR 2017/745 Compliance Gap Assessment Tool

Analyzes device classification, identifies documentation gaps, and generates
compliance roadmap for EU MDR transition.

Usage:
    python mdr_gap_analyzer.py --device "Device Name" --class IIa
    python mdr_gap_analyzer.py --device "Device Name" --class III --output json
    python mdr_gap_analyzer.py --interactive
"""

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from datetime import datetime
from typing import List, Dict, Optional
from enum import Enum


class DeviceClass(Enum):
    I = "I"
    I_STERILE = "Is"
    I_MEASURING = "Im"
    IIA = "IIa"
    IIB = "IIb"
    III = "III"


class GapStatus(Enum):
    NOT_STARTED = "Not Started"
    IN_PROGRESS = "In Progress"
    COMPLETE = "Complete"
    NOT_APPLICABLE = "N/A"


@dataclass
class GapItem:
    requirement: str
    category: str
    description: str
    status: GapStatus = GapStatus.NOT_STARTED
    priority: str = "Medium"
    evidence_needed: List[str] = field(default_factory=list)
    notes: str = ""


@dataclass
class GapAnalysisResult:
    device_name: str
    device_class: str
    analysis_date: str
    total_requirements: int
    gaps_identified: int
    completion_percentage: float
    gaps: List[Dict]
    recommendations: List[str]
    critical_gaps: List[str]


class MDRGapAnalyzer:
    """Analyzer for EU MDR 2017/745 compliance gaps."""

    # MDR Requirements by category
    REQUIREMENTS = {
        "technical_documentation": [
            GapItem(
                requirement="Annex II - Device Description",
                category="Technical Documentation",
                description="Complete device description including variants, accessories, intended purpose",
                priority="High",
                evidence_needed=["Device specification", "Intended purpose statement", "Variant listing"]
            ),
            GapItem(
                requirement="Annex II - Information Supplied",
                category="Technical Documentation",
                description="Label and IFU meeting Article 13 requirements",
                priority="High",
                evidence_needed=["Label artwork", "Instructions for use", "Symbol glossary"]
            ),
            GapItem(
                requirement="Annex II - Design and Manufacturing",
                category="Technical Documentation",
                description="Design history file and manufacturing documentation",
                priority="High",
                evidence_needed=["Design history file", "Process flow diagram", "Validation reports"]
            ),
            GapItem(
                requirement="Annex II - GSPR Compliance",
                category="Technical Documentation",
                description="General Safety and Performance Requirements checklist",
                priority="Critical",
                evidence_needed=["GSPR matrix", "Standard compliance evidence", "Risk management file"]
            ),
        ],
        "clinical_evaluation": [
            GapItem(
                requirement="Annex XIV Part A - Clinical Evaluation",
                category="Clinical Evaluation",
                description="Clinical evaluation report with systematic literature review",
                priority="Critical",
                evidence_needed=["Clinical evaluation report", "Literature search protocol", "Data appraisal"]
            ),
            GapItem(
                requirement="Annex XIV Part B - PMCF",
                category="Clinical Evaluation",
                description="Post-market clinical follow-up plan and evaluation report",
                priority="High",
                evidence_needed=["PMCF plan", "PMCF evaluation report", "Residual risk assessment"]
            ),
            GapItem(
                requirement="Qualified Person for CER",
                category="Clinical Evaluation",
                description="Clinical evaluation by qualified evaluator per Annex XIV",
                priority="High",
                evidence_needed=["Evaluator CV", "Qualification evidence", "Signed CER"]
            ),
        ],
        "risk_management": [
            GapItem(
                requirement="ISO 14971 Risk Management",
                category="Risk Management",
                description="Complete risk management file per ISO 14971:2019",
                priority="Critical",
                evidence_needed=["Risk management plan", "Risk analysis", "Risk evaluation", "Risk control"]
            ),
            GapItem(
                requirement="Benefit-Risk Analysis",
                category="Risk Management",
                description="Documented benefit-risk determination",
                priority="High",
                evidence_needed=["Benefit-risk analysis document", "Residual risk acceptability"]
            ),
        ],
        "quality_management": [
            GapItem(
                requirement="ISO 13485 QMS",
                category="Quality Management",
                description="Quality management system conforming to ISO 13485:2016",
                priority="Critical",
                evidence_needed=["QMS manual", "Process documentation", "Internal audit records"]
            ),
            GapItem(
                requirement="Post-Market Surveillance",
                category="Quality Management",
                description="PMS system per Article 83-86",
                priority="High",
                evidence_needed=["PMS plan", "PSUR (if required)", "Vigilance procedures"]
            ),
        ],
        "udi_eudamed": [
            GapItem(
                requirement="UDI System",
                category="UDI/EUDAMED",
                description="Unique Device Identification per Article 27",
                priority="High",
                evidence_needed=["UDI-DI assignment", "Label with UDI carrier", "GUDID/EUDAMED registration"]
            ),
            GapItem(
                requirement="EUDAMED Registration",
                category="UDI/EUDAMED",
                description="Actor, device, and certificate registration in EUDAMED",
                priority="Medium",
                evidence_needed=["Actor registration", "Device registration", "Certificate upload"]
            ),
        ],
        "notified_body": [
            GapItem(
                requirement="Notified Body Selection",
                category="Notified Body",
                description="Selection and engagement of MDR-designated Notified Body",
                priority="Critical",
                evidence_needed=["NB selection criteria", "NB engagement letter", "Audit schedule"]
            ),
            GapItem(
                requirement="Conformity Assessment",
                category="Notified Body",
                description="Completion of appropriate conformity assessment procedure",
                priority="Critical",
                evidence_needed=["Application dossier", "Technical documentation submission", "Certificate"]
            ),
        ],
    }

    # Class-specific requirements
    CLASS_REQUIREMENTS = {
        DeviceClass.III: [
            GapItem(
                requirement="Annex III - Class III Additions",
                category="Technical Documentation",
                description="Additional documentation for Class III devices",
                priority="Critical",
                evidence_needed=["Implant card", "Patient information", "Device tracking"]
            ),
            GapItem(
                requirement="Clinical Investigation",
                category="Clinical Evaluation",
                description="Clinical investigation per Article 61 (unless equivalent device)",
                priority="Critical",
                evidence_needed=["Clinical investigation plan", "Ethics approval", "Clinical study report"]
            ),
        ],
        DeviceClass.IIB: [
            GapItem(
                requirement="Implantable Device Documentation",
                category="Technical Documentation",
                description="Additional requirements for implantable Class IIb devices",
                priority="High",
                evidence_needed=["Implant card (if implantable)", "Long-term safety data"]
            ),
        ],
    }

    def __init__(self, device_name: str, device_class: DeviceClass):
        self.device_name = device_name
        self.device_class = device_class
        self.gaps: List[GapItem] = []
        self._build_requirements_list()

    def _build_requirements_list(self):
        """Build complete requirements list based on device class."""
        # Add all base requirements
        for category_gaps in self.REQUIREMENTS.values():
            for gap in category_gaps:
                self.gaps.append(GapItem(
                    requirement=gap.requirement,
                    category=gap.category,
                    description=gap.description,
                    priority=gap.priority,
                    evidence_needed=gap.evidence_needed.copy()
                ))

        # Add class-specific requirements
        if self.device_class in self.CLASS_REQUIREMENTS:
            for gap in self.CLASS_REQUIREMENTS[self.device_class]:
                self.gaps.append(GapItem(
                    requirement=gap.requirement,
                    category=gap.category,
                    description=gap.description,
                    priority=gap.priority,
                    evidence_needed=gap.evidence_needed.copy()
                ))

        # Class I self-certification: NB not required
        if self.device_class == DeviceClass.I:
            for gap in self.gaps:
                if gap.category == "Notified Body":
                    gap.status = GapStatus.NOT_APPLICABLE

    def update_gap_status(self, requirement: str, status: GapStatus, notes: str = ""):
        """Update status of a specific gap."""
        for gap in self.gaps:
            if gap.requirement == requirement:
                gap.status = status
                gap.notes = notes
                break

    def analyze(self) -> GapAnalysisResult:
        """Perform gap analysis and generate results."""
        applicable_gaps = [g for g in self.gaps if g.status != GapStatus.NOT_APPLICABLE]
        complete_gaps = [g for g in applicable_gaps if g.status == GapStatus.COMPLETE]

        completion = (len(complete_gaps) / len(applicable_gaps) * 100) if applicable_gaps else 0

        # Identify critical gaps
        critical_gaps = [
            g.requirement for g in applicable_gaps
            if g.priority == "Critical" and g.status != GapStatus.COMPLETE
        ]

        # Generate recommendations
        recommendations = self._generate_recommendations()

        return GapAnalysisResult(
            device_name=self.device_name,
            device_class=self.device_class.value,
            analysis_date=datetime.now().isoformat(),
            total_requirements=len(applicable_gaps),
            gaps_identified=len(applicable_gaps) - len(complete_gaps),
            completion_percentage=round(completion, 1),
            gaps=[{
                "requirement": g.requirement,
                "category": g.category,
                "status": g.status.value,
                "priority": g.priority,
                "evidence_needed": g.evidence_needed
            } for g in applicable_gaps],
            recommendations=recommendations,
            critical_gaps=critical_gaps
        )

    def _generate_recommendations(self) -> List[str]:
        """Generate prioritized recommendations."""
        recommendations = []

        # Check for critical gaps
        critical_incomplete = [
            g for g in self.gaps
            if g.priority == "Critical" and g.status not in [GapStatus.COMPLETE, GapStatus.NOT_APPLICABLE]
        ]

        if critical_incomplete:
            recommendations.append(
                f"CRITICAL: {len(critical_incomplete)} critical requirements not complete. "
                "Address immediately to proceed with conformity assessment."
            )

        # Check clinical evaluation
        cer_gap = next((g for g in self.gaps if "Clinical Evaluation" in g.requirement), None)
        if cer_gap and cer_gap.status != GapStatus.COMPLETE:
            recommendations.append(
                "Clinical Evaluation Report (CER) is incomplete. "
                "This is required before Notified Body submission."
            )

        # Check for Class III specific
        if self.device_class == DeviceClass.III:
            ci_gap = next((g for g in self.gaps if "Clinical Investigation" in g.requirement), None)
            if ci_gap and ci_gap.status != GapStatus.COMPLETE:
                recommendations.append(
                    "Class III device requires clinical investigation per Article 61 "
                    "unless equivalence can be demonstrated."
                )

        # Check EUDAMED
        udi_gap = next((g for g in self.gaps if "UDI System" in g.requirement), None)
        if udi_gap and udi_gap.status != GapStatus.COMPLETE:
            recommendations.append(
                "Implement UDI system and plan for EUDAMED registration. "
                "Required for placing device on EU market."
            )

        return recommendations


def format_text_output(result: GapAnalysisResult) -> str:
    """Format analysis result as text."""
    lines = [
        "=" * 60,
        "MDR 2017/745 GAP ANALYSIS REPORT",
        "=" * 60,
        f"Device: {result.device_name}",
        f"Class: {result.device_class}",
        f"Date: {result.analysis_date[:10]}",
        "",
        "-" * 60,
        "SUMMARY",
        "-" * 60,
        f"Total Requirements: {result.total_requirements}",
        f"Gaps Identified: {result.gaps_identified}",
        f"Completion: {result.completion_percentage}%",
        "",
    ]

    if result.critical_gaps:
        lines.extend([
            "-" * 60,
            "CRITICAL GAPS (Address Immediately)",
            "-" * 60,
        ])
        for gap in result.critical_gaps:
            lines.append(f"  * {gap}")
        lines.append("")

    lines.extend([
        "-" * 60,
        "GAP DETAILS BY CATEGORY",
        "-" * 60,
    ])

    # Group by category
    categories = {}
    for gap in result.gaps:
        cat = gap["category"]
        if cat not in categories:
            categories[cat] = []
        categories[cat].append(gap)

    for category, gaps in categories.items():
        lines.append(f"\n{category}:")
        for gap in gaps:
            status_mark = "✓" if gap["status"] == "Complete" else "○"
            lines.append(f"  [{status_mark}] {gap['requirement']} ({gap['priority']})")

    lines.extend([
        "",
        "-" * 60,
        "RECOMMENDATIONS",
        "-" * 60,
    ])
    for i, rec in enumerate(result.recommendations, 1):
        lines.append(f"{i}. {rec}")

    lines.append("=" * 60)
    return "\n".join(lines)


def interactive_mode():
    """Run interactive gap analysis session."""
    print("=" * 60)
    print("MDR 2017/745 Gap Analysis - Interactive Mode")
    print("=" * 60)

    device_name = input("\nDevice name: ").strip()
    if not device_name:
        device_name = "Unnamed Device"

    print("\nDevice classes:")
    print("  1. Class I")
    print("  2. Class I (sterile)")
    print("  3. Class I (measuring)")
    print("  4. Class IIa")
    print("  5. Class IIb")
    print("  6. Class III")

    class_map = {
        "1": DeviceClass.I,
        "2": DeviceClass.I_STERILE,
        "3": DeviceClass.I_MEASURING,
        "4": DeviceClass.IIA,
        "5": DeviceClass.IIB,
        "6": DeviceClass.III,
    }

    class_choice = input("\nSelect class (1-6): ").strip()
    device_class = class_map.get(class_choice, DeviceClass.IIA)

    analyzer = MDRGapAnalyzer(device_name, device_class)

    print("\nFor each requirement, enter status:")
    print("  c = Complete")
    print("  i = In Progress")
    print("  n = Not Started (default)")
    print("  x = Not Applicable")
    print("  Enter = Skip (Not Started)")
    print("")

    status_map = {
        "c": GapStatus.COMPLETE,
        "i": GapStatus.IN_PROGRESS,
        "n": GapStatus.NOT_STARTED,
        "x": GapStatus.NOT_APPLICABLE,
    }

    for gap in analyzer.gaps:
        if gap.status == GapStatus.NOT_APPLICABLE:
            continue
        status_input = input(f"{gap.requirement} [c/i/n/x]: ").strip().lower()
        if status_input in status_map:
            gap.status = status_map[status_input]

    result = analyzer.analyze()
    print("\n" + format_text_output(result))


def main():
    parser = argparse.ArgumentParser(
        description="EU MDR 2017/745 Gap Analysis Tool"
    )
    parser.add_argument("--device", type=str, help="Device name")
    parser.add_argument(
        "--class",
        dest="device_class",
        choices=["I", "Is", "Im", "IIa", "IIb", "III"],
        help="Device classification"
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

    args = parser.parse_args()

    if args.interactive:
        interactive_mode()
        return

    if not args.device or not args.device_class:
        parser.print_help()
        print("\nError: --device and --class required (or use --interactive)")
        sys.exit(1)

    class_map = {
        "I": DeviceClass.I,
        "Is": DeviceClass.I_STERILE,
        "Im": DeviceClass.I_MEASURING,
        "IIa": DeviceClass.IIA,
        "IIb": DeviceClass.IIB,
        "III": DeviceClass.III,
    }

    analyzer = MDRGapAnalyzer(args.device, class_map[args.device_class])
    result = analyzer.analyze()

    if args.output == "json":
        print(json.dumps(asdict(result), indent=2))
    else:
        print(format_text_output(result))


if __name__ == "__main__":
    main()
