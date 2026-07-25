#!/usr/bin/env python3
"""
FMEA Analyzer - Failure Mode and Effects Analysis for medical device risk management.

Supports Design FMEA (dFMEA) and Process FMEA (pFMEA) per ISO 14971 and IEC 60812.
Calculates Risk Priority Numbers (RPN), identifies critical items, and generates
risk reduction recommendations.

Usage:
    python fmea_analyzer.py --data fmea_input.json
    python fmea_analyzer.py --interactive
    python fmea_analyzer.py --data fmea_input.json --output json
"""

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Optional, Tuple
from enum import Enum
from datetime import datetime


class FMEAType(Enum):
    DESIGN = "Design FMEA"
    PROCESS = "Process FMEA"


class Severity(Enum):
    INCONSEQUENTIAL = 1
    MINOR = 2
    MODERATE = 3
    SIGNIFICANT = 4
    SERIOUS = 5
    CRITICAL = 6
    SERIOUS_HAZARD = 7
    HAZARDOUS = 8
    HAZARDOUS_NO_WARNING = 9
    CATASTROPHIC = 10


class Occurrence(Enum):
    REMOTE = 1
    LOW = 2
    LOW_MODERATE = 3
    MODERATE = 4
    MODERATE_HIGH = 5
    HIGH = 6
    VERY_HIGH = 7
    EXTREMELY_HIGH = 8
    ALMOST_CERTAIN = 9
    INEVITABLE = 10


class Detection(Enum):
    ALMOST_CERTAIN = 1
    VERY_HIGH = 2
    HIGH = 3
    MODERATE_HIGH = 4
    MODERATE = 5
    LOW_MODERATE = 6
    LOW = 7
    VERY_LOW = 8
    REMOTE = 9
    ABSOLUTELY_UNCERTAIN = 10


@dataclass
class FMEAEntry:
    """Single FMEA line item."""
    item_process: str
    function: str
    failure_mode: str
    effect: str
    severity: int
    cause: str
    occurrence: int
    current_controls: str
    detection: int
    rpn: int = 0
    criticality: str = ""
    recommended_actions: List[str] = field(default_factory=list)
    responsibility: str = ""
    target_date: str = ""
    actions_taken: str = ""
    revised_severity: int = 0
    revised_occurrence: int = 0
    revised_detection: int = 0
    revised_rpn: int = 0

    def calculate_rpn(self):
        self.rpn = self.severity * self.occurrence * self.detection
        if self.severity >= 8:
            self.criticality = "CRITICAL"
        elif self.rpn >= 200:
            self.criticality = "HIGH"
        elif self.rpn >= 100:
            self.criticality = "MEDIUM"
        else:
            self.criticality = "LOW"

    def calculate_revised_rpn(self):
        if self.revised_severity and self.revised_occurrence and self.revised_detection:
            self.revised_rpn = self.revised_severity * self.revised_occurrence * self.revised_detection


@dataclass
class FMEAReport:
    """Complete FMEA analysis report."""
    fmea_type: str
    product_process: str
    team: List[str]
    date: str
    entries: List[FMEAEntry]
    summary: Dict
    risk_reduction_actions: List[Dict]


class FMEAAnalyzer:
    """Analyzes FMEA data and generates risk assessments."""

    # RPN thresholds
    RPN_CRITICAL = 200
    RPN_HIGH = 100
    RPN_MEDIUM = 50

    def __init__(self, fmea_type: FMEAType = FMEAType.DESIGN):
        self.fmea_type = fmea_type

    def analyze_entries(self, entries: List[FMEAEntry]) -> Dict:
        """Analyze all FMEA entries and generate summary."""
        for entry in entries:
            entry.calculate_rpn()
            entry.calculate_revised_rpn()

        rpns = [e.rpn for e in entries if e.rpn > 0]
        revised_rpns = [e.revised_rpn for e in entries if e.revised_rpn > 0]

        critical = [e for e in entries if e.criticality == "CRITICAL"]
        high = [e for e in entries if e.criticality == "HIGH"]
        medium = [e for e in entries if e.criticality == "MEDIUM"]

        # Severity distribution
        sev_dist = {}
        for e in entries:
            sev_range = "1-3 (Low)" if e.severity <= 3 else "4-6 (Medium)" if e.severity <= 6 else "7-10 (High)"
            sev_dist[sev_range] = sev_dist.get(sev_range, 0) + 1

        summary = {
            "total_entries": len(entries),
            "rpn_statistics": {
                "min": min(rpns) if rpns else 0,
                "max": max(rpns) if rpns else 0,
                "average": round(sum(rpns) / len(rpns), 1) if rpns else 0,
                "median": sorted(rpns)[len(rpns) // 2] if rpns else 0
            },
            "risk_distribution": {
                "critical_severity": len(critical),
                "high_rpn": len(high),
                "medium_rpn": len(medium),
                "low_rpn": len(entries) - len(critical) - len(high) - len(medium)
            },
            "severity_distribution": sev_dist,
            "top_risks": [
                {
                    "item": e.item_process,
                    "failure_mode": e.failure_mode,
                    "rpn": e.rpn,
                    "severity": e.severity
                }
                for e in sorted(entries, key=lambda x: x.rpn, reverse=True)[:5]
            ]
        }

        if revised_rpns:
            summary["revised_rpn_statistics"] = {
                "min": min(revised_rpns),
                "max": max(revised_rpns),
                "average": round(sum(revised_rpns) / len(revised_rpns), 1),
                "improvement": round((sum(rpns) - sum(revised_rpns)) / sum(rpns) * 100, 1) if rpns else 0
            }

        return summary

    def generate_risk_reduction_actions(self, entries: List[FMEAEntry]) -> List[Dict]:
        """Generate recommended risk reduction actions."""
        actions = []

        # Sort by RPN descending
        sorted_entries = sorted(entries, key=lambda e: e.rpn, reverse=True)

        for entry in sorted_entries[:10]:  # Top 10 risks
            if entry.rpn >= self.RPN_HIGH or entry.severity >= 8:
                strategies = []

                # Severity reduction strategies (highest priority for high severity)
                if entry.severity >= 7:
                    strategies.append({
                        "type": "Severity Reduction",
                        "action": f"Redesign {entry.item_process} to eliminate failure mode: {entry.failure_mode}",
                        "priority": "Highest",
                        "expected_impact": "May reduce severity by 2-4 points"
                    })

                # Occurrence reduction strategies
                if entry.occurrence >= 5:
                    strategies.append({
                        "type": "Occurrence Reduction",
                        "action": f"Implement preventive controls for cause: {entry.cause}",
                        "priority": "High",
                        "expected_impact": f"Target occurrence reduction from {entry.occurrence} to {max(1, entry.occurrence - 3)}"
                    })

                # Detection improvement strategies
                if entry.detection >= 5:
                    strategies.append({
                        "type": "Detection Improvement",
                        "action": f"Enhance detection methods: {entry.current_controls}",
                        "priority": "Medium",
                        "expected_impact": f"Target detection improvement from {entry.detection} to {max(1, entry.detection - 3)}"
                    })

                actions.append({
                    "item": entry.item_process,
                    "failure_mode": entry.failure_mode,
                    "current_rpn": entry.rpn,
                    "current_severity": entry.severity,
                    "strategies": strategies
                })

        return actions

    def create_entry_from_dict(self, data: Dict) -> FMEAEntry:
        """Create FMEA entry from dictionary."""
        entry = FMEAEntry(
            item_process=data.get("item_process", ""),
            function=data.get("function", ""),
            failure_mode=data.get("failure_mode", ""),
            effect=data.get("effect", ""),
            severity=data.get("severity", 1),
            cause=data.get("cause", ""),
            occurrence=data.get("occurrence", 1),
            current_controls=data.get("current_controls", ""),
            detection=data.get("detection", 1),
            recommended_actions=data.get("recommended_actions", []),
            responsibility=data.get("responsibility", ""),
            target_date=data.get("target_date", ""),
            actions_taken=data.get("actions_taken", ""),
            revised_severity=data.get("revised_severity", 0),
            revised_occurrence=data.get("revised_occurrence", 0),
            revised_detection=data.get("revised_detection", 0)
        )
        entry.calculate_rpn()
        entry.calculate_revised_rpn()
        return entry

    def generate_report(self, product_process: str, team: List[str], entries_data: List[Dict]) -> FMEAReport:
        """Generate complete FMEA report."""
        entries = [self.create_entry_from_dict(e) for e in entries_data]
        summary = self.analyze_entries(entries)
        actions = self.generate_risk_reduction_actions(entries)

        return FMEAReport(
            fmea_type=self.fmea_type.value,
            product_process=product_process,
            team=team,
            date=datetime.now().strftime("%Y-%m-%d"),
            entries=entries,
            summary=summary,
            risk_reduction_actions=actions
        )


def format_fmea_text(report: FMEAReport) -> str:
    """Format FMEA report as text."""
    lines = [
        "=" * 80,
        f"{report.fmea_type.upper()} REPORT",
        "=" * 80,
        f"Product/Process: {report.product_process}",
        f"Date: {report.date}",
        f"Team: {', '.join(report.team)}",
        "",
        "SUMMARY",
        "-" * 60,
        f"Total Failure Modes Analyzed: {report.summary['total_entries']}",
        f"Critical Severity (≥8): {report.summary['risk_distribution']['critical_severity']}",
        f"High RPN (≥100): {report.summary['risk_distribution']['high_rpn']}",
        f"Medium RPN (50-99): {report.summary['risk_distribution']['medium_rpn']}",
        "",
        "RPN Statistics:",
        f"  Min: {report.summary['rpn_statistics']['min']}",
        f"  Max: {report.summary['rpn_statistics']['max']}",
        f"  Average: {report.summary['rpn_statistics']['average']}",
        f"  Median: {report.summary['rpn_statistics']['median']}",
    ]

    if "revised_rpn_statistics" in report.summary:
        lines.extend([
            "",
            "Revised RPN Statistics:",
            f"  Average: {report.summary['revised_rpn_statistics']['average']}",
            f"  Improvement: {report.summary['revised_rpn_statistics']['improvement']}%",
        ])

    lines.extend([
        "",
        "TOP RISKS",
        "-" * 60,
        f"{'Item':<25} {'Failure Mode':<30} {'RPN':>5} {'Sev':>4}",
        "-" * 66,
    ])
    for risk in report.summary.get("top_risks", []):
        lines.append(f"{risk['item'][:24]:<25} {risk['failure_mode'][:29]:<30} {risk['rpn']:>5} {risk['severity']:>4}")

    lines.extend([
        "",
        "FMEA ENTRIES",
        "-" * 60,
    ])

    for i, entry in enumerate(report.entries, 1):
        marker = "⚠" if entry.criticality in ["CRITICAL", "HIGH"] else "•"
        lines.extend([
            f"",
            f"{marker} Entry {i}: {entry.item_process} - {entry.function}",
            f"  Failure Mode: {entry.failure_mode}",
            f"  Effect: {entry.effect}",
            f"  Cause: {entry.cause}",
            f"  S={entry.severity} × O={entry.occurrence} × D={entry.detection} = RPN {entry.rpn} [{entry.criticality}]",
            f"  Current Controls: {entry.current_controls}",
        ])
        if entry.recommended_actions:
            lines.append(f"  Recommended Actions:")
            for action in entry.recommended_actions:
                lines.append(f"    → {action}")
        if entry.revised_rpn > 0:
            lines.append(f"  Revised: S={entry.revised_severity} × O={entry.revised_occurrence} × D={entry.revised_detection} = RPN {entry.revised_rpn}")

    if report.risk_reduction_actions:
        lines.extend([
            "",
            "RISK REDUCTION RECOMMENDATIONS",
            "-" * 60,
        ])
        for action in report.risk_reduction_actions:
            lines.extend([
                f"",
                f"  {action['item']} - {action['failure_mode']}",
                f"  Current RPN: {action['current_rpn']} (Severity: {action['current_severity']})",
            ])
            for strategy in action["strategies"]:
                lines.append(f"    [{strategy['priority']}] {strategy['type']}: {strategy['action']}")
                lines.append(f"      Expected: {strategy['expected_impact']}")

    lines.append("=" * 80)
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="FMEA Analyzer for Medical Device Risk Management")
    parser.add_argument("--type", choices=["design", "process"], default="design", help="FMEA type")
    parser.add_argument("--data", type=str, help="JSON file with FMEA data")
    parser.add_argument("--output", choices=["text", "json"], default="text", help="Output format")
    parser.add_argument("--interactive", action="store_true", help="Interactive mode")

    args = parser.parse_args()

    fmea_type = FMEAType.DESIGN if args.type == "design" else FMEAType.PROCESS
    analyzer = FMEAAnalyzer(fmea_type)

    if args.data:
        with open(args.data) as f:
            data = json.load(f)
        report = analyzer.generate_report(
            product_process=data.get("product_process", ""),
            team=data.get("team", []),
            entries_data=data.get("entries", [])
        )
    else:
        # Demo data
        demo_entries = [
            {
                "item_process": "Battery Module",
                "function": "Provide power for 8 hours",
                "failure_mode": "Premature battery drain",
                "effect": "Device shuts down during procedure",
                "severity": 8,
                "cause": "Cell degradation due to temperature cycling",
                "occurrence": 4,
                "current_controls": "Incoming battery testing, temperature spec in IFU",
                "detection": 5,
                "recommended_actions": ["Add battery health monitoring algorithm", "Implement low-battery warning at 20%"]
            },
            {
                "item_process": "Software Controller",
                "function": "Control device operation",
                "failure_mode": "Firmware crash",
                "effect": "Device becomes unresponsive",
                "severity": 7,
                "cause": "Memory leak in logging module",
                "occurrence": 3,
                "current_controls": "Code review, unit testing, integration testing",
                "detection": 4,
                "recommended_actions": ["Add watchdog timer", "Implement memory usage monitoring"]
            },
            {
                "item_process": "Sterile Packaging",
                "function": "Maintain sterility until use",
                "failure_mode": "Seal breach",
                "effect": "Device contamination",
                "severity": 9,
                "cause": "Sealing jaw temperature variation",
                "occurrence": 2,
                "current_controls": "Seal integrity testing (dye penetration), SPC on sealing process",
                "detection": 3,
                "recommended_actions": ["Add real-time seal temperature monitoring", "Implement 100% seal integrity testing"]
            }
        ]
        report = analyzer.generate_report(
            product_process="Insulin Pump Model X200",
            team=["Quality Engineer", "R&D Lead", "Manufacturing Engineer", "Risk Manager"],
            entries_data=demo_entries
        )

    if args.output == "json":
        result = {
            "fmea_type": report.fmea_type,
            "product_process": report.product_process,
            "date": report.date,
            "team": report.team,
            "entries": [asdict(e) for e in report.entries],
            "summary": report.summary,
            "risk_reduction_actions": report.risk_reduction_actions
        }
        print(json.dumps(result, indent=2))
    else:
        print(format_fmea_text(report))


if __name__ == "__main__":
    main()
