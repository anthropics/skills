#!/usr/bin/env python3
"""
CAPA Tracker - Corrective and Preventive Action Management Tool

Tracks CAPA status, calculates metrics, identifies overdue items,
and generates reports for management review.

Usage:
    python capa_tracker.py --capas capas.json
    python capa_tracker.py --interactive
    python capa_tracker.py --capas capas.json --output json
"""

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta
from typing import List, Dict, Optional
from enum import Enum


class CAPAStatus(Enum):
    OPEN = "Open"
    INVESTIGATION = "Investigation"
    ACTION_PLANNING = "Action Planning"
    IMPLEMENTATION = "Implementation"
    VERIFICATION = "Verification"
    CLOSED_EFFECTIVE = "Closed - Effective"
    CLOSED_INEFFECTIVE = "Closed - Ineffective"


class CAPASeverity(Enum):
    CRITICAL = "Critical"
    MAJOR = "Major"
    MINOR = "Minor"


class CAPASource(Enum):
    COMPLAINT = "Customer Complaint"
    AUDIT = "Internal Audit"
    EXTERNAL_AUDIT = "External Audit"
    NONCONFORMANCE = "Nonconformance"
    MANAGEMENT_REVIEW = "Management Review"
    TREND_ANALYSIS = "Trend Analysis"
    REGULATORY = "Regulatory Feedback"
    OTHER = "Other"


@dataclass
class CAPA:
    capa_number: str
    title: str
    description: str
    source: CAPASource
    severity: CAPASeverity
    status: CAPAStatus
    open_date: str
    target_date: str
    owner: str
    root_cause: str = ""
    corrective_action: str = ""
    verification_date: Optional[str] = None
    close_date: Optional[str] = None
    days_open: int = 0
    is_overdue: bool = False


@dataclass
class CAPAMetrics:
    total_capas: int
    open_capas: int
    closed_capas: int
    overdue_capas: int
    avg_cycle_time: float
    effectiveness_rate: float
    by_status: Dict[str, int]
    by_severity: Dict[str, int]
    by_source: Dict[str, int]
    overdue_list: List[Dict]
    recommendations: List[str]


class CAPATracker:
    """CAPA tracking and metrics calculator."""

    # Target cycle times by severity (days)
    TARGET_CYCLE_TIMES = {
        CAPASeverity.CRITICAL: 30,
        CAPASeverity.MAJOR: 60,
        CAPASeverity.MINOR: 90,
    }

    def __init__(self, capas: List[CAPA]):
        self.capas = capas
        self.today = datetime.now()
        self._calculate_derived_fields()

    def _calculate_derived_fields(self):
        """Calculate days open and overdue status."""
        for capa in self.capas:
            open_date = datetime.strptime(capa.open_date, "%Y-%m-%d")

            if capa.close_date:
                close_date = datetime.strptime(capa.close_date, "%Y-%m-%d")
                capa.days_open = (close_date - open_date).days
            else:
                capa.days_open = (self.today - open_date).days

            target_date = datetime.strptime(capa.target_date, "%Y-%m-%d")
            if not capa.close_date and self.today > target_date:
                capa.is_overdue = True

    def calculate_metrics(self) -> CAPAMetrics:
        """Calculate comprehensive CAPA metrics."""
        total = len(self.capas)

        # Status counts
        closed_statuses = [CAPAStatus.CLOSED_EFFECTIVE, CAPAStatus.CLOSED_INEFFECTIVE]
        open_capas = [c for c in self.capas if c.status not in closed_statuses]
        closed_capas = [c for c in self.capas if c.status in closed_statuses]
        overdue_capas = [c for c in self.capas if c.is_overdue]

        # Average cycle time (closed CAPAs only)
        if closed_capas:
            avg_cycle = sum(c.days_open for c in closed_capas) / len(closed_capas)
        else:
            avg_cycle = 0.0

        # Effectiveness rate
        effective = [c for c in self.capas if c.status == CAPAStatus.CLOSED_EFFECTIVE]
        ineffective = [c for c in self.capas if c.status == CAPAStatus.CLOSED_INEFFECTIVE]
        if effective or ineffective:
            effectiveness = len(effective) / (len(effective) + len(ineffective)) * 100
        else:
            effectiveness = 0.0

        # Counts by category
        by_status = {}
        for status in CAPAStatus:
            count = len([c for c in self.capas if c.status == status])
            if count > 0:
                by_status[status.value] = count

        by_severity = {}
        for severity in CAPASeverity:
            count = len([c for c in self.capas if c.severity == severity])
            if count > 0:
                by_severity[severity.value] = count

        by_source = {}
        for source in CAPASource:
            count = len([c for c in self.capas if c.source == source])
            if count > 0:
                by_source[source.value] = count

        # Overdue list
        overdue_list = []
        for capa in sorted(overdue_capas, key=lambda c: c.days_open, reverse=True):
            target = datetime.strptime(capa.target_date, "%Y-%m-%d")
            days_overdue = (self.today - target).days
            overdue_list.append({
                "capa_number": capa.capa_number,
                "title": capa.title,
                "severity": capa.severity.value,
                "status": capa.status.value,
                "days_overdue": days_overdue,
                "owner": capa.owner
            })

        # Generate recommendations
        recommendations = self._generate_recommendations(
            open_capas, overdue_capas, effectiveness, avg_cycle
        )

        return CAPAMetrics(
            total_capas=total,
            open_capas=len(open_capas),
            closed_capas=len(closed_capas),
            overdue_capas=len(overdue_capas),
            avg_cycle_time=round(avg_cycle, 1),
            effectiveness_rate=round(effectiveness, 1),
            by_status=by_status,
            by_severity=by_severity,
            by_source=by_source,
            overdue_list=overdue_list,
            recommendations=recommendations
        )

    def _generate_recommendations(
        self,
        open_capas: List[CAPA],
        overdue_capas: List[CAPA],
        effectiveness: float,
        avg_cycle: float
    ) -> List[str]:
        """Generate actionable recommendations."""
        recommendations = []

        # Overdue CAPAs
        if overdue_capas:
            critical_overdue = [c for c in overdue_capas if c.severity == CAPASeverity.CRITICAL]
            if critical_overdue:
                recommendations.append(
                    f"URGENT: {len(critical_overdue)} critical CAPA(s) overdue. "
                    "Escalate to management immediately."
                )
            else:
                recommendations.append(
                    f"ACTION: {len(overdue_capas)} CAPA(s) overdue. "
                    "Review and update target dates or expedite closure."
                )

        # Effectiveness rate
        if effectiveness < 80 and effectiveness > 0:
            recommendations.append(
                f"CONCERN: Effectiveness rate at {effectiveness:.0f}%. "
                "Review root cause analysis quality and corrective action adequacy."
            )

        # Cycle time
        if avg_cycle > 60:
            recommendations.append(
                f"IMPROVEMENT: Average cycle time is {avg_cycle:.0f} days. "
                "Target is 60 days. Review investigation and approval bottlenecks."
            )

        # Investigation backlog
        in_investigation = [c for c in open_capas if c.status == CAPAStatus.INVESTIGATION]
        if len(in_investigation) > 5:
            recommendations.append(
                f"WORKLOAD: {len(in_investigation)} CAPAs in investigation phase. "
                "Consider additional resources or prioritization."
            )

        # Stuck in verification
        in_verification = [c for c in open_capas if c.status == CAPAStatus.VERIFICATION]
        old_verification = [c for c in in_verification if c.days_open > 120]
        if old_verification:
            recommendations.append(
                f"STALLED: {len(old_verification)} CAPA(s) in verification >120 days. "
                "Complete effectiveness checks or extend with justification."
            )

        # Source patterns
        complaint_capas = [c for c in self.capas if c.source == CAPASource.COMPLAINT]
        if len(complaint_capas) > len(self.capas) * 0.4:
            recommendations.append(
                "TREND: >40% of CAPAs from customer complaints. "
                "Review preventive action effectiveness and quality controls."
            )

        if not recommendations:
            recommendations.append(
                "CAPA program operating within targets. "
                "Continue monitoring key metrics."
            )

        return recommendations

    def get_aging_report(self) -> Dict:
        """Generate aging analysis of open CAPAs."""
        open_statuses = [
            CAPAStatus.OPEN, CAPAStatus.INVESTIGATION,
            CAPAStatus.ACTION_PLANNING, CAPAStatus.IMPLEMENTATION,
            CAPAStatus.VERIFICATION
        ]
        open_capas = [c for c in self.capas if c.status in open_statuses]

        aging_buckets = {
            "0-30 days": [],
            "31-60 days": [],
            "61-90 days": [],
            "91-120 days": [],
            ">120 days": []
        }

        for capa in open_capas:
            days = capa.days_open
            if days <= 30:
                bucket = "0-30 days"
            elif days <= 60:
                bucket = "31-60 days"
            elif days <= 90:
                bucket = "61-90 days"
            elif days <= 120:
                bucket = "91-120 days"
            else:
                bucket = ">120 days"

            aging_buckets[bucket].append({
                "capa_number": capa.capa_number,
                "title": capa.title,
                "days_open": days,
                "status": capa.status.value,
                "severity": capa.severity.value
            })

        return aging_buckets


def format_text_output(metrics: CAPAMetrics, aging: Dict) -> str:
    """Format metrics as text report."""
    lines = [
        "=" * 70,
        "CAPA STATUS REPORT",
        "=" * 70,
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}",
        "",
        "SUMMARY METRICS",
        "-" * 40,
        f"Total CAPAs:        {metrics.total_capas}",
        f"Open CAPAs:         {metrics.open_capas}",
        f"Closed CAPAs:       {metrics.closed_capas}",
        f"Overdue CAPAs:      {metrics.overdue_capas}",
        f"Avg Cycle Time:     {metrics.avg_cycle_time} days",
        f"Effectiveness Rate: {metrics.effectiveness_rate}%",
        "",
        "STATUS DISTRIBUTION",
        "-" * 40,
    ]

    for status, count in metrics.by_status.items():
        bar = "█" * min(count, 20)
        lines.append(f"  {status:<25} {bar} {count}")

    lines.extend([
        "",
        "SEVERITY DISTRIBUTION",
        "-" * 40,
    ])

    for severity, count in metrics.by_severity.items():
        bar = "█" * min(count, 20)
        lines.append(f"  {severity:<25} {bar} {count}")

    lines.extend([
        "",
        "SOURCE DISTRIBUTION",
        "-" * 40,
    ])

    for source, count in metrics.by_source.items():
        bar = "█" * min(count, 20)
        lines.append(f"  {source:<25} {bar} {count}")

    lines.extend([
        "",
        "AGING ANALYSIS",
        "-" * 40,
    ])

    for bucket, capas in aging.items():
        lines.append(f"  {bucket}: {len(capas)} CAPA(s)")

    if metrics.overdue_list:
        lines.extend([
            "",
            "OVERDUE CAPAs",
            "-" * 40,
            f"{'CAPA #':<12} {'Title':<25} {'Days':<6} {'Owner':<15}",
            "-" * 60,
        ])

        for item in metrics.overdue_list[:10]:
            title = item["title"][:24] if len(item["title"]) > 24 else item["title"]
            lines.append(
                f"{item['capa_number']:<12} {title:<25} "
                f"{item['days_overdue']:<6} {item['owner']:<15}"
            )

        if len(metrics.overdue_list) > 10:
            lines.append(f"... and {len(metrics.overdue_list) - 10} more")

    lines.extend([
        "",
        "RECOMMENDATIONS",
        "-" * 40,
    ])

    for i, rec in enumerate(metrics.recommendations, 1):
        lines.append(f"{i}. {rec}")

    lines.append("=" * 70)
    return "\n".join(lines)


def interactive_mode():
    """Run interactive CAPA entry mode."""
    print("=" * 60)
    print("CAPA Tracker - Interactive Mode")
    print("=" * 60)

    capas = []
    print("\nEnter CAPAs (blank CAPA number to finish):\n")

    while True:
        capa_num = input("CAPA Number (e.g., CAPA-2024-001): ").strip()
        if not capa_num:
            break

        title = input("Title: ").strip()
        description = input("Description: ").strip()

        print("Source options: C=Complaint, A=Audit, N=Nonconformance, M=Management Review, T=Trend, O=Other")
        source_input = input("Source [C/A/N/M/T/O]: ").strip().upper()
        source_map = {
            "C": CAPASource.COMPLAINT,
            "A": CAPASource.AUDIT,
            "N": CAPASource.NONCONFORMANCE,
            "M": CAPASource.MANAGEMENT_REVIEW,
            "T": CAPASource.TREND_ANALYSIS,
            "O": CAPASource.OTHER
        }
        source = source_map.get(source_input, CAPASource.OTHER)

        print("Severity: C=Critical, M=Major, I=Minor")
        severity_input = input("Severity [C/M/I]: ").strip().upper()
        severity_map = {
            "C": CAPASeverity.CRITICAL,
            "M": CAPASeverity.MAJOR,
            "I": CAPASeverity.MINOR
        }
        severity = severity_map.get(severity_input, CAPASeverity.MINOR)

        print("Status: O=Open, I=Investigation, P=Action Planning, M=Implementation, V=Verification, E=Closed Effective, N=Closed Ineffective")
        status_input = input("Status [O/I/P/M/V/E/N]: ").strip().upper()
        status_map = {
            "O": CAPAStatus.OPEN,
            "I": CAPAStatus.INVESTIGATION,
            "P": CAPAStatus.ACTION_PLANNING,
            "M": CAPAStatus.IMPLEMENTATION,
            "V": CAPAStatus.VERIFICATION,
            "E": CAPAStatus.CLOSED_EFFECTIVE,
            "N": CAPAStatus.CLOSED_INEFFECTIVE
        }
        status = status_map.get(status_input, CAPAStatus.OPEN)

        open_date = input("Open Date (YYYY-MM-DD): ").strip()
        target_date = input("Target Date (YYYY-MM-DD): ").strip()
        owner = input("Owner: ").strip()

        close_date = None
        if status in [CAPAStatus.CLOSED_EFFECTIVE, CAPAStatus.CLOSED_INEFFECTIVE]:
            close_date = input("Close Date (YYYY-MM-DD): ").strip()

        capas.append(CAPA(
            capa_number=capa_num,
            title=title,
            description=description,
            source=source,
            severity=severity,
            status=status,
            open_date=open_date,
            target_date=target_date,
            owner=owner,
            close_date=close_date if close_date else None
        ))

        print(f"\nAdded: {capa_num}\n")

    if not capas:
        print("No CAPAs entered. Exiting.")
        return

    tracker = CAPATracker(capas)
    metrics = tracker.calculate_metrics()
    aging = tracker.get_aging_report()
    print("\n" + format_text_output(metrics, aging))


def main():
    parser = argparse.ArgumentParser(
        description="CAPA Tracking and Metrics Tool"
    )
    parser.add_argument(
        "--capas",
        type=str,
        help="JSON file with CAPA data"
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
        help="Generate sample CAPA data file"
    )

    args = parser.parse_args()

    if args.interactive:
        interactive_mode()
        return

    if args.sample:
        sample_data = {
            "capas": [
                {
                    "capa_number": "CAPA-2024-001",
                    "title": "Calibration overdue for pH meter",
                    "description": "pH meter EQ-042 found 2 months overdue",
                    "source": "AUDIT",
                    "severity": "MAJOR",
                    "status": "VERIFICATION",
                    "open_date": "2024-06-15",
                    "target_date": "2024-08-15",
                    "owner": "J. Smith",
                    "root_cause": "No trigger for schedule update at equipment purchase",
                    "corrective_action": "Updated SOP-EQ-001 to require schedule update"
                },
                {
                    "capa_number": "CAPA-2024-002",
                    "title": "Customer complaint - labeling error",
                    "description": "Wrong lot number on product label",
                    "source": "COMPLAINT",
                    "severity": "CRITICAL",
                    "status": "INVESTIGATION",
                    "open_date": "2024-09-01",
                    "target_date": "2024-10-01",
                    "owner": "M. Jones"
                },
                {
                    "capa_number": "CAPA-2024-003",
                    "title": "Training records incomplete",
                    "description": "Missing effectiveness verification for 3 operators",
                    "source": "AUDIT",
                    "severity": "MINOR",
                    "status": "CLOSED_EFFECTIVE",
                    "open_date": "2024-03-10",
                    "target_date": "2024-06-10",
                    "owner": "A. Brown",
                    "close_date": "2024-05-20"
                }
            ]
        }
        print(json.dumps(sample_data, indent=2))
        return

    if args.capas:
        with open(args.capas, "r") as f:
            data = json.load(f)

        capas = []
        for c in data.get("capas", []):
            try:
                source = CAPASource[c.get("source", "OTHER").upper()]
            except KeyError:
                source = CAPASource.OTHER

            try:
                severity = CAPASeverity[c.get("severity", "MINOR").upper()]
            except KeyError:
                severity = CAPASeverity.MINOR

            try:
                status = CAPAStatus[c.get("status", "OPEN").upper()]
            except KeyError:
                status = CAPAStatus.OPEN

            capas.append(CAPA(
                capa_number=c["capa_number"],
                title=c.get("title", ""),
                description=c.get("description", ""),
                source=source,
                severity=severity,
                status=status,
                open_date=c["open_date"],
                target_date=c["target_date"],
                owner=c.get("owner", ""),
                root_cause=c.get("root_cause", ""),
                corrective_action=c.get("corrective_action", ""),
                verification_date=c.get("verification_date"),
                close_date=c.get("close_date")
            ))
    else:
        # Demo data if no file provided
        capas = [
            CAPA(
                capa_number="CAPA-2024-001",
                title="Calibration overdue",
                description="pH meter overdue",
                source=CAPASource.AUDIT,
                severity=CAPASeverity.MAJOR,
                status=CAPAStatus.VERIFICATION,
                open_date="2024-06-15",
                target_date="2024-08-15",
                owner="J. Smith"
            ),
            CAPA(
                capa_number="CAPA-2024-002",
                title="Labeling error complaint",
                description="Wrong lot number",
                source=CAPASource.COMPLAINT,
                severity=CAPASeverity.CRITICAL,
                status=CAPAStatus.INVESTIGATION,
                open_date="2024-09-01",
                target_date="2024-10-01",
                owner="M. Jones"
            ),
            CAPA(
                capa_number="CAPA-2024-003",
                title="Training records incomplete",
                description="Missing effectiveness verification",
                source=CAPASource.AUDIT,
                severity=CAPASeverity.MINOR,
                status=CAPAStatus.CLOSED_EFFECTIVE,
                open_date="2024-03-10",
                target_date="2024-06-10",
                owner="A. Brown",
                close_date="2024-05-20"
            )
        ]

    tracker = CAPATracker(capas)
    metrics = tracker.calculate_metrics()
    aging = tracker.get_aging_report()

    if args.output == "json":
        output = {
            "metrics": asdict(metrics),
            "aging": aging
        }
        print(json.dumps(output, indent=2))
    else:
        print(format_text_output(metrics, aging))


if __name__ == "__main__":
    main()
