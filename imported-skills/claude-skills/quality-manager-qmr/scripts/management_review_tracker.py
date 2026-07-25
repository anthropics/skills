#!/usr/bin/env python3
"""
Management Review Tracker - QMS Management Review Preparation and Tracking

Tracks management review inputs, action items, and generates review reports
for ISO 13485 compliance.

Usage:
    python management_review_tracker.py --data review_data.json
    python management_review_tracker.py --interactive
    python management_review_tracker.py --data review_data.json --output json
"""

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta
from typing import List, Dict, Optional
from enum import Enum


class ActionStatus(Enum):
    NOT_STARTED = "Not Started"
    IN_PROGRESS = "In Progress"
    ON_HOLD = "On Hold"
    OVERDUE = "Overdue"
    COMPLETE = "Complete"
    VERIFIED = "Verified"


class ActionPriority(Enum):
    HIGH = "High"
    MEDIUM = "Medium"
    LOW = "Low"


class InputStatus(Enum):
    NOT_COLLECTED = "Not Collected"
    IN_PROGRESS = "In Progress"
    COMPLETE = "Complete"
    REVIEWED = "Reviewed"


@dataclass
class ReviewInput:
    topic: str
    responsible: str
    status: InputStatus
    data_period: str
    summary: str = ""
    concerns: List[str] = field(default_factory=list)


@dataclass
class ActionItem:
    action_id: str
    description: str
    owner: str
    due_date: str
    priority: ActionPriority
    status: ActionStatus
    source_review: str
    category: str = "Improvement"
    completion_date: Optional[str] = None
    notes: str = ""


@dataclass
class ReviewMetrics:
    complaint_rate: float = 0.0
    complaint_count: int = 0
    capa_open: int = 0
    capa_overdue: int = 0
    capa_effectiveness: float = 0.0
    audit_findings_open: int = 0
    audit_findings_major: int = 0
    first_pass_yield: float = 0.0
    customer_satisfaction: float = 0.0
    training_compliance: float = 0.0


@dataclass
class ManagementReview:
    review_date: str
    review_type: str
    period_start: str
    period_end: str
    inputs: List[ReviewInput]
    actions: List[ActionItem]
    metrics: ReviewMetrics
    decisions: List[str] = field(default_factory=list)
    attendees: List[str] = field(default_factory=list)


class ManagementReviewTracker:
    """Tracks and reports management review status."""

    # Required ISO 13485 inputs
    REQUIRED_INPUTS = [
        ("Audit Results", "QA Manager"),
        ("Customer Feedback", "Customer Quality"),
        ("Process Performance", "Operations"),
        ("Product Conformity", "QC Manager"),
        ("CAPA Status", "CAPA Officer"),
        ("Previous Actions", "QMR"),
        ("QMS Changes", "RA Manager"),
        ("Recommendations", "All Managers"),
    ]

    def __init__(self, review: ManagementReview):
        self.review = review
        self.today = datetime.now()

    def check_input_readiness(self) -> Dict:
        """Check readiness of all required inputs."""
        readiness = {
            "total_required": len(self.REQUIRED_INPUTS),
            "complete": 0,
            "in_progress": 0,
            "not_started": 0,
            "missing_topics": [],
            "readiness_score": 0.0
        }

        input_topics = {inp.topic: inp for inp in self.review.inputs}

        for topic, responsible in self.REQUIRED_INPUTS:
            if topic in input_topics:
                inp = input_topics[topic]
                if inp.status in [InputStatus.COMPLETE, InputStatus.REVIEWED]:
                    readiness["complete"] += 1
                elif inp.status == InputStatus.IN_PROGRESS:
                    readiness["in_progress"] += 1
                else:
                    readiness["not_started"] += 1
            else:
                readiness["missing_topics"].append(topic)
                readiness["not_started"] += 1

        readiness["readiness_score"] = round(
            (readiness["complete"] / readiness["total_required"]) * 100, 1
        )

        return readiness

    def analyze_actions(self) -> Dict:
        """Analyze action item status."""
        analysis = {
            "total": len(self.review.actions),
            "by_status": {},
            "by_priority": {},
            "overdue": [],
            "due_soon": [],
            "completion_rate": 0.0
        }

        completed = 0
        for action in self.review.actions:
            # Count by status
            status = action.status.value
            analysis["by_status"][status] = analysis["by_status"].get(status, 0) + 1

            # Count by priority
            priority = action.priority.value
            analysis["by_priority"][priority] = analysis["by_priority"].get(priority, 0) + 1

            # Check completion
            if action.status in [ActionStatus.COMPLETE, ActionStatus.VERIFIED]:
                completed += 1

            # Check overdue
            if action.due_date:
                due = datetime.strptime(action.due_date, "%Y-%m-%d")
                if due < self.today and action.status not in [
                    ActionStatus.COMPLETE, ActionStatus.VERIFIED
                ]:
                    days_overdue = (self.today - due).days
                    analysis["overdue"].append({
                        "action_id": action.action_id,
                        "description": action.description[:50],
                        "owner": action.owner,
                        "days_overdue": days_overdue
                    })
                elif due <= self.today + timedelta(days=14) and action.status not in [
                    ActionStatus.COMPLETE, ActionStatus.VERIFIED
                ]:
                    days_until = (due - self.today).days
                    analysis["due_soon"].append({
                        "action_id": action.action_id,
                        "description": action.description[:50],
                        "owner": action.owner,
                        "days_until_due": days_until
                    })

        if analysis["total"] > 0:
            analysis["completion_rate"] = round((completed / analysis["total"]) * 100, 1)

        return analysis

    def assess_metrics(self) -> Dict:
        """Assess quality metrics against targets."""
        metrics = self.review.metrics
        assessment = {
            "metrics": [],
            "alerts": [],
            "overall_status": "On Track"
        }

        # Define targets and assess
        checks = [
            ("Complaint Rate", metrics.complaint_rate, 0.1, "lower"),
            ("CAPA Overdue", metrics.capa_overdue, 0, "lower"),
            ("CAPA Effectiveness", metrics.capa_effectiveness, 85.0, "higher"),
            ("First Pass Yield", metrics.first_pass_yield, 95.0, "higher"),
            ("Customer Satisfaction", metrics.customer_satisfaction, 4.0, "higher"),
            ("Training Compliance", metrics.training_compliance, 95.0, "higher"),
        ]

        warnings = 0
        critical = 0

        for name, value, target, direction in checks:
            if direction == "lower":
                status = "Pass" if value <= target else "Fail"
                threshold = target * 1.2
                warning = value > target and value <= threshold
            else:
                status = "Pass" if value >= target else "Fail"
                threshold = target * 0.9
                warning = value < target and value >= threshold

            metric_result = {
                "name": name,
                "value": value,
                "target": target,
                "status": status
            }
            assessment["metrics"].append(metric_result)

            if status == "Fail":
                if warning:
                    warnings += 1
                    assessment["alerts"].append(f"WARNING: {name} at {value} (target: {target})")
                else:
                    critical += 1
                    assessment["alerts"].append(f"CRITICAL: {name} at {value} (target: {target})")

        if critical > 0:
            assessment["overall_status"] = "Critical"
        elif warnings > 0:
            assessment["overall_status"] = "Needs Attention"

        return assessment

    def generate_recommendations(self) -> List[str]:
        """Generate recommendations based on analysis."""
        recommendations = []

        # Check input readiness
        readiness = self.check_input_readiness()
        if readiness["readiness_score"] < 100:
            recommendations.append(
                f"Complete remaining review inputs: {', '.join(readiness['missing_topics'])}"
            )

        # Check actions
        action_analysis = self.analyze_actions()
        if action_analysis["overdue"]:
            recommendations.append(
                f"Address {len(action_analysis['overdue'])} overdue action(s) immediately"
            )

        # Check metrics
        metrics_assessment = self.assess_metrics()
        if metrics_assessment["overall_status"] == "Critical":
            recommendations.append(
                "Escalate critical metric failures to senior management"
            )

        # CAPA specific
        if self.review.metrics.capa_overdue > 0:
            recommendations.append(
                f"Expedite closure of {self.review.metrics.capa_overdue} overdue CAPA(s)"
            )

        if self.review.metrics.capa_effectiveness < 85:
            recommendations.append(
                "Review root cause analysis quality for ineffective CAPAs"
            )

        # Audit findings
        if self.review.metrics.audit_findings_major > 0:
            recommendations.append(
                f"Prioritize resolution of {self.review.metrics.audit_findings_major} major audit finding(s)"
            )

        if not recommendations:
            recommendations.append("Quality system performing within targets. Maintain monitoring.")

        return recommendations

    def generate_report(self) -> Dict:
        """Generate complete review status report."""
        return {
            "review_date": self.review.review_date,
            "review_type": self.review.review_type,
            "period": f"{self.review.period_start} to {self.review.period_end}",
            "input_readiness": self.check_input_readiness(),
            "action_analysis": self.analyze_actions(),
            "metrics_assessment": self.assess_metrics(),
            "recommendations": self.generate_recommendations()
        }


def format_text_report(report: Dict) -> str:
    """Format report as text output."""
    lines = [
        "=" * 70,
        "MANAGEMENT REVIEW STATUS REPORT",
        "=" * 70,
        f"Review Date: {report['review_date']}",
        f"Review Type: {report['review_type']}",
        f"Period: {report['period']}",
        "",
        "INPUT READINESS",
        "-" * 40,
        f"Readiness Score: {report['input_readiness']['readiness_score']}%",
        f"Complete: {report['input_readiness']['complete']} / {report['input_readiness']['total_required']}",
    ]

    if report['input_readiness']['missing_topics']:
        lines.append(f"Missing: {', '.join(report['input_readiness']['missing_topics'])}")

    lines.extend([
        "",
        "ACTION STATUS",
        "-" * 40,
        f"Total Actions: {report['action_analysis']['total']}",
        f"Completion Rate: {report['action_analysis']['completion_rate']}%",
    ])

    for status, count in report['action_analysis']['by_status'].items():
        lines.append(f"  {status}: {count}")

    if report['action_analysis']['overdue']:
        lines.extend([
            "",
            "OVERDUE ACTIONS:",
        ])
        for item in report['action_analysis']['overdue']:
            lines.append(f"  [{item['action_id']}] {item['description']} - {item['days_overdue']} days overdue")

    lines.extend([
        "",
        "METRICS ASSESSMENT",
        "-" * 40,
        f"Overall Status: {report['metrics_assessment']['overall_status']}",
        "",
        f"{'Metric':<25} {'Value':<10} {'Target':<10} {'Status':<10}",
        "-" * 55,
    ])

    for metric in report['metrics_assessment']['metrics']:
        lines.append(
            f"{metric['name']:<25} {metric['value']:<10} {metric['target']:<10} {metric['status']:<10}"
        )

    if report['metrics_assessment']['alerts']:
        lines.extend([
            "",
            "ALERTS:",
        ])
        for alert in report['metrics_assessment']['alerts']:
            lines.append(f"  ! {alert}")

    lines.extend([
        "",
        "RECOMMENDATIONS",
        "-" * 40,
    ])

    for i, rec in enumerate(report['recommendations'], 1):
        lines.append(f"{i}. {rec}")

    lines.append("=" * 70)
    return "\n".join(lines)


def interactive_mode():
    """Run interactive review data entry."""
    print("=" * 60)
    print("Management Review Tracker - Interactive Mode")
    print("=" * 60)

    review_date = input("\nReview Date (YYYY-MM-DD): ").strip()
    review_type = input("Review Type (Annual/Semi-annual/Quarterly): ").strip()
    period_start = input("Period Start (YYYY-MM-DD): ").strip()
    period_end = input("Period End (YYYY-MM-DD): ").strip()

    print("\nEnter Quality Metrics:")
    metrics = ReviewMetrics(
        complaint_rate=float(input("Complaint Rate (%): ") or 0),
        complaint_count=int(input("Complaint Count: ") or 0),
        capa_open=int(input("Open CAPAs: ") or 0),
        capa_overdue=int(input("Overdue CAPAs: ") or 0),
        capa_effectiveness=float(input("CAPA Effectiveness (%): ") or 0),
        audit_findings_open=int(input("Open Audit Findings: ") or 0),
        audit_findings_major=int(input("Major Audit Findings: ") or 0),
        first_pass_yield=float(input("First Pass Yield (%): ") or 0),
        customer_satisfaction=float(input("Customer Satisfaction (1-5): ") or 0),
        training_compliance=float(input("Training Compliance (%): ") or 0)
    )

    # Create review with sample inputs
    inputs = [
        ReviewInput(topic=topic, responsible=resp, status=InputStatus.COMPLETE, data_period=f"{period_start} to {period_end}")
        for topic, resp in ManagementReviewTracker.REQUIRED_INPUTS
    ]

    review = ManagementReview(
        review_date=review_date,
        review_type=review_type,
        period_start=period_start,
        period_end=period_end,
        inputs=inputs,
        actions=[],
        metrics=metrics
    )

    tracker = ManagementReviewTracker(review)
    report = tracker.generate_report()
    print("\n" + format_text_report(report))


def main():
    parser = argparse.ArgumentParser(
        description="Management Review Tracker"
    )
    parser.add_argument(
        "--data",
        type=str,
        help="JSON file with review data"
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
        help="Generate sample review data"
    )

    args = parser.parse_args()

    if args.interactive:
        interactive_mode()
        return

    if args.sample:
        sample = {
            "review_date": "2024-06-30",
            "review_type": "Semi-annual",
            "period_start": "2024-01-01",
            "period_end": "2024-06-30",
            "inputs": [
                {"topic": "Audit Results", "responsible": "QA Manager", "status": "Complete", "data_period": "H1 2024"},
                {"topic": "Customer Feedback", "responsible": "Customer Quality", "status": "Complete", "data_period": "H1 2024"},
                {"topic": "Process Performance", "responsible": "Operations", "status": "In Progress", "data_period": "H1 2024"},
                {"topic": "CAPA Status", "responsible": "CAPA Officer", "status": "Complete", "data_period": "Current"}
            ],
            "actions": [
                {
                    "action_id": "MR-2024-001",
                    "description": "Implement enhanced CAPA tracking system",
                    "owner": "QA Manager",
                    "due_date": "2024-09-30",
                    "priority": "High",
                    "status": "In Progress",
                    "source_review": "2024-Q1"
                }
            ],
            "metrics": {
                "complaint_rate": 0.08,
                "complaint_count": 12,
                "capa_open": 8,
                "capa_overdue": 2,
                "capa_effectiveness": 88.0,
                "audit_findings_open": 5,
                "audit_findings_major": 1,
                "first_pass_yield": 96.5,
                "customer_satisfaction": 4.2,
                "training_compliance": 97.0
            }
        }
        print(json.dumps(sample, indent=2))
        return

    # Create sample review if no data provided
    if args.data:
        with open(args.data, "r") as f:
            data = json.load(f)

        inputs = [
            ReviewInput(
                topic=inp["topic"],
                responsible=inp["responsible"],
                status=InputStatus[inp["status"].upper().replace(" ", "_")],
                data_period=inp.get("data_period", "")
            )
            for inp in data.get("inputs", [])
        ]

        actions = [
            ActionItem(
                action_id=act["action_id"],
                description=act["description"],
                owner=act["owner"],
                due_date=act["due_date"],
                priority=ActionPriority[act["priority"].upper()],
                status=ActionStatus[act["status"].upper().replace(" ", "_")],
                source_review=act.get("source_review", "")
            )
            for act in data.get("actions", [])
        ]

        metrics_data = data.get("metrics", {})
        metrics = ReviewMetrics(**metrics_data)

        review = ManagementReview(
            review_date=data["review_date"],
            review_type=data["review_type"],
            period_start=data["period_start"],
            period_end=data["period_end"],
            inputs=inputs,
            actions=actions,
            metrics=metrics
        )
    else:
        # Demo data
        review = ManagementReview(
            review_date="2024-06-30",
            review_type="Semi-annual",
            period_start="2024-01-01",
            period_end="2024-06-30",
            inputs=[
                ReviewInput("Audit Results", "QA Manager", InputStatus.COMPLETE, "H1 2024"),
                ReviewInput("Customer Feedback", "Customer Quality", InputStatus.COMPLETE, "H1 2024"),
                ReviewInput("CAPA Status", "CAPA Officer", InputStatus.COMPLETE, "Current"),
            ],
            actions=[
                ActionItem("MR-2024-001", "Implement CAPA tracking", "QA Mgr", "2024-09-30",
                          ActionPriority.HIGH, ActionStatus.IN_PROGRESS, "2024-Q1"),
            ],
            metrics=ReviewMetrics(
                complaint_rate=0.08, capa_open=8, capa_overdue=2,
                capa_effectiveness=88.0, first_pass_yield=96.5,
                customer_satisfaction=4.2, training_compliance=97.0
            )
        )

    tracker = ManagementReviewTracker(review)
    report = tracker.generate_report()

    if args.output == "json":
        print(json.dumps(report, indent=2))
    else:
        print(format_text_report(report))


if __name__ == "__main__":
    main()
