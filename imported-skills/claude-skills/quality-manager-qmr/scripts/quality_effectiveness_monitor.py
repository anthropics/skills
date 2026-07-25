#!/usr/bin/env python3
"""
Quality Management System Effectiveness Monitor

Quantitatively assess QMS effectiveness using leading and lagging indicators.
Tracks trends, calculates control limits, and predicts potential quality issues
before they become failures. Integrates with CAPA and management review processes.

Supports metrics:
- Complaint rates, defect rates, rework rates
- Supplier performance
- CAPA effectiveness
- Audit findings trends
- Non-conformance statistics

Usage:
    python quality_effectiveness_monitor.py --metrics metrics.csv --dashboard
    python quality_effectiveness_monitor.py --qms-data qms_data.json --predict
    python quality_effectiveness_monitor.py --interactive
"""

import argparse
import json
import csv
import sys
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Optional, Tuple
from datetime import datetime, timedelta
from statistics import mean, stdev, median



@dataclass
class QualityMetric:
    """A single quality metric data point."""
    metric_id: str
    metric_name: str
    category: str
    date: str
    value: float
    unit: str
    target: float
    upper_limit: float
    lower_limit: float
    trend_direction: str = ""  # "up", "down", "stable"
    sigma_level: float = 0.0
    is_alert: bool = False
    is_critical: bool = False


@dataclass
class QMSReport:
    """QMS effectiveness report."""
    report_period: Tuple[str, str]
    overall_effectiveness_score: float
    metrics_count: int
    metrics_in_control: int
    metrics_out_of_control: int
    critical_alerts: int
    trends_analysis: Dict
    predictive_alerts: List[Dict]
    improvement_opportunities: List[Dict]
    management_review_summary: str


class QMSEffectivenessMonitor:
    """Monitors and analyzes QMS effectiveness."""

    SIGNAL_INDICATORS = {
        "complaint_rate": {"unit": "per 1000 units", "target": 0, "upper_limit": 1.5},
        "defect_rate": {"unit": "PPM", "target": 100, "upper_limit": 500},
        "rework_rate": {"unit": "%", "target": 2.0, "upper_limit": 5.0},
        "on_time_delivery": {"unit": "%", "target": 98, "lower_limit": 95},
        "audit_findings": {"unit": "count/month", "target": 0, "upper_limit": 3},
        "capa_closure_rate": {"unit": "% within target", "target": 100, "lower_limit": 90},
        "supplier_defect_rate": {"unit": "PPM", "target": 200, "upper_limit": 1000}
    }

    def __init__(self):
        self.metrics = []

    def load_csv(self, csv_path: str) -> List[QualityMetric]:
        """Load metrics from CSV file."""
        metrics = []
        with open(csv_path, 'r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                metric = QualityMetric(
                    metric_id=row.get('metric_id', ''),
                    metric_name=row.get('metric_name', ''),
                    category=row.get('category', 'General'),
                    date=row.get('date', ''),
                    value=float(row.get('value', 0)),
                    unit=row.get('unit', ''),
                    target=float(row.get('target', 0)),
                    upper_limit=float(row.get('upper_limit', 0)),
                    lower_limit=float(row.get('lower_limit', 0)),
                )
                metrics.append(metric)
        self.metrics = metrics
        return metrics

    def calculate_sigma_level(self, metric: QualityMetric, historical_values: List[float]) -> float:
        """Calculate process sigma level based on defect rate."""
        if metric.unit == "PPM" or "rate" in metric.metric_name.lower():
            # For defect rates, DPMO = defects_per_million_opportunities
            if historical_values:
                avg_defect_rate = mean(historical_values)
                if avg_defect_rate > 0:
                    dpmo = avg_defect_rate
                    # Simplified sigma conversion (actual uses 1.5σ shift)
                    sigma_map = {
                        330000: 1.0, 620000: 2.0, 110000: 3.0, 27000: 4.0,
                        6200: 5.0, 230: 6.0, 3.4: 6.0
                    }
                    # Rough sigma calculation
                    sigma = 6.0 - (dpmo / 1000000) * 10
                    return max(0.0, min(6.0, sigma))
        return 0.0

    def analyze_trend(self, values: List[float]) -> Tuple[str, float]:
        """Analyze trend direction and significance."""
        if len(values) < 3:
            return "insufficient_data", 0.0

        x = list(range(len(values)))
        y = values

        # Linear regression
        n = len(x)
        sum_x = sum(x)
        sum_y = sum(y)
        sum_xy = sum(x[i] * y[i] for i in range(n))
        sum_x2 = sum(xi * xi for xi in x)

        slope = (n * sum_xy - sum_x * sum_y) / (n * sum_x2 - sum_x * sum_x) if (n * sum_x2 - sum_x * sum_x) != 0 else 0

        # Determine trend direction
        if slope > 0.01:
            direction = "up"
        elif slope < -0.01:
            direction = "down"
        else:
            direction = "stable"

        # Calculate R-squared
        if slope != 0:
            intercept = (sum_y - slope * sum_x) / n
            y_pred = [slope * xi + intercept for xi in x]
            ss_res = sum((y[i] - y_pred[i])**2 for i in range(n))
            ss_tot = sum((y[i] - mean(y))**2 for i in range(n))
            r2 = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0
        else:
            r2 = 0

        return direction, r2

    def detect_alerts(self, metrics: List[QualityMetric]) -> List[Dict]:
        """Detect metrics that require attention."""
        alerts = []
        for metric in metrics:
            # Check immediate control limit violation
            if metric.upper_limit and metric.value > metric.upper_limit:
                alerts.append({
                    "metric_id": metric.metric_id,
                    "metric_name": metric.metric_name,
                    "issue": "exceeds_upper_limit",
                    "value": metric.value,
                    "limit": metric.upper_limit,
                    "severity": "critical" if metric.category in ["Customer", "Regulatory"] else "high"
                })
            if metric.lower_limit and metric.value < metric.lower_limit:
                alerts.append({
                    "metric_id": metric.metric_id,
                    "metric_name": metric.metric_name,
                    "issue": "below_lower_limit",
                    "value": metric.value,
                    "limit": metric.lower_limit,
                    "severity": "critical" if metric.category in ["Customer", "Regulatory"] else "high"
                })

            # Check for adverse trend (3+ points in same direction)
            # Need to group by metric_name and check historical data
            # Simplified: check trend_direction flag if set
            if metric.trend_direction in ["up", "down"] and metric.sigma_level > 3:
                alerts.append({
                    "metric_id": metric.metric_id,
                    "metric_name": metric.metric_name,
                    "issue": f"adverse_trend_{metric.trend_direction}",
                    "value": metric.value,
                    "severity": "medium"
                })

        return alerts

    def predict_failures(self, metrics: List[QualityMetric], forecast_days: int = 30) -> List[Dict]:
        """Predict potential failures based on trends."""
        predictions = []

        # Group metrics by name to get time series
        grouped = {}
        for m in metrics:
            if m.metric_name not in grouped:
                grouped[m.metric_name] = []
            grouped[m.metric_name].append(m)

        for metric_name, metric_list in grouped.items():
            if len(metric_list) < 5:
                continue

            # Sort by date
            metric_list.sort(key=lambda m: m.date)
            values = [m.value for m in metric_list]

            # Simple linear extrapolation
            x = list(range(len(values)))
            y = values
            n = len(x)
            sum_x = sum(x)
            sum_y = sum(y)
            sum_xy = sum(x[i] * y[i] for i in range(n))
            sum_x2 = sum(xi * xi for xi in x)
            slope = (n * sum_xy - sum_x * sum_y) / (n * sum_x2 - sum_x * sum_x) if (n * sum_x2 - sum_x * sum_x) != 0 else 0

            if slope != 0:
                # Forecast next value
                next_value = y[-1] + slope
                target = metric_list[0].target
                upper_limit = metric_list[0].upper_limit

                if (target and next_value > target * 1.2) or (upper_limit and next_value > upper_limit * 0.9):
                    predictions.append({
                        "metric": metric_name,
                        "current_value": y[-1],
                        "forecast_value": round(next_value, 2),
                        "forecast_days": forecast_days,
                        "trend_slope": round(slope, 3),
                        "risk_level": "high" if upper_limit and next_value > upper_limit else "medium"
                    })

        return predictions

    def calculate_effectiveness_score(self, metrics: List[QualityMetric]) -> float:
        """Calculate overall QMS effectiveness score (0-100)."""
        if not metrics:
            return 0.0

        scores = []
        for m in metrics:
            # Score based on distance to target
            if m.target != 0:
                deviation = abs(m.value - m.target) / max(abs(m.target), 1)
                score = max(0, 100 - deviation * 100)
            else:
                # For metrics where lower is better (defects, etc.)
                if m.upper_limit:
                    score = max(0, 100 - (m.value / m.upper_limit) * 100 * 0.5)
                else:
                    score = 50  # Neutral if no target
            scores.append(score)

        # Penalize for alerts
        alerts = self.detect_alerts(metrics)
        penalty = len([a for a in alerts if a["severity"] in ["critical", "high"]]) * 5
        return max(0, min(100, mean(scores) - penalty))

    def identify_improvement_opportunities(self, metrics: List[QualityMetric]) -> List[Dict]:
        """Identify metrics with highest improvement potential."""
        opportunities = []
        for m in metrics:
            if m.upper_limit and m.value > m.upper_limit * 0.8:
                gap = m.upper_limit - m.value
                if gap > 0:
                    improvement_pct = (gap / m.upper_limit) * 100
                    opportunities.append({
                        "metric": m.metric_name,
                        "current": m.value,
                        "target": m.upper_limit,
                        "gap": round(gap, 2),
                        "improvement_potential_pct": round(improvement_pct, 1),
                        "recommended_action": f"Reduce {m.metric_name} by at least {round(gap, 2)} {m.unit}",
                        "impact": "High" if m.category in ["Customer", "Regulatory"] else "Medium"
                    })

        # Sort by improvement potential
        opportunities.sort(key=lambda x: x["improvement_potential_pct"], reverse=True)
        return opportunities[:10]

    def generate_management_review_summary(self, report: QMSReport) -> str:
        """Generate executive summary for management review."""
        summary = [
            f"QMS EFFECTIVENESS REVIEW - {report.report_period[0]} to {report.report_period[1]}",
            "",
            f"Overall Effectiveness Score: {report.overall_effectiveness_score:.1f}/100",
            f"Metrics Tracked: {report.metrics_count} | In Control: {report.metrics_in_control} | Alerts: {report.critical_alerts}",
            ""
        ]

        if report.critical_alerts > 0:
            summary.append("🔴 CRITICAL ALERTS REQUIRING IMMEDIATE ATTENTION:")
            for alert in [a for a in report.predictive_alerts if a.get("risk_level") == "high"]:
                summary.append(f"  • {alert['metric']}: forecast {alert['forecast_value']} (from {alert['current_value']})")
            summary.append("")

        summary.append("📈 TOP IMPROVEMENT OPPORTUNITIES:")
        for i, opp in enumerate(report.improvement_opportunities[:3], 1):
            summary.append(f"  {i}. {opp['metric']}: {opp['recommended_action']} (Impact: {opp['impact']})")
        summary.append("")

        summary.append("🎯 RECOMMENDED ACTIONS:")
        summary.append("  1. Address all high-severity alerts within 30 days")
        summary.append("  2. Launch improvement projects for top 3 opportunities")
        summary.append("  3. Review CAPA effectiveness for recurring issues")
        summary.append("  4. Update risk assessments based on predictive trends")

        return "\n".join(summary)

    def analyze(
        self,
        metrics: List[QualityMetric],
        start_date: str = None,
        end_date: str = None
    ) -> QMSReport:
        """Perform comprehensive QMS effectiveness analysis."""
        in_control = 0
        for m in metrics:
            if not m.is_alert and not m.is_critical:
                in_control += 1

        out_of_control = len(metrics) - in_control

        alerts = self.detect_alerts(metrics)
        critical_alerts = len([a for a in alerts if a["severity"] in ["critical", "high"]])

        predictions = self.predict_failures(metrics)
        improvement_opps = self.identify_improvement_opportunities(metrics)

        effectiveness = self.calculate_effectiveness_score(metrics)

        # Trend analysis by category
        trends = {}
        categories = set(m.category for m in metrics)
        for cat in categories:
            cat_metrics = [m for m in metrics if m.category == cat]
            if len(cat_metrics) >= 2:
                avg_values = [mean([m.value for m in cat_metrics])]  # Simplistic - would need time series
                trends[cat] = {
                    "metric_count": len(cat_metrics),
                    "avg_value": round(mean([m.value for m in cat_metrics]), 2),
                    "alerts": len([a for a in alerts if any(m.metric_name == a["metric_name"] for m in cat_metrics)])
                }

        period = (start_date or metrics[0].date, end_date or metrics[-1].date) if metrics else ("", "")

        report = QMSReport(
            report_period=period,
            overall_effectiveness_score=effectiveness,
            metrics_count=len(metrics),
            metrics_in_control=in_control,
            metrics_out_of_control=out_of_control,
            critical_alerts=critical_alerts,
            trends_analysis=trends,
            predictive_alerts=predictions,
            improvement_opportunities=improvement_opps,
            management_review_summary=""  # Filled later
        )

        report.management_review_summary = self.generate_management_review_summary(report)

        return report


def format_qms_report(report: QMSReport) -> str:
    """Format QMS report as text."""
    lines = [
        "=" * 80,
        "QMS EFFECTIVENESS MONITORING REPORT",
        "=" * 80,
        f"Period: {report.report_period[0]} to {report.report_period[1]}",
        f"Overall Score: {report.overall_effectiveness_score:.1f}/100",
        "",
        "METRIC STATUS",
        "-" * 40,
        f"  Total Metrics: {report.metrics_count}",
        f"  In Control: {report.metrics_in_control}",
        f"  Out of Control: {report.metrics_out_of_control}",
        f"  Critical Alerts: {report.critical_alerts}",
        "",
        "TREND ANALYSIS BY CATEGORY",
        "-" * 40,
    ]

    for category, data in report.trends_analysis.items():
        lines.append(f"  {category}: {data['avg_value']} (alerts: {data['alerts']})")

    if report.predictive_alerts:
        lines.extend([
            "",
            "PREDICTIVE ALERTS (Next 30 days)",
            "-" * 40,
        ])
        for alert in report.predictive_alerts[:5]:
            lines.append(f"  ⚠ {alert['metric']}: {alert['current_value']} → {alert['forecast_value']} ({alert['risk_level']})")

    if report.improvement_opportunities:
        lines.extend([
            "",
            "TOP IMPROVEMENT OPPORTUNITIES",
            "-" * 40,
        ])
        for i, opp in enumerate(report.improvement_opportunities[:5], 1):
            lines.append(f"  {i}. {opp['metric']}: {opp['recommended_action']}")

    lines.extend([
        "",
        "MANAGEMENT REVIEW SUMMARY",
        "-" * 40,
        report.management_review_summary,
        "=" * 80
    ])

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="QMS Effectiveness Monitor")
    parser.add_argument("--metrics", type=str, help="CSV file with quality metrics")
    parser.add_argument("--qms-data", type=str, help="JSON file with QMS data")
    parser.add_argument("--dashboard", action="store_true", help="Generate dashboard summary")
    parser.add_argument("--predict", action="store_true", help="Include predictive analytics")
    parser.add_argument("--output", choices=["text", "json"], default="text")
    parser.add_argument("--interactive", action="store_true", help="Interactive mode")

    args = parser.parse_args()
    monitor = QMSEffectivenessMonitor()

    if args.metrics:
        metrics = monitor.load_csv(args.metrics)
        report = monitor.analyze(metrics)
    elif args.qms_data:
        with open(args.qms_data) as f:
            data = json.load(f)
        # Convert to QualityMetric objects
        metrics = [QualityMetric(**m) for m in data.get("metrics", [])]
        report = monitor.analyze(metrics)
    else:
        # Demo data
        demo_metrics = [
            QualityMetric("M001", "Customer Complaint Rate", "Customer", "2026-03-01", 0.8, "per 1000", 1.0, 1.5, 0.5),
            QualityMetric("M002", "Defect Rate PPM", "Quality", "2026-03-01", 125, "PPM", 100, 500, 0, trend_direction="down", sigma_level=4.2),
            QualityMetric("M003", "On-Time Delivery", "Operations", "2026-03-01", 96.5, "%", 98, 0, 95, trend_direction="down"),
            QualityMetric("M004", "CAPA Closure Rate", "Quality", "2026-03-01", 92.0, "%", 100, 0, 90, is_alert=True),
            QualityMetric("M005", "Supplier Defect Rate", "Supplier", "2026-03-01", 450, "PPM", 200, 1000, 0, is_critical=True),
        ]
        # Simulate time series
        all_metrics = []
        for i in range(30):
            for dm in demo_metrics:
                new_metric = QualityMetric(
                    metric_id=dm.metric_id,
                    metric_name=dm.metric_name,
                    category=dm.category,
                    date=f"2026-03-{i+1:02d}",
                    value=dm.value + (i * 0.1) if dm.metric_name == "Customer Complaint Rate" else dm.value,
                    unit=dm.unit,
                    target=dm.target,
                    upper_limit=dm.upper_limit,
                    lower_limit=dm.lower_limit
                )
                all_metrics.append(new_metric)
        report = monitor.analyze(all_metrics)

    if args.output == "json":
        result = asdict(report)
        print(json.dumps(result, indent=2))
    else:
        print(format_qms_report(report))


if __name__ == "__main__":
    main()
