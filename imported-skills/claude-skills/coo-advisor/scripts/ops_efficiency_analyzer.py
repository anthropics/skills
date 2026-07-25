#!/usr/bin/env python3
"""
ops_efficiency_analyzer.py — Operational Efficiency Analyzer

Analyzes startup operational efficiency using Theory of Constraints,
process maturity scoring, and bottleneck identification.

Usage:
    python ops_efficiency_analyzer.py                    # Runs with sample data
    python ops_efficiency_analyzer.py --input data.json  # Custom data
    python ops_efficiency_analyzer.py --input data.json --output report.txt

Input format: See SAMPLE_DATA at bottom of file.
"""

import json
import sys
import argparse
import math
from datetime import datetime
from typing import Any, Optional


# ---------------------------------------------------------------------------
# Data Models (plain dicts with type aliases for clarity)
# ---------------------------------------------------------------------------

ProcessData = dict[str, Any]
TeamData = dict[str, Any]
MetricsData = dict[str, Any]


# ---------------------------------------------------------------------------
# Process Maturity Scoring
# ---------------------------------------------------------------------------

MATURITY_LEVELS = {
    1: "Ad Hoc",
    2: "Defined",
    3: "Managed",
    4: "Optimized",
    5: "Innovating",
}

MATURITY_DESCRIPTIONS = {
    1: "No documented process. Outcomes depend on individual heroics.",
    2: "Process exists and is documented. Inconsistently followed.",
    3: "Process is followed consistently. Metrics are tracked.",
    4: "Process is optimized based on metrics. Proactively improved.",
    5: "Process enables competitive advantage. Continuously innovating.",
}

MATURITY_CRITERIA = {
    "documentation": {
        "weight": 0.20,
        "levels": {
            0: "No documentation",
            1: "Informal notes or tribal knowledge",
            2: "Process documented but not maintained",
            3: "Documented, current, accessible",
            4: "Documented with examples, edge cases, and owner",
            5: "Living doc with version history and improvement log",
        },
    },
    "ownership": {
        "weight": 0.15,
        "levels": {
            0: "No owner",
            1: "Unclear ownership, multiple people responsible",
            2: "Named team responsible",
            3: "Named individual DRI",
            4: "DRI with metrics accountability",
            5: "DRI with improvement mandate and resources",
        },
    },
    "metrics": {
        "weight": 0.20,
        "levels": {
            0: "No metrics",
            1: "Anecdotal measurement",
            2: "Some metrics tracked, not regularly reviewed",
            3: "Key metrics tracked and reviewed monthly",
            4: "Metrics drive decisions, targets set",
            5: "Predictive metrics, benchmarked externally",
        },
    },
    "automation": {
        "weight": 0.20,
        "levels": {
            0: "100% manual",
            1: "Mostly manual, some tools used",
            2: "Key steps automated, significant manual work remains",
            3: "Majority automated, manual exception handling",
            4: "Mostly automated with exception playbooks",
            5: "Fully automated with human oversight only",
        },
    },
    "consistency": {
        "weight": 0.15,
        "levels": {
            0: "Never consistent",
            1: "Consistent <50% of time",
            2: "Consistent 50-75% of time",
            3: "Consistent 75-90% of time",
            4: "Consistent >90% of time",
            5: "Six Sigma level (>99.7%)",
        },
    },
    "feedback_loop": {
        "weight": 0.10,
        "levels": {
            0: "No feedback loop",
            1: "Ad hoc complaints surface issues",
            2: "Periodic review when problems arise",
            3: "Regular review cadence",
            4: "Structured improvement cycles",
            5: "Real-time feedback with automated triggers",
        },
    },
}


def score_process_maturity(process: ProcessData) -> dict[str, Any]:
    """
    Score a single process on 1-5 maturity scale.
    Returns scored process with dimension breakdown and recommendations.
    """
    maturity_inputs = process.get("maturity", {})
    total_score = 0.0
    dimension_scores = {}
    recommendations = []

    for dimension, config in MATURITY_CRITERIA.items():
        raw_score = maturity_inputs.get(dimension, 0)
        # Normalize raw score (0-5) to weight
        normalized = (raw_score / 5.0) * config["weight"] * 5
        total_score += normalized
        dimension_scores[dimension] = raw_score

        # Generate recommendation if below threshold
        if raw_score < 3:
            severity = "🔴 Critical" if raw_score < 2 else "🟡 Needs work"
            recommendations.append({
                "dimension": dimension,
                "current_score": raw_score,
                "target_score": 3,
                "severity": severity,
                "action": _get_improvement_action(dimension, raw_score),
            })

    # Clamp to 1-5 range (scores can't be below 1 for a running process)
    maturity_score = max(1.0, min(5.0, total_score))
    maturity_level = round(maturity_score)

    return {
        "name": process["name"],
        "maturity_score": round(maturity_score, 2),
        "maturity_level": maturity_level,
        "maturity_label": MATURITY_LEVELS[maturity_level],
        "dimension_scores": dimension_scores,
        "recommendations": recommendations,
        "process_data": process,
    }


def _get_improvement_action(dimension: str, current_score: int) -> str:
    """Return a concrete improvement action for a given dimension and score."""
    actions = {
        "documentation": {
            0: "Write a basic SOP this week: trigger, steps, owner, done-definition",
            1: "Convert tribal knowledge into a written process doc with clear steps",
            2: "Assign a process owner to maintain and update documentation quarterly",
        },
        "ownership": {
            0: "Assign a DRI (Directly Responsible Individual) today",
            1: "Clarify ownership: assign one named person, remove ambiguity",
            2: "Give the named owner accountability for process metrics",
        },
        "metrics": {
            0: "Define 1-2 metrics that measure if this process is working",
            1: "Set up automated metric collection and add to monthly review",
            2: "Set targets for each metric and review monthly",
        },
        "automation": {
            0: "Identify the highest-volume manual step; automate it first",
            1: "Run automation ROI calc — if payback <12 months, build it",
            2: "Automate exception routing and error notifications",
        },
        "consistency": {
            0: "Root-cause why the process fails; fix the #1 failure mode",
            1: "Create a checklist for the process; require sign-off",
            2: "Add process adherence check to team's weekly review",
        },
        "feedback_loop": {
            0: "Add this process to monthly operational review agenda",
            1: "Create a feedback channel (Slack thread, form) for process issues",
            2: "Set a quarterly review date for this process",
        },
    }
    return actions.get(dimension, {}).get(current_score, "Improve this dimension")


# ---------------------------------------------------------------------------
# Bottleneck Analysis (Theory of Constraints)
# ---------------------------------------------------------------------------

def analyze_bottlenecks(processes: list[ProcessData]) -> dict[str, Any]:
    """
    Identify bottlenecks using throughput analysis.
    Bottleneck = step with lowest throughput (or highest queue buildup).
    """
    bottlenecks = []
    throughput_chain = []

    for process in processes:
        steps = process.get("steps", [])
        if not steps:
            continue

        step_analysis = []
        min_throughput = float("inf")
        bottleneck_step = None

        for step in steps:
            throughput = step.get("throughput_per_day", 0)
            queue_depth = step.get("current_queue", 0)
            avg_wait_hours = step.get("avg_wait_hours", 0)

            # Utilization estimate
            capacity = step.get("capacity_per_day", throughput * 1.2)
            utilization = (throughput / capacity * 100) if capacity > 0 else 100

            step_info = {
                "name": step["name"],
                "throughput_per_day": throughput,
                "queue_depth": queue_depth,
                "avg_wait_hours": avg_wait_hours,
                "utilization_pct": round(utilization, 1),
                "is_bottleneck": False,
            }
            step_analysis.append(step_info)

            if throughput < min_throughput:
                min_throughput = throughput
                bottleneck_step = step_info

        if bottleneck_step:
            bottleneck_step["is_bottleneck"] = True

            # Calculate flow efficiency
            total_lead_time = sum(
                s.get("avg_wait_hours", 0) + s.get("avg_process_hours", 1)
                for s in steps
            )
            total_process_time = sum(s.get("avg_process_hours", 1) for s in steps)
            flow_efficiency = (
                (total_process_time / total_lead_time * 100)
                if total_lead_time > 0
                else 0
            )

            bottlenecks.append({
                "process": process["name"],
                "bottleneck_step": bottleneck_step["name"],
                "bottleneck_throughput": min_throughput,
                "bottleneck_queue": bottleneck_step["queue_depth"],
                "flow_efficiency_pct": round(flow_efficiency, 1),
                "steps": step_analysis,
                "toc_recommendation": _generate_toc_recommendation(
                    bottleneck_step, process
                ),
            })

        throughput_chain.append({
            "process": process["name"],
            "steps": step_analysis,
        })

    # Rank bottlenecks by severity (queue depth × utilization)
    for b in bottlenecks:
        b["severity_score"] = b["bottleneck_queue"] * (b["bottleneck_throughput"] or 1)
    bottlenecks.sort(key=lambda x: x["severity_score"], reverse=True)

    return {
        "bottlenecks": bottlenecks,
        "throughput_chain": throughput_chain,
    }


def _generate_toc_recommendation(bottleneck_step: dict, process: ProcessData) -> str:
    """Generate a Theory of Constraints recommendation for a bottleneck."""
    util = bottleneck_step["utilization_pct"]
    queue = bottleneck_step["queue_depth"]
    step_name = bottleneck_step["name"]

    if util >= 90:
        return (
            f"ELEVATE: '{step_name}' is at {util}% utilization — at capacity. "
            f"Add resources (people, automation, or parallel processing) immediately. "
            f"Queue of {queue} units will grow until capacity is increased."
        )
    elif util >= 70:
        return (
            f"EXPLOIT: '{step_name}' has capacity headroom but is the constraint. "
            f"Eliminate non-value-add work in this step. Protect it from interruptions. "
            f"Ensure upstream steps feed it steadily, not in batches."
        )
    else:
        return (
            f"INVESTIGATE: '{step_name}' shows low throughput ({bottleneck_step['throughput_per_day']}/day) "
            f"despite available capacity. Root cause may be upstream blocking, "
            f"unclear handoffs, or quality issues requiring rework."
        )


# ---------------------------------------------------------------------------
# Team Structure Analysis
# ---------------------------------------------------------------------------

def analyze_team_structure(team: TeamData) -> dict[str, Any]:
    """
    Analyze team structure for span of control, layer count, and hiring gaps.
    """
    issues = []
    recommendations = []
    warnings = []

    total_headcount = team.get("total_headcount", 0)
    departments = team.get("departments", [])

    # Span of control analysis
    span_issues = []
    for dept in departments:
        for manager in dept.get("managers", []):
            direct_reports = manager.get("direct_reports", 0)
            manages_managers = manager.get("manages_managers", False)

            optimal_min = 3 if manages_managers else 5
            optimal_max = 5 if manages_managers else 8

            if direct_reports < optimal_min:
                span_issues.append({
                    "manager": manager["name"],
                    "dept": dept["name"],
                    "reports": direct_reports,
                    "issue": "Under-span",
                    "recommendation": f"Merge team or promote ICs — {direct_reports} reports is management overhead",
                })
            elif direct_reports > optimal_max:
                span_issues.append({
                    "manager": manager["name"],
                    "dept": dept["name"],
                    "reports": direct_reports,
                    "issue": "Over-span",
                    "recommendation": f"Split team — {direct_reports} reports means minimal 1:1 time and poor feedback loops",
                })

    # Management layers analysis
    max_layers = team.get("management_layers", 0)
    expected_layers = _expected_layers(total_headcount)
    if max_layers > expected_layers + 1:
        issues.append({
            "type": "Over-layered",
            "detail": f"{max_layers} management layers for {total_headcount} people. "
                      f"Expected: {expected_layers}. Excess layers slow decisions.",
            "recommendation": "Flatten: remove middle management layers that don't add decision value",
        })

    # Revenue per employee by department
    annual_revenue = team.get("annual_revenue_usd", 0)
    dept_analysis = []
    for dept in departments:
        headcount = dept.get("headcount", 0)
        if headcount > 0 and annual_revenue > 0:
            rev_per_employee = annual_revenue / headcount
            benchmark = _dept_revenue_benchmark(dept["name"], team.get("stage", "series_a"))
            efficiency_pct = (rev_per_employee / benchmark * 100) if benchmark > 0 else None

            dept_analysis.append({
                "department": dept["name"],
                "headcount": headcount,
                "revenue_per_employee": round(rev_per_employee),
                "benchmark": benchmark,
                "efficiency_vs_benchmark_pct": round(efficiency_pct, 1) if efficiency_pct else "N/A",
                "status": _efficiency_status(efficiency_pct),
            })

    # Open req health
    open_reqs = team.get("open_requisitions", 0)
    req_to_headcount_ratio = (open_reqs / total_headcount * 100) if total_headcount > 0 else 0
    if req_to_headcount_ratio > 20:
        warnings.append(
            f"High open req ratio: {open_reqs} open reqs against {total_headcount} headcount "
            f"({req_to_headcount_ratio:.0f}%). This level of hiring while operating is operationally disruptive."
        )

    return {
        "total_headcount": total_headcount,
        "management_layers": max_layers,
        "expected_layers": expected_layers,
        "span_of_control_issues": span_issues,
        "structural_issues": issues,
        "department_efficiency": dept_analysis,
        "open_req_health": {
            "open_reqs": open_reqs,
            "ratio_pct": round(req_to_headcount_ratio, 1),
            "warnings": warnings,
        },
    }


def _expected_layers(headcount: int) -> int:
    if headcount <= 15:
        return 1
    elif headcount <= 50:
        return 2
    elif headcount <= 150:
        return 3
    elif headcount <= 500:
        return 4
    else:
        return 5


def _dept_revenue_benchmark(dept_name: str, stage: str) -> int:
    """Revenue per employee benchmark by department and stage (USD)."""
    benchmarks = {
        "series_a": {
            "engineering": 400000,
            "sales": 250000,
            "customer_success": 300000,
            "marketing": 500000,
            "operations": 400000,
            "product": 400000,
            "default": 200000,
        },
        "series_b": {
            "engineering": 500000,
            "sales": 350000,
            "customer_success": 400000,
            "marketing": 700000,
            "operations": 500000,
            "product": 500000,
            "default": 300000,
        },
        "series_c": {
            "engineering": 600000,
            "sales": 450000,
            "customer_success": 500000,
            "marketing": 900000,
            "operations": 600000,
            "product": 600000,
            "default": 400000,
        },
    }
    stage_data = benchmarks.get(stage, benchmarks["series_a"])
    dept_key = dept_name.lower().replace(" ", "_").replace("-", "_")
    return stage_data.get(dept_key, stage_data["default"])


def _efficiency_status(efficiency_pct: Optional[float]) -> str:
    if efficiency_pct is None:
        return "N/A"
    if efficiency_pct >= 90:
        return "🟢 On benchmark"
    elif efficiency_pct >= 70:
        return "🟡 Below benchmark"
    else:
        return "🔴 Significantly below"


# ---------------------------------------------------------------------------
# Improvement Plan Generator
# ---------------------------------------------------------------------------

def generate_improvement_plan(
    process_scores: list[dict],
    bottleneck_analysis: dict,
    team_analysis: dict,
    metrics: MetricsData,
) -> list[dict]:
    """
    Generate a prioritized improvement plan combining all analysis outputs.
    Priority = Impact × Urgency / Effort
    """
    items = []

    # Priority 1: Process bottlenecks (Theory of Constraints — fix the constraint first)
    for b in bottleneck_analysis.get("bottlenecks", [])[:3]:
        items.append({
            "priority": 1,
            "category": "Bottleneck",
            "item": f"Resolve bottleneck in '{b['process']}' at step '{b['bottleneck_step']}'",
            "detail": b["toc_recommendation"],
            "impact": "HIGH — constraint limits entire system throughput",
            "effort": "MEDIUM",
            "owner_suggestion": "COO + process owner",
            "timebox": "2-4 weeks",
            "success_metric": f"Throughput at {b['bottleneck_step']} increases by 25%+",
        })

    # Priority 2: Critical process maturity gaps
    critical_processes = [
        p for p in process_scores if p["maturity_score"] < 2.0
    ]
    for proc in sorted(critical_processes, key=lambda x: x["maturity_score"]):
        for rec in proc["recommendations"][:2]:  # Top 2 recs per critical process
            items.append({
                "priority": 2,
                "category": "Process Maturity",
                "item": f"Fix {rec['dimension']} in '{proc['name']}' (score: {rec['current_score']}/5)",
                "detail": rec["action"],
                "impact": "HIGH — ad-hoc processes create inconsistency and risk",
                "effort": "LOW-MEDIUM",
                "owner_suggestion": "Process owner",
                "timebox": "1-2 weeks",
                "success_metric": f"Dimension score improves to 3/5",
            })

    # Priority 3: Team structural issues
    for issue in team_analysis.get("structural_issues", []):
        items.append({
            "priority": 3,
            "category": "Org Structure",
            "item": issue["type"],
            "detail": issue["detail"],
            "impact": "MEDIUM — structural issues compound over time",
            "effort": "HIGH",
            "owner_suggestion": "COO + People",
            "timebox": "1-2 quarters",
            "success_metric": "Management layer count normalized",
        })

    for span_issue in team_analysis.get("span_of_control_issues", []):
        severity = "HIGH" if span_issue["issue"] == "Over-span" else "MEDIUM"
        items.append({
            "priority": 3,
            "category": "Span of Control",
            "item": f"{span_issue['issue']}: {span_issue['manager']} ({span_issue['dept']})",
            "detail": span_issue["recommendation"],
            "impact": severity,
            "effort": "MEDIUM",
            "owner_suggestion": f"VP {span_issue['dept']}",
            "timebox": "1 quarter",
            "success_metric": "Span within 5-8 for ICs, 3-5 for managers",
        })

    # Priority 4: Maturity improvements for non-critical processes
    medium_processes = [
        p for p in process_scores if 2.0 <= p["maturity_score"] < 3.5
    ]
    for proc in sorted(medium_processes, key=lambda x: x["maturity_score"])[:3]:
        if proc["recommendations"]:
            top_rec = proc["recommendations"][0]
            items.append({
                "priority": 4,
                "category": "Process Improvement",
                "item": f"Improve {top_rec['dimension']} in '{proc['name']}'",
                "detail": top_rec["action"],
                "impact": "MEDIUM",
                "effort": "LOW",
                "owner_suggestion": "Process owner",
                "timebox": "2-4 weeks",
                "success_metric": f"Dimension score reaches 3/5",
            })

    # Priority 5: Metrics-driven flags
    burn_multiple = metrics.get("burn_multiple")
    if burn_multiple and burn_multiple > 2.0:
        items.append({
            "priority": 2,
            "category": "Financial Efficiency",
            "item": f"Burn multiple of {burn_multiple:.1f}x is above healthy range",
            "detail": "Burn multiple >1.5x indicates spending exceeds efficient growth. Review headcount-to-revenue ratio by department.",
            "impact": "HIGH",
            "effort": "MEDIUM",
            "owner_suggestion": "COO + CFO",
            "timebox": "30 days to diagnose, 60-90 days to act",
            "success_metric": "Burn multiple <1.5x within 2 quarters",
        })

    nrr = metrics.get("net_revenue_retention_pct")
    if nrr and nrr < 100:
        items.append({
            "priority": 1,
            "category": "Revenue Health",
            "item": f"NRR of {nrr}% — losing more from churn/contraction than gaining from expansion",
            "detail": "NRR <100% means the customer base shrinks without new sales. Investigate churn root causes immediately.",
            "impact": "CRITICAL",
            "effort": "HIGH",
            "owner_suggestion": "COO + VP CS",
            "timebox": "Immediate — 30 days to root cause, 90 days to fix",
            "success_metric": "NRR >100% within 2 quarters",
        })

    # Sort by priority then impact
    priority_order = {"CRITICAL": 0, "HIGH": 1, "MEDIUM": 2, "LOW": 3}
    items.sort(key=lambda x: (x["priority"], priority_order.get(x["impact"].split(" — ")[0], 9)))

    return items


# ---------------------------------------------------------------------------
# Report Formatter
# ---------------------------------------------------------------------------

def format_report(
    process_scores: list[dict],
    bottleneck_analysis: dict,
    team_analysis: dict,
    improvement_plan: list[dict],
    metrics: MetricsData,
) -> str:
    """Format the full analysis report as plain text."""
    lines = []
    now = datetime.now().strftime("%Y-%m-%d %H:%M")

    lines.append("=" * 70)
    lines.append("OPERATIONAL EFFICIENCY ANALYSIS REPORT")
    lines.append(f"Generated: {now}")
    lines.append("=" * 70)

    # --- Executive Summary ---
    lines.append("\n📊 EXECUTIVE SUMMARY")
    lines.append("-" * 40)

    avg_maturity = (
        sum(p["maturity_score"] for p in process_scores) / len(process_scores)
        if process_scores else 0
    )
    critical_count = sum(1 for p in process_scores if p["maturity_score"] < 2.0)
    bottleneck_count = len(bottleneck_analysis.get("bottlenecks", []))
    plan_items = len(improvement_plan)

    lines.append(f"Average Process Maturity:  {avg_maturity:.1f}/5.0  ({MATURITY_LEVELS.get(round(avg_maturity), 'Unknown')})")
    lines.append(f"Critical Process Gaps:     {critical_count}")
    lines.append(f"Active Bottlenecks:        {bottleneck_count}")
    lines.append(f"Improvement Plan Items:    {plan_items}")

    if metrics:
        lines.append("\nKey Business Metrics:")
        if metrics.get("burn_multiple"):
            flag = " ⚠️" if metrics["burn_multiple"] > 2.0 else ""
            lines.append(f"  Burn Multiple:           {metrics['burn_multiple']:.1f}x{flag}")
        if metrics.get("net_revenue_retention_pct"):
            flag = " ⚠️" if metrics["net_revenue_retention_pct"] < 100 else ""
            lines.append(f"  NRR:                     {metrics['net_revenue_retention_pct']}%{flag}")
        if metrics.get("cac_payback_months"):
            flag = " ⚠️" if metrics["cac_payback_months"] > 18 else ""
            lines.append(f"  CAC Payback:             {metrics['cac_payback_months']} months{flag}")

    # --- Process Maturity Scores ---
    lines.append("\n\n📋 PROCESS MATURITY SCORES")
    lines.append("-" * 40)
    lines.append(f"{'Process':<35} {'Score':>6}  {'Level':<12} {'Status'}")
    lines.append(f"{'─'*35} {'─'*6}  {'─'*12} {'─'*20}")

    for p in sorted(process_scores, key=lambda x: x["maturity_score"]):
        score = p["maturity_score"]
        label = p["maturity_label"]
        status = "🔴 Critical" if score < 2 else ("🟡 Needs work" if score < 3.5 else "🟢 Healthy")
        lines.append(f"{p['name']:<35} {score:>6.1f}  {label:<12} {status}")

    # Dimension heatmap
    lines.append("\n\nDimension Breakdown (scores 0-5):")
    lines.append(f"{'Process':<30} {'Doc':>4} {'Own':>4} {'Met':>4} {'Aut':>4} {'Con':>4} {'Fbk':>4}")
    lines.append(f"{'─'*30} {'─'*4} {'─'*4} {'─'*4} {'─'*4} {'─'*4} {'─'*4}")
    for p in sorted(process_scores, key=lambda x: x["maturity_score"]):
        d = p["dimension_scores"]
        lines.append(
            f"{p['name']:<30} {d.get('documentation',0):>4} {d.get('ownership',0):>4} "
            f"{d.get('metrics',0):>4} {d.get('automation',0):>4} "
            f"{d.get('consistency',0):>4} {d.get('feedback_loop',0):>4}"
        )

    # --- Bottleneck Analysis ---
    lines.append("\n\n🔍 BOTTLENECK ANALYSIS (Theory of Constraints)")
    lines.append("-" * 40)

    bottlenecks = bottleneck_analysis.get("bottlenecks", [])
    if not bottlenecks:
        lines.append("No process steps defined for bottleneck analysis.")
    else:
        for i, b in enumerate(bottlenecks, 1):
            lines.append(f"\n{i}. {b['process']}")
            lines.append(f"   Bottleneck step:    {b['bottleneck_step']}")
            lines.append(f"   Throughput:         {b['bottleneck_throughput']}/day")
            lines.append(f"   Queue depth:        {b['bottleneck_queue']} units")
            lines.append(f"   Flow efficiency:    {b['flow_efficiency_pct']}%")
            lines.append(f"   Recommendation:     {b['toc_recommendation']}")

            lines.append(f"\n   Step-by-step throughput:")
            for step in b["steps"]:
                marker = " ← BOTTLENECK" if step["is_bottleneck"] else ""
                lines.append(
                    f"     {step['name']:<30} {step['throughput_per_day']:>4}/day  "
                    f"Queue: {step['queue_depth']:>4}  Util: {step['utilization_pct']:>5.1f}%{marker}"
                )

    # --- Team Structure ---
    lines.append("\n\n👥 TEAM STRUCTURE ANALYSIS")
    lines.append("-" * 40)
    lines.append(f"Total headcount:    {team_analysis['total_headcount']}")
    lines.append(f"Management layers:  {team_analysis['management_layers']} (expected: {team_analysis['expected_layers']})")

    span_issues = team_analysis.get("span_of_control_issues", [])
    if span_issues:
        lines.append(f"\n⚠️  Span of Control Issues ({len(span_issues)}):")
        for issue in span_issues:
            lines.append(f"   {issue['issue']}: {issue['manager']} ({issue['dept']}) — {issue['reports']} reports")
            lines.append(f"   → {issue['recommendation']}")

    dept_eff = team_analysis.get("department_efficiency", [])
    if dept_eff:
        lines.append(f"\nDepartment Revenue Efficiency:")
        lines.append(f"{'Department':<20} {'HC':>4} {'Rev/Head':>10} {'Benchmark':>10} {'vs Bench':>9} {'Status'}")
        lines.append(f"{'─'*20} {'─'*4} {'─'*10} {'─'*10} {'─'*9} {'─'*20}")
        for d in dept_eff:
            rev = f"${d['revenue_per_employee']:,}" if d['revenue_per_employee'] else "N/A"
            bench = f"${d['benchmark']:,}" if d['benchmark'] else "N/A"
            vs_bench = f"{d['efficiency_vs_benchmark_pct']}%" if d['efficiency_vs_benchmark_pct'] != "N/A" else "N/A"
            lines.append(
                f"{d['department']:<20} {d['headcount']:>4} {rev:>10} {bench:>10} {vs_bench:>9} {d['status']}"
            )

    # --- Improvement Plan ---
    lines.append("\n\n🎯 PRIORITIZED IMPROVEMENT PLAN")
    lines.append("-" * 40)
    lines.append("Items ranked by priority (1=highest). Fix Priority 1 before starting Priority 2.\n")

    current_priority = None
    for i, item in enumerate(improvement_plan, 1):
        if item["priority"] != current_priority:
            current_priority = item["priority"]
            lines.append(f"\nPRIORITY {current_priority}")
            lines.append("─" * 30)

        lines.append(f"\n{i}. [{item['category']}] {item['item']}")
        lines.append(f"   Detail:   {item['detail']}")
        lines.append(f"   Impact:   {item['impact']}")
        lines.append(f"   Effort:   {item['effort']}")
        lines.append(f"   Owner:    {item['owner_suggestion']}")
        lines.append(f"   Timebox:  {item['timebox']}")
        lines.append(f"   Success:  {item['success_metric']}")

    lines.append("\n" + "=" * 70)
    lines.append("END OF REPORT")
    lines.append("=" * 70)

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main Entrypoint
# ---------------------------------------------------------------------------

def run_analysis(data: dict) -> str:
    """Run the full analysis pipeline on input data."""
    processes = data.get("processes", [])
    team = data.get("team", {})
    metrics = data.get("metrics", {})

    # 1. Score process maturity
    process_scores = [score_process_maturity(p) for p in processes]

    # 2. Analyze bottlenecks
    bottleneck_analysis = analyze_bottlenecks(processes)

    # 3. Analyze team structure
    team_analysis = analyze_team_structure(team)

    # 4. Generate improvement plan
    improvement_plan = generate_improvement_plan(
        process_scores, bottleneck_analysis, team_analysis, metrics
    )

    # 5. Format and return report
    return format_report(
        process_scores, bottleneck_analysis, team_analysis, improvement_plan, metrics
    )


def main():
    parser = argparse.ArgumentParser(
        description="Operational Efficiency Analyzer — COO Advisor Tool",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        "--input", "-i",
        help="Path to JSON input file (default: use built-in sample data)",
        default=None,
    )
    parser.add_argument(
        "--output", "-o",
        help="Path to write report (default: stdout)",
        default=None,
    )
    args = parser.parse_args()

    if args.input:
        try:
            with open(args.input, "r") as f:
                data = json.load(f)
        except FileNotFoundError:
            print(f"Error: Input file not found: {args.input}", file=sys.stderr)
            sys.exit(1)
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON in input file: {e}", file=sys.stderr)
            sys.exit(1)
    else:
        print("No input file specified — running with sample data.\n")
        data = SAMPLE_DATA

    report = run_analysis(data)

    if args.output:
        with open(args.output, "w") as f:
            f.write(report)
        print(f"Report written to: {args.output}")
    else:
        print(report)


# ---------------------------------------------------------------------------
# Sample Data
# ---------------------------------------------------------------------------

SAMPLE_DATA = {
    "company": "AcmeSaaS",
    "stage": "series_b",
    "metrics": {
        "annual_revenue_usd": 18000000,
        "burn_multiple": 1.8,
        "net_revenue_retention_pct": 108,
        "cac_payback_months": 14,
        "headcount": 85,
        "monthly_churn_pct": 1.2,
    },
    "processes": [
        {
            "name": "Customer Onboarding",
            "category": "Customer Success",
            "maturity": {
                "documentation": 3,
                "ownership": 4,
                "metrics": 3,
                "automation": 2,
                "consistency": 3,
                "feedback_loop": 2,
            },
            "steps": [
                {
                    "name": "Contract signed → kickoff scheduled",
                    "throughput_per_day": 4,
                    "capacity_per_day": 6,
                    "current_queue": 3,
                    "avg_wait_hours": 4,
                    "avg_process_hours": 1,
                },
                {
                    "name": "Technical setup & integration",
                    "throughput_per_day": 2,
                    "capacity_per_day": 3,
                    "current_queue": 8,
                    "avg_wait_hours": 24,
                    "avg_process_hours": 8,
                },
                {
                    "name": "Training & enablement",
                    "throughput_per_day": 3,
                    "capacity_per_day": 4,
                    "current_queue": 2,
                    "avg_wait_hours": 8,
                    "avg_process_hours": 4,
                },
                {
                    "name": "Go-live confirmation",
                    "throughput_per_day": 4,
                    "capacity_per_day": 6,
                    "current_queue": 1,
                    "avg_wait_hours": 2,
                    "avg_process_hours": 1,
                },
            ],
        },
        {
            "name": "Sales Deal Qualification",
            "category": "Sales",
            "maturity": {
                "documentation": 2,
                "ownership": 3,
                "metrics": 4,
                "automation": 2,
                "consistency": 2,
                "feedback_loop": 3,
            },
            "steps": [
                {
                    "name": "Inbound lead review",
                    "throughput_per_day": 15,
                    "capacity_per_day": 20,
                    "current_queue": 5,
                    "avg_wait_hours": 2,
                    "avg_process_hours": 0.5,
                },
                {
                    "name": "BANT qualification call",
                    "throughput_per_day": 8,
                    "capacity_per_day": 10,
                    "current_queue": 12,
                    "avg_wait_hours": 24,
                    "avg_process_hours": 1,
                },
                {
                    "name": "Demo scheduling & prep",
                    "throughput_per_day": 6,
                    "capacity_per_day": 8,
                    "current_queue": 4,
                    "avg_wait_hours": 8,
                    "avg_process_hours": 0.5,
                },
            ],
        },
        {
            "name": "Engineering Deployment",
            "category": "Engineering",
            "maturity": {
                "documentation": 4,
                "ownership": 5,
                "metrics": 4,
                "automation": 4,
                "consistency": 5,
                "feedback_loop": 4,
            },
            "steps": [
                {
                    "name": "PR submitted",
                    "throughput_per_day": 20,
                    "capacity_per_day": 25,
                    "current_queue": 8,
                    "avg_wait_hours": 3,
                    "avg_process_hours": 2,
                },
                {
                    "name": "Code review",
                    "throughput_per_day": 18,
                    "capacity_per_day": 22,
                    "current_queue": 10,
                    "avg_wait_hours": 4,
                    "avg_process_hours": 1,
                },
                {
                    "name": "CI pipeline",
                    "throughput_per_day": 18,
                    "capacity_per_day": 30,
                    "current_queue": 2,
                    "avg_wait_hours": 0.5,
                    "avg_process_hours": 0.5,
                },
                {
                    "name": "Deploy to production",
                    "throughput_per_day": 16,
                    "capacity_per_day": 20,
                    "current_queue": 1,
                    "avg_wait_hours": 0.5,
                    "avg_process_hours": 0.25,
                },
            ],
        },
        {
            "name": "Incident Response",
            "category": "Engineering / Operations",
            "maturity": {
                "documentation": 2,
                "ownership": 2,
                "metrics": 1,
                "automation": 1,
                "consistency": 2,
                "feedback_loop": 1,
            },
            "steps": [],
        },
        {
            "name": "Employee Onboarding",
            "category": "People",
            "maturity": {
                "documentation": 2,
                "ownership": 2,
                "metrics": 1,
                "automation": 1,
                "consistency": 2,
                "feedback_loop": 2,
            },
            "steps": [],
        },
        {
            "name": "Vendor Procurement",
            "category": "Operations",
            "maturity": {
                "documentation": 1,
                "ownership": 1,
                "metrics": 0,
                "automation": 0,
                "consistency": 1,
                "feedback_loop": 0,
            },
            "steps": [],
        },
    ],
    "team": {
        "total_headcount": 85,
        "annual_revenue_usd": 18000000,
        "stage": "series_b",
        "management_layers": 3,
        "open_requisitions": 18,
        "departments": [
            {
                "name": "Engineering",
                "headcount": 32,
                "managers": [
                    {"name": "VP Engineering", "direct_reports": 4, "manages_managers": True},
                    {"name": "Engineering Manager (Platform)", "direct_reports": 7, "manages_managers": False},
                    {"name": "Engineering Manager (Product)", "direct_reports": 8, "manages_managers": False},
                    {"name": "Engineering Manager (Infra)", "direct_reports": 9, "manages_managers": False},
                ],
            },
            {
                "name": "Sales",
                "headcount": 18,
                "managers": [
                    {"name": "VP Sales", "direct_reports": 3, "manages_managers": True},
                    {"name": "Sales Manager (SMB)", "direct_reports": 6, "manages_managers": False},
                    {"name": "Sales Manager (Enterprise)", "direct_reports": 4, "manages_managers": False},
                ],
            },
            {
                "name": "Customer Success",
                "headcount": 12,
                "managers": [
                    {"name": "VP CS", "direct_reports": 2, "manages_managers": False},
                ],
            },
            {
                "name": "Marketing",
                "headcount": 8,
                "managers": [
                    {"name": "VP Marketing", "direct_reports": 7, "manages_managers": False},
                ],
            },
            {
                "name": "Operations",
                "headcount": 6,
                "managers": [
                    {"name": "COO", "direct_reports": 5, "manages_managers": True},
                ],
            },
            {
                "name": "Product",
                "headcount": 9,
                "managers": [
                    {"name": "VP Product", "direct_reports": 8, "manages_managers": False},
                ],
            },
        ],
    },
}


if __name__ == "__main__":
    main()
