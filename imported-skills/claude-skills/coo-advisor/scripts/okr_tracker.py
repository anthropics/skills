#!/usr/bin/env python3
"""
okr_tracker.py — OKR Cascade and Alignment Tracker

Tracks OKR progress from company → department → team level.
Calculates scores, flags at-risk key results, and generates alignment reports.

Scoring: Google's 0.0–1.0 scale (target: 0.6–0.7; hitting 1.0 means goal was too easy)

Usage:
    python okr_tracker.py                    # Runs with sample data
    python okr_tracker.py --input okrs.json  # Custom OKR data
    python okr_tracker.py --input okrs.json --output report.txt
    python okr_tracker.py --format json      # Machine-readable output
"""

import json
import sys
import argparse
from datetime import datetime, date
from typing import Any


# ---------------------------------------------------------------------------
# Scoring Engine
# ---------------------------------------------------------------------------

# OKR health thresholds (Google-style 0.0–1.0 scale)
SCORE_THRESHOLDS = {
    "on_track": 0.70,       # Above this: healthy
    "at_risk": 0.40,        # Between at_risk and on_track: needs attention
    # Below at_risk: off track
}

STATUS_LABELS = {
    "on_track": "🟢 On Track",
    "at_risk": "🟡 At Risk",
    "off_track": "🔴 Off Track",
    "complete": "✅ Complete",
    "not_started": "⬜ Not Started",
}

RISK_LABELS = {
    "critical": "🔴 Critical",
    "high": "🟠 High",
    "medium": "🟡 Medium",
    "low": "🟢 Low",
}


def calculate_kr_score(kr: dict) -> float:
    """
    Calculate a Key Result's progress score (0.0–1.0).
    
    Supports multiple KR types:
    - numeric: current_value / target_value
    - percentage: current_pct / target_pct
    - milestone: milestone_score (0.0–1.0 provided directly)
    - boolean: done (1.0) / not done (0.0)
    """
    kr_type = kr.get("type", "numeric")

    if kr_type == "boolean":
        return 1.0 if kr.get("done", False) else 0.0

    elif kr_type == "milestone":
        # Milestone KRs have explicit score (0.0–1.0) or count of milestones hit
        milestones_total = kr.get("milestones_total", 1)
        milestones_hit = kr.get("milestones_hit", 0)
        explicit_score = kr.get("score")
        if explicit_score is not None:
            return max(0.0, min(1.0, float(explicit_score)))
        return milestones_hit / milestones_total if milestones_total > 0 else 0.0

    elif kr_type == "percentage":
        target = kr.get("target_pct", 100)
        current = kr.get("current_pct", 0)
        baseline = kr.get("baseline_pct", 0)
        if target == baseline:
            return 0.0
        score = (current - baseline) / (target - baseline)
        return max(0.0, min(1.0, score))

    else:  # numeric (default)
        target = kr.get("target_value", 0)
        current = kr.get("current_value", 0)
        baseline = kr.get("baseline_value", 0)
        if target == baseline:
            return 0.0
        # Handle "lower is better" metrics (e.g., churn, response time)
        if kr.get("lower_is_better", False):
            if current <= target:
                return 1.0
            improvement = baseline - current
            needed = baseline - target
            score = improvement / needed if needed != 0 else 0.0
        else:
            score = (current - baseline) / (target - baseline)
        return max(0.0, min(1.0, score))


def get_kr_status(score: float, quarter_progress: float, kr: dict) -> str:
    """
    Determine KR status based on score, time elapsed in quarter, and trend.
    
    A KR is at-risk if its score is significantly behind the time elapsed.
    E.g., if we're 70% through the quarter but KR is at 30%, it's at risk.
    """
    if kr.get("done", False):
        return "complete"

    # Not started
    if score == 0.0 and quarter_progress < 0.1:
        return "not_started"

    # Check against absolute thresholds
    if score >= SCORE_THRESHOLDS["on_track"]:
        return "on_track"

    # Adjust for time: if we're early in quarter, lower scores are acceptable
    adjusted_threshold = SCORE_THRESHOLDS["at_risk"] * (quarter_progress or 0.5)

    if score >= max(adjusted_threshold, SCORE_THRESHOLDS["at_risk"]):
        return "at_risk"

    return "off_track"


def calculate_objective_score(objective: dict, quarter_progress: float) -> dict:
    """
    Score an objective based on its key results.
    Returns scored objective with KR scores and status.
    """
    key_results = objective.get("key_results", [])
    if not key_results:
        return {**objective, "score": 0.0, "status": "not_started", "key_results_scored": []}

    scored_krs = []
    for kr in key_results:
        score = calculate_kr_score(kr)
        status = get_kr_status(score, quarter_progress, kr)

        # Calculate time-adjusted gap
        expected_score = quarter_progress * 0.85  # Expect 85% of time-proportional progress
        gap = expected_score - score

        risk_level = _assess_kr_risk(score, status, gap, quarter_progress, kr)

        scored_krs.append({
            **kr,
            "score": round(score, 3),
            "score_pct": f"{score * 100:.0f}%",
            "status": status,
            "status_label": STATUS_LABELS.get(status, status),
            "expected_score": round(expected_score, 3),
            "gap_vs_expected": round(gap, 3),
            "risk_level": risk_level,
            "risk_label": RISK_LABELS.get(risk_level, risk_level),
        })

    # Objective score = weighted average of KR scores
    # Weight is explicit in KR data or defaults to equal weight
    total_weight = sum(kr.get("weight", 1.0) for kr in key_results)
    weighted_score = sum(
        kr_scored["score"] * kr.get("weight", 1.0)
        for kr_scored, kr in zip(scored_krs, key_results)
    )
    obj_score = weighted_score / total_weight if total_weight > 0 else 0.0

    # Objective status = worst KR status (a chain is only as strong as weakest link)
    status_priority = {"off_track": 0, "at_risk": 1, "not_started": 2, "on_track": 3, "complete": 4}
    obj_status = min(scored_krs, key=lambda x: status_priority.get(x["status"], 2))["status"]

    return {
        **objective,
        "score": round(obj_score, 3),
        "score_pct": f"{obj_score * 100:.0f}%",
        "status": obj_status,
        "status_label": STATUS_LABELS.get(obj_status, obj_status),
        "key_results_scored": scored_krs,
    }


def _assess_kr_risk(
    score: float,
    status: str,
    gap: float,
    quarter_progress: float,
    kr: dict,
) -> str:
    """Assess risk level for a key result."""
    if status == "complete" or status == "on_track":
        return "low"

    weeks_remaining = kr.get("weeks_remaining", max(1, int((1 - quarter_progress) * 13)))

    # Critical: off track with <4 weeks left
    if status == "off_track" and weeks_remaining <= 4:
        return "critical"

    # High: significantly behind with limited time
    if gap > 0.3 and weeks_remaining <= 6:
        return "high"

    # High: off track regardless of time
    if status == "off_track":
        return "high"

    # Medium: at risk
    if status == "at_risk":
        return "medium"

    return "low"


# ---------------------------------------------------------------------------
# OKR Cascade and Alignment Analysis
# ---------------------------------------------------------------------------

def build_okr_tree(data: dict, quarter_progress: float) -> dict:
    """
    Build scored OKR tree: company → departments → teams.
    Returns full hierarchy with scores at every level.
    """
    company = data.get("company_okrs", {})
    departments = data.get("department_okrs", [])
    teams = data.get("team_okrs", [])

    # Score company-level OKRs
    company_scored = {
        "name": company.get("name", "Company"),
        "quarter": company.get("quarter", ""),
        "objectives": [
            calculate_objective_score(obj, quarter_progress)
            for obj in company.get("objectives", [])
        ],
    }

    # Score department-level OKRs
    depts_scored = []
    for dept in departments:
        dept_objectives = [
            calculate_objective_score(obj, quarter_progress)
            for obj in dept.get("objectives", [])
        ]
        dept_score = (
            sum(o["score"] for o in dept_objectives) / len(dept_objectives)
            if dept_objectives else 0.0
        )
        depts_scored.append({
            **dept,
            "objectives": dept_objectives,
            "overall_score": round(dept_score, 3),
            "overall_score_pct": f"{dept_score * 100:.0f}%",
        })

    # Score team-level OKRs
    teams_scored = []
    for team in teams:
        team_objectives = [
            calculate_objective_score(obj, quarter_progress)
            for obj in team.get("objectives", [])
        ]
        team_score = (
            sum(o["score"] for o in team_objectives) / len(team_objectives)
            if team_objectives else 0.0
        )
        teams_scored.append({
            **team,
            "objectives": team_objectives,
            "overall_score": round(team_score, 3),
            "overall_score_pct": f"{team_score * 100:.0f}%",
        })

    return {
        "company": company_scored,
        "departments": depts_scored,
        "teams": teams_scored,
    }


def analyze_alignment(okr_tree: dict) -> dict:
    """
    Analyze how team and department OKRs align to company OKRs.
    Flags: orphaned OKRs (no company parent), missing coverage (company OKR with no team support).
    """
    company_objective_ids = {
        obj.get("id") for obj in okr_tree["company"].get("objectives", [])
        if obj.get("id")
    }

    # Collect all alignment references from dept and team OKRs
    alignment_map: dict[str, list[str]] = {oid: [] for oid in company_objective_ids}
    orphaned = []
    all_supporting = []

    def check_objectives(objectives: list, owner_name: str, level: str):
        for obj in objectives:
            supports = obj.get("supports_company_objective_ids", [])
            if not supports:
                # Check if it's supposed to support something
                if obj.get("supports_company_objective_id"):
                    supports = [obj["supports_company_objective_id"]]

            if not supports:
                orphaned.append({
                    "level": level,
                    "owner": owner_name,
                    "objective": obj.get("title", obj.get("name", "Unknown")),
                    "issue": "No link to company objective — may be misaligned or low priority",
                })
            else:
                for cid in supports:
                    if cid in alignment_map:
                        alignment_map[cid].append(f"{level}:{owner_name}")
                        all_supporting.append(cid)
                    else:
                        orphaned.append({
                            "level": level,
                            "owner": owner_name,
                            "objective": obj.get("title", obj.get("name", "Unknown")),
                            "issue": f"References company objective '{cid}' which doesn't exist",
                        })

    for dept in okr_tree["departments"]:
        check_objectives(dept["objectives"], dept.get("name", "Unknown Dept"), "Department")

    for team in okr_tree["teams"]:
        check_objectives(team["objectives"], team.get("name", "Unknown Team"), "Team")

    # Find company objectives with no support from below
    unsupported = []
    for obj in okr_tree["company"].get("objectives", []):
        obj_id = obj.get("id")
        if obj_id and obj_id not in all_supporting:
            unsupported.append({
                "objective_id": obj_id,
                "objective": obj.get("title", obj.get("name", "Unknown")),
                "issue": "No department or team OKR explicitly supports this company objective",
            })

    coverage_score = (
        len(set(all_supporting)) / len(company_objective_ids) * 100
        if company_objective_ids else 100
    )

    return {
        "alignment_map": alignment_map,
        "orphaned_okrs": orphaned,
        "unsupported_company_objectives": unsupported,
        "coverage_score_pct": round(coverage_score, 1),
    }


def collect_at_risk_krs(okr_tree: dict) -> list[dict]:
    """Collect all at-risk and off-track key results across the full OKR tree."""
    at_risk = []

    def scan_objectives(objectives: list, owner: str, level: str):
        for obj in objectives:
            for kr in obj.get("key_results_scored", []):
                if kr["status"] in ("at_risk", "off_track"):
                    at_risk.append({
                        "level": level,
                        "owner": owner,
                        "objective": obj.get("title", obj.get("name", "Unknown")),
                        "key_result": kr.get("title", kr.get("name", "Unknown")),
                        "score": kr["score"],
                        "score_pct": kr["score_pct"],
                        "status": kr["status"],
                        "status_label": kr["status_label"],
                        "risk_level": kr["risk_level"],
                        "risk_label": kr["risk_label"],
                        "gap_vs_expected": kr["gap_vs_expected"],
                        "notes": kr.get("notes", ""),
                    })

    scan_objectives(
        okr_tree["company"].get("objectives", []),
        okr_tree["company"].get("name", "Company"),
        "Company",
    )
    for dept in okr_tree["departments"]:
        scan_objectives(dept["objectives"], dept.get("name", ""), "Department")
    for team in okr_tree["teams"]:
        scan_objectives(team["objectives"], team.get("name", ""), "Team")

    # Sort: off_track before at_risk, then by gap
    status_order = {"off_track": 0, "at_risk": 1}
    at_risk.sort(key=lambda x: (status_order.get(x["status"], 2), -x.get("gap_vs_expected", 0)))

    return at_risk


# ---------------------------------------------------------------------------
# Report Formatter
# ---------------------------------------------------------------------------

def _score_bar(score: float, width: int = 20) -> str:
    """Render a text progress bar for a 0.0–1.0 score."""
    filled = round(score * width)
    bar = "█" * filled + "░" * (width - filled)
    return f"[{bar}] {score * 100:.0f}%"


def format_report(
    okr_tree: dict,
    alignment: dict,
    at_risk_krs: list[dict],
    quarter_progress: float,
    quarter_label: str,
) -> str:
    """Format full OKR tracking report as plain text."""
    lines = []
    now = datetime.now().strftime("%Y-%m-%d %H:%M")
    company_name = okr_tree["company"].get("name", "Company")

    lines.append("=" * 70)
    lines.append(f"OKR TRACKING REPORT — {company_name}")
    lines.append(f"Quarter: {quarter_label}   |   Quarter progress: {quarter_progress * 100:.0f}%")
    lines.append(f"Generated: {now}")
    lines.append("=" * 70)

    # --- Executive Summary ---
    lines.append("\n📊 EXECUTIVE SUMMARY")
    lines.append("-" * 40)

    company_objectives = okr_tree["company"].get("objectives", [])
    if company_objectives:
        company_avg = sum(o["score"] for o in company_objectives) / len(company_objectives)
        on_track = sum(1 for o in company_objectives if o["status"] == "on_track")
        at_risk = sum(1 for o in company_objectives if o["status"] == "at_risk")
        off_track = sum(1 for o in company_objectives if o["status"] == "off_track")

        lines.append(f"Company OKR Score:    {_score_bar(company_avg)}")
        lines.append(f"Objectives:           {len(company_objectives)} total — "
                     f"🟢 {on_track} on track, 🟡 {at_risk} at risk, 🔴 {off_track} off track")
        lines.append(f"At-risk KRs (all):    {len(at_risk_krs)}")
        lines.append(f"Alignment coverage:   {alignment['coverage_score_pct']}% of company objectives have team support")

        # Overall health assessment
        if company_avg >= 0.7:
            health = "🟢 HEALTHY — On track for a strong quarter"
        elif company_avg >= 0.5:
            health = "🟡 CAUTION — Some objectives need attention"
        elif company_avg >= 0.3:
            health = "🔴 AT RISK — Multiple objectives behind; intervention needed"
        else:
            health = "🚨 CRITICAL — Quarter in serious jeopardy; executive review required"
        lines.append(f"\nOverall Health: {health}")

    # --- Company OKRs ---
    lines.append("\n\n🏢 COMPANY OKRs")
    lines.append("-" * 40)

    for obj in company_objectives:
        lines.append(f"\n  Objective: {obj.get('title', obj.get('name', 'Unknown'))}")
        lines.append(f"  Owner: {obj.get('owner', 'Unassigned')}  |  Score: {_score_bar(obj['score'], 15)}  {obj['status_label']}")

        for kr in obj.get("key_results_scored", []):
            risk_marker = f"  {kr['risk_label']}" if kr["risk_level"] in ("critical", "high") else ""
            lines.append(f"\n    KR: {kr.get('title', kr.get('name', 'Unknown'))}")
            lines.append(f"        Score: {_score_bar(kr['score'], 12)}  {kr['status_label']}{risk_marker}")

            # Show actual progress
            if kr.get("type") == "numeric":
                current = kr.get("current_value", "?")
                target = kr.get("target_value", "?")
                baseline = kr.get("baseline_value", 0)
                unit = kr.get("unit", "")
                lines.append(f"        Progress: {current}{unit} / {target}{unit}  (baseline: {baseline}{unit})")
            elif kr.get("type") == "percentage":
                lines.append(f"        Progress: {kr.get('current_pct', '?')}% / {kr.get('target_pct', '?')}%")
            elif kr.get("type") == "milestone":
                hit = kr.get("milestones_hit", "?")
                total = kr.get("milestones_total", "?")
                lines.append(f"        Milestones: {hit} / {total}")

            if kr.get("notes"):
                lines.append(f"        Note: {kr['notes']}")

    # --- Department OKRs ---
    lines.append("\n\n🏬 DEPARTMENT OKRs")
    lines.append("-" * 40)

    for dept in okr_tree["departments"]:
        lines.append(f"\n  📁 {dept.get('name', 'Unknown')}  |  Score: {_score_bar(dept['overall_score'], 15)}")

        for obj in dept.get("objectives", []):
            lines.append(f"\n     Objective: {obj.get('title', obj.get('name', 'Unknown'))}")
            lines.append(f"     Owner: {obj.get('owner', 'Unassigned')}  |  {obj['status_label']}")
            supports = obj.get("supports_company_objective_ids", [])
            if supports:
                lines.append(f"     Supports: Company Objective(s) {', '.join(supports)}")

            for kr in obj.get("key_results_scored", []):
                risk_marker = f"  {kr['risk_label']}" if kr["risk_level"] in ("critical", "high") else ""
                lines.append(f"\n       KR: {kr.get('title', kr.get('name', 'Unknown'))}")
                lines.append(f"           {_score_bar(kr['score'], 10)}  {kr['status_label']}{risk_marker}")

    # --- Team OKRs ---
    if okr_tree["teams"]:
        lines.append("\n\n👥 TEAM OKRs")
        lines.append("-" * 40)

        for team in okr_tree["teams"]:
            lines.append(f"\n  📋 {team.get('name', 'Unknown')}  |  Score: {_score_bar(team['overall_score'], 15)}")

            for obj in team.get("objectives", []):
                lines.append(f"\n     Objective: {obj.get('title', obj.get('name', 'Unknown'))}")
                supports = obj.get("supports_company_objective_ids", [])
                if supports:
                    lines.append(f"     Supports: {', '.join(supports)}")

                for kr in obj.get("key_results_scored", []):
                    risk_marker = f"  {kr['risk_label']}" if kr["risk_level"] in ("critical", "high") else ""
                    lines.append(
                        f"       • {kr.get('title', kr.get('name', 'Unknown'))}: "
                        f"{kr['score_pct']} {kr['status_label']}{risk_marker}"
                    )

    # --- At-Risk KRs ---
    lines.append("\n\n⚠️  AT-RISK KEY RESULTS (Action Required)")
    lines.append("-" * 40)

    if not at_risk_krs:
        lines.append("✅ No key results currently at risk or off track.")
    else:
        critical = [kr for kr in at_risk_krs if kr["risk_level"] == "critical"]
        high = [kr for kr in at_risk_krs if kr["risk_level"] == "high"]
        medium = [kr for kr in at_risk_krs if kr["risk_level"] == "medium"]

        for group_label, group in [("🔴 CRITICAL", critical), ("🟠 HIGH", high), ("🟡 MEDIUM", medium)]:
            if not group:
                continue
            lines.append(f"\n{group_label} ({len(group)} items):")
            for kr in group:
                lines.append(f"\n  [{kr['level']}] {kr['owner']}")
                lines.append(f"  Obj: {kr['objective']}")
                lines.append(f"  KR:  {kr['key_result']}")
                lines.append(f"  Score: {kr['score_pct']}  {kr['status_label']}  (gap vs expected: {kr['gap_vs_expected'] * 100:.0f}pp)")
                if kr["notes"]:
                    lines.append(f"  Note: {kr['notes']}")

    # --- Alignment Report ---
    lines.append("\n\n🔗 ALIGNMENT REPORT")
    lines.append("-" * 40)
    lines.append(f"Alignment coverage: {alignment['coverage_score_pct']}% of company objectives have explicit support\n")

    # Show alignment map
    lines.append("Company Objective Coverage:")
    for obj in company_objectives:
        obj_id = obj.get("id", "")
        supporters = alignment["alignment_map"].get(obj_id, [])
        obj_name = obj.get("title", obj.get("name", obj_id))
        count = len(supporters)
        marker = "✅" if count > 0 else "⚠️ "
        lines.append(f"  {marker} [{obj_id}] {obj_name}")
        if supporters:
            for s in supporters:
                lines.append(f"       ↑ {s}")
        else:
            lines.append(f"       ↑ (no department or team OKR supports this)")

    if alignment["unsupported_company_objectives"]:
        lines.append(f"\n⚠️  Unsupported Company Objectives ({len(alignment['unsupported_company_objectives'])}):")
        for u in alignment["unsupported_company_objectives"]:
            lines.append(f"  • [{u['objective_id']}] {u['objective']}")
            lines.append(f"    → {u['issue']}")

    if alignment["orphaned_okrs"]:
        lines.append(f"\n⚠️  Orphaned OKRs (not linked to company objectives):")
        for o in alignment["orphaned_okrs"]:
            lines.append(f"  • [{o['level']}] {o['owner']}: {o['objective']}")
            lines.append(f"    → {o['issue']}")

    # --- Recommendations ---
    lines.append("\n\n📋 RECOMMENDED ACTIONS")
    lines.append("-" * 40)

    recs = _generate_recommendations(okr_tree, at_risk_krs, alignment, quarter_progress)
    for i, rec in enumerate(recs, 1):
        lines.append(f"\n{i}. {rec['title']}")
        lines.append(f"   {rec['detail']}")
        lines.append(f"   Owner: {rec['owner']}  |  When: {rec['when']}")

    lines.append("\n" + "=" * 70)
    lines.append("END OF REPORT")
    lines.append("=" * 70)

    return "\n".join(lines)


def _generate_recommendations(
    okr_tree: dict,
    at_risk_krs: list[dict],
    alignment: dict,
    quarter_progress: float,
) -> list[dict]:
    """Generate actionable recommendations based on OKR analysis."""
    recs = []

    # Critical KRs
    critical = [kr for kr in at_risk_krs if kr["risk_level"] == "critical"]
    if critical:
        recs.append({
            "title": f"Emergency review: {len(critical)} critical key result(s) need immediate intervention",
            "detail": f"Critical KRs: {', '.join(kr['key_result'] for kr in critical[:3])}. "
                      f"With limited time remaining, these need escalation today.",
            "owner": "COO + KR owners",
            "when": "This week",
        })

    # Off-track objectives
    off_track_objs = [
        o for o in okr_tree["company"].get("objectives", [])
        if o["status"] == "off_track"
    ]
    if off_track_objs:
        recs.append({
            "title": f"Scope reset for {len(off_track_objs)} off-track company objective(s)",
            "detail": "When a company objective is off track by mid-quarter, "
                      "the options are: (1) resource surge, (2) scope reduction, or (3) accept the miss. "
                      "Choose explicitly — don't let it drift.",
            "owner": "CEO + COO",
            "when": "Within 1 week",
        })

    # Alignment gaps
    if alignment["coverage_score_pct"] < 80:
        recs.append({
            "title": "OKR alignment gap — not all company objectives have team support",
            "detail": f"Only {alignment['coverage_score_pct']}% of company objectives have explicit team/dept OKRs supporting them. "
                      "Either add supporting OKRs or acknowledge these objectives are founder-owned.",
            "owner": "COO + VPs",
            "when": "Next OKR planning cycle",
        })

    if alignment["orphaned_okrs"]:
        recs.append({
            "title": f"{len(alignment['orphaned_okrs'])} orphaned OKR(s) with no company objective linkage",
            "detail": "Team OKRs that don't connect to company objectives waste capacity. "
                      "Either link them explicitly or discontinue them.",
            "owner": "Team leads + COO",
            "when": "OKR review session",
        })

    # Late quarter: force ranking
    if quarter_progress >= 0.67:
        at_risk_count = sum(
            1 for o in okr_tree["company"].get("objectives", [])
            if o["status"] in ("at_risk", "off_track")
        )
        if at_risk_count > 0:
            recs.append({
                "title": f"Late quarter: force-rank which at-risk OKRs to save vs. accept as miss",
                "detail": f"{at_risk_count} objectives at risk with <{int((1 - quarter_progress) * 13)} weeks left. "
                           "You cannot save everything. Pick the 1–2 most important and resource them fully. "
                           "Explicitly accept the others as misses and learn from them.",
                "owner": "CEO + COO",
                "when": "Immediately",
            })

    # Measurement gaps
    unscored_krs = []
    for obj in okr_tree["company"].get("objectives", []):
        for kr in obj.get("key_results_scored", []):
            if kr["score"] == 0.0 and kr["status"] == "not_started" and quarter_progress > 0.25:
                unscored_krs.append(kr.get("title", kr.get("name", "Unknown")))

    if unscored_krs:
        recs.append({
            "title": f"{len(unscored_krs)} key result(s) show no progress past Q1",
            "detail": "KRs with zero progress after 25% of quarter has elapsed are either not started, "
                      "unmeasured, or forgotten. Require owners to update scores this week.",
            "owner": "KR owners",
            "when": "This week — before next leadership sync",
        })

    return recs


def format_json_output(okr_tree: dict, alignment: dict, at_risk_krs: list[dict]) -> str:
    """Format analysis as machine-readable JSON."""
    return json.dumps(
        {
            "generated_at": datetime.now().isoformat(),
            "company_score": (
                sum(o["score"] for o in okr_tree["company"].get("objectives", []))
                / max(1, len(okr_tree["company"].get("objectives", [])))
            ),
            "at_risk_count": len(at_risk_krs),
            "alignment_coverage_pct": alignment["coverage_score_pct"],
            "objectives": okr_tree["company"].get("objectives", []),
            "departments": okr_tree["departments"],
            "teams": okr_tree["teams"],
            "at_risk_key_results": at_risk_krs,
            "alignment": alignment,
        },
        indent=2,
    )


# ---------------------------------------------------------------------------
# Main Entrypoint
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="OKR Cascade and Alignment Tracker — COO Advisor Tool",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("--input", "-i", help="Path to JSON OKR data file", default=None)
    parser.add_argument("--output", "-o", help="Path to write report (default: stdout)", default=None)
    parser.add_argument(
        "--format", "-f",
        choices=["text", "json"],
        default="text",
        help="Output format: text (default) or json",
    )
    parser.add_argument(
        "--quarter-progress",
        type=float,
        default=None,
        help="Override quarter progress (0.0–1.0). Default: auto-calculated from quarter dates.",
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
            print(f"Error: Invalid JSON: {e}", file=sys.stderr)
            sys.exit(1)
    else:
        print("No input file specified — running with sample data.\n")
        data = SAMPLE_DATA

    # Determine quarter progress
    if args.quarter_progress is not None:
        quarter_progress = args.quarter_progress
    else:
        quarter_progress = _calculate_quarter_progress(data)

    quarter_label = data.get("company_okrs", {}).get("quarter", "Unknown Quarter")

    # Run analysis
    okr_tree = build_okr_tree(data, quarter_progress)
    alignment = analyze_alignment(okr_tree)
    at_risk_krs = collect_at_risk_krs(okr_tree)

    # Format output
    if args.format == "json":
        output = format_json_output(okr_tree, alignment, at_risk_krs)
    else:
        output = format_report(okr_tree, alignment, at_risk_krs, quarter_progress, quarter_label)

    if args.output:
        with open(args.output, "w") as f:
            f.write(output)
        print(f"Report written to: {args.output}")
    else:
        print(output)


def _calculate_quarter_progress(data: dict) -> float:
    """Auto-calculate quarter progress from start/end dates in data, or default to 0.5."""
    q = data.get("company_okrs", {})
    start_str = q.get("quarter_start")
    end_str = q.get("quarter_end")

    if not start_str or not end_str:
        return 0.5  # Default to mid-quarter if not specified

    try:
        start = date.fromisoformat(start_str)
        end = date.fromisoformat(end_str)
        today = date.today()
        total_days = (end - start).days
        elapsed_days = (today - start).days
        progress = elapsed_days / total_days if total_days > 0 else 0.5
        return max(0.0, min(1.0, progress))
    except (ValueError, TypeError):
        return 0.5


# ---------------------------------------------------------------------------
# Sample Data
# ---------------------------------------------------------------------------

SAMPLE_DATA = {
    "company_okrs": {
        "name": "AcmeSaaS",
        "quarter": "Q1 2025",
        "quarter_start": "2025-01-01",
        "quarter_end": "2025-03-31",
        "objectives": [
            {
                "id": "CO1",
                "title": "Achieve breakout revenue growth",
                "owner": "CEO",
                "key_results": [
                    {
                        "id": "CO1-KR1",
                        "title": "Reach $5M net new ARR",
                        "type": "numeric",
                        "baseline_value": 0,
                        "current_value": 2800000,
                        "target_value": 5000000,
                        "unit": "",
                        "notes": "Strong January, February softer; pipeline looks better for March",
                    },
                    {
                        "id": "CO1-KR2",
                        "title": "Achieve 115% NRR",
                        "type": "percentage",
                        "baseline_pct": 108,
                        "current_pct": 110,
                        "target_pct": 115,
                        "notes": "Expansion motion improved; churn still elevated in SMB segment",
                    },
                    {
                        "id": "CO1-KR3",
                        "title": "Close 3 enterprise deals (>$150K ACV)",
                        "type": "numeric",
                        "baseline_value": 0,
                        "current_value": 1,
                        "target_value": 3,
                        "unit": " deals",
                        "notes": "1 closed, 2 in late-stage negotiation",
                    },
                ],
            },
            {
                "id": "CO2",
                "title": "Build a world-class product that customers love",
                "owner": "CPO",
                "key_results": [
                    {
                        "id": "CO2-KR1",
                        "title": "Increase feature adoption rate to 65% (% of customers using 3+ core features)",
                        "type": "percentage",
                        "baseline_pct": 48,
                        "current_pct": 52,
                        "target_pct": 65,
                        "notes": "Onboarding improvements shipped; adoption curve is moving",
                    },
                    {
                        "id": "CO2-KR2",
                        "title": "Ship the integration platform (milestone)",
                        "type": "milestone",
                        "milestones_total": 4,
                        "milestones_hit": 1,
                        "milestones": [
                            "API design complete",
                            "Internal alpha",
                            "Beta with 5 customers",
                            "GA launch",
                        ],
                        "notes": "API design shipped. Internal alpha delayed 2 weeks.",
                    },
                    {
                        "id": "CO2-KR3",
                        "title": "NPS score reaches 45",
                        "type": "numeric",
                        "baseline_value": 32,
                        "current_value": 38,
                        "target_value": 45,
                        "unit": "",
                    },
                ],
            },
            {
                "id": "CO3",
                "title": "Build an operationally excellent company",
                "owner": "COO",
                "key_results": [
                    {
                        "id": "CO3-KR1",
                        "title": "Reduce burn multiple from 1.8x to 1.3x",
                        "type": "numeric",
                        "baseline_value": 1.8,
                        "current_value": 1.65,
                        "target_value": 1.3,
                        "lower_is_better": True,
                        "unit": "x",
                    },
                    {
                        "id": "CO3-KR2",
                        "title": "Achieve <30-day customer onboarding (avg)",
                        "type": "numeric",
                        "baseline_value": 47,
                        "current_value": 38,
                        "target_value": 30,
                        "lower_is_better": True,
                        "unit": " days",
                        "notes": "Good progress; blocked by technical setup step (avg 12 days)",
                    },
                    {
                        "id": "CO3-KR3",
                        "title": "Voluntary attrition <10%",
                        "type": "numeric",
                        "baseline_value": 15,
                        "current_value": 12,
                        "target_value": 10,
                        "lower_is_better": True,
                        "unit": "%",
                        "notes": "2 unexpected departures in January; retention initiatives launched",
                    },
                ],
            },
        ],
    },
    "department_okrs": [
        {
            "name": "Sales",
            "owner": "VP Sales",
            "objectives": [
                {
                    "title": "Drive net new ARR to hit company growth target",
                    "owner": "VP Sales",
                    "supports_company_objective_ids": ["CO1"],
                    "key_results": [
                        {
                            "title": "Close $4M in new business ARR",
                            "type": "numeric",
                            "baseline_value": 0,
                            "current_value": 2200000,
                            "target_value": 4000000,
                            "unit": "",
                        },
                        {
                            "title": "Maintain pipeline coverage ratio ≥3x",
                            "type": "numeric",
                            "baseline_value": 2.5,
                            "current_value": 3.1,
                            "target_value": 3.0,
                            "unit": "x",
                        },
                        {
                            "title": "Reduce average sales cycle to 42 days",
                            "type": "numeric",
                            "baseline_value": 58,
                            "current_value": 50,
                            "target_value": 42,
                            "lower_is_better": True,
                            "unit": " days",
                        },
                    ],
                }
            ],
        },
        {
            "name": "Engineering",
            "owner": "VP Engineering",
            "objectives": [
                {
                    "title": "Deliver the integration platform on schedule",
                    "owner": "VP Engineering",
                    "supports_company_objective_ids": ["CO2"],
                    "key_results": [
                        {
                            "title": "Integration platform beta live with 5 customers",
                            "type": "milestone",
                            "milestones_total": 3,
                            "milestones_hit": 1,
                            "notes": "Alpha delayed — dependency on API gateway refactor",
                        },
                        {
                            "title": "Deploy frequency ≥10/week",
                            "type": "numeric",
                            "baseline_value": 6,
                            "current_value": 9,
                            "target_value": 10,
                            "unit": "/week",
                        },
                        {
                            "title": "P0/P1 incidents <2 per month",
                            "type": "numeric",
                            "baseline_value": 5,
                            "current_value": 2.5,
                            "target_value": 2,
                            "lower_is_better": True,
                            "unit": "/month",
                        },
                    ],
                }
            ],
        },
        {
            "name": "Customer Success",
            "owner": "VP CS",
            "objectives": [
                {
                    "title": "Drive retention and expansion to fuel NRR growth",
                    "owner": "VP CS",
                    "supports_company_objective_ids": ["CO1", "CO2"],
                    "key_results": [
                        {
                            "title": "Gross retention ≥92%",
                            "type": "percentage",
                            "baseline_pct": 88,
                            "current_pct": 89,
                            "target_pct": 92,
                            "notes": "3 at-risk accounts in red status",
                        },
                        {
                            "title": "Average onboarding time ≤30 days",
                            "type": "numeric",
                            "baseline_value": 47,
                            "current_value": 38,
                            "target_value": 30,
                            "lower_is_better": True,
                            "unit": " days",
                        },
                        {
                            "title": "Expansion ARR from existing customers: $800K",
                            "type": "numeric",
                            "baseline_value": 0,
                            "current_value": 580000,
                            "target_value": 800000,
                            "unit": "",
                        },
                    ],
                }
            ],
        },
    ],
    "team_okrs": [
        {
            "name": "Platform Engineering",
            "department": "Engineering",
            "objectives": [
                {
                    "title": "Build the integration API infrastructure",
                    "supports_company_objective_ids": ["CO2"],
                    "key_results": [
                        {
                            "title": "API gateway v2 deployed to production",
                            "type": "boolean",
                            "done": False,
                            "notes": "Targeting end of week 8",
                        },
                        {
                            "title": "Webhook system handles 10K events/sec",
                            "type": "boolean",
                            "done": False,
                        },
                        {
                            "title": "P99 API latency <200ms",
                            "type": "numeric",
                            "baseline_value": 380,
                            "current_value": 290,
                            "target_value": 200,
                            "lower_is_better": True,
                            "unit": "ms",
                        },
                    ],
                }
            ],
        },
        {
            "name": "Enterprise Sales Team",
            "department": "Sales",
            "objectives": [
                {
                    "title": "Land 3 enterprise accounts",
                    "supports_company_objective_ids": ["CO1"],
                    "key_results": [
                        {
                            "title": "3 enterprise deals closed",
                            "type": "numeric",
                            "baseline_value": 0,
                            "current_value": 1,
                            "target_value": 3,
                            "unit": " deals",
                        },
                        {
                            "title": "5 enterprise POCs initiated",
                            "type": "numeric",
                            "baseline_value": 0,
                            "current_value": 4,
                            "target_value": 5,
                            "unit": " POCs",
                        },
                    ],
                }
            ],
        },
    ],
}


if __name__ == "__main__":
    main()
