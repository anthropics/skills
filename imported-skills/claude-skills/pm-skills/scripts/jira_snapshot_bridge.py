#!/usr/bin/env python3
"""jira_snapshot_bridge.py — turn a Jira MCP issue export into analyzable inputs.

Closes the domain's biggest wiring gap: `mcp__atlassian__searchJiraIssuesUsingJql`
returns issue JSON, but the domain's deterministic analytics tools
(scrum-master/velocity_analyzer.py, sprint_health_scorer.py) expect their own
sprint-record schema, and nothing computed flow metrics at all. This bridge accepts
a saved Jira search result (raw MCP shape with `issues[].fields`, or a flat list of
simplified issue dicts) and emits:

  --to flow    the four mandatory Kanban flow measures (Kanban Guide, May 2025):
               WIP, throughput, cycle time (p50/p85/p95), work-item age — plus SLE
               conformance and aging-WIP alerts, and an optional Monte Carlo
               "when will N items be done" forecast (Vacanti-style, seeded, refuses
               on < 10 completed items).
  --to sprint  scrum-master sprint-record JSON (pipe into velocity_analyzer.py /
               sprint_health_scorer.py). Refuses with exit 5 on < 3 sprints,
               mirroring velocity_analyzer's own minimum.

Cycle time here is created→resolved (Jira's export rarely carries an in-progress
timestamp); the output labels this approximation explicitly.

Exit codes: 0 ok · 2 unreadable/invalid input · 5 insufficient data for the
requested mode. Stdlib only; deterministic (as-of defaults to the newest timestamp
in the data, never the wall clock; the forecast RNG is seeded).
"""

import argparse
import json
import math
import random
import sys
from datetime import date, timedelta

DONE_STATUSES = {"done", "closed", "resolved", "released"}
NOT_STARTED_STATUSES = {"to do", "todo", "open", "backlog", "new", "created"}
POINT_FIELD_CANDIDATES = ["story_points", "storyPoints", "customfield_10016", "points"]

SAMPLE_SNAPSHOT = {
    "issues": [
        {"key": "PROJ-1", "fields": {"summary": "Login flow", "status": {"name": "Done"},
         "created": "2026-05-04T09:00:00.000+0000",
         "resolutiondate": "2026-05-08T16:00:00.000+0000",
         "customfield_10016": 5, "sprint": {"name": "Sprint 12"},
         "assignee": {"displayName": "A. Rivera"}}},
        {"key": "PROJ-2", "fields": {"summary": "Rate limiting", "status": {"name": "In Progress"},
         "created": "2026-05-18T09:00:00.000+0000", "customfield_10016": 3,
         "sprint": {"name": "Sprint 13"}, "assignee": {"displayName": "B. Okafor"}}},
    ]
}


def parse_date(value):
    if not value:
        return None
    text = str(value)[:10]
    try:
        return date.fromisoformat(text)
    except ValueError:
        return None


def name_of(value):
    if isinstance(value, dict):
        return value.get("name") or value.get("displayName") or ""
    return str(value) if value else ""


def sprint_of(value):
    if isinstance(value, list) and value:
        value = value[-1]
    return name_of(value)


def normalize(raw, points_field):
    if isinstance(raw, dict) and "issues" in raw:
        records = raw["issues"]
    elif isinstance(raw, list):
        records = raw
    else:
        raise ValueError("expected {'issues': [...]} or a JSON list of issues")
    issues = []
    for rec in records:
        if not isinstance(rec, dict):
            continue
        f = rec.get("fields", rec)
        points = None
        for cand in ([points_field] if points_field else []) + POINT_FIELD_CANDIDATES:
            if cand and f.get(cand) is not None:
                points = f.get(cand)
                break
        status = name_of(f.get("status")).lower()
        issues.append({
            "key": rec.get("key") or f.get("key") or "?",
            "summary": f.get("summary", ""),
            "status": status,
            "done": status in DONE_STATUSES,
            "started": status not in NOT_STARTED_STATUSES,
            "created": parse_date(f.get("created")),
            "resolved": parse_date(f.get("resolutiondate") or f.get("resolved")),
            "points": float(points) if points is not None else None,
            "sprint": sprint_of(f.get("sprint") or f.get("customfield_10020")),
            "assignee": name_of(f.get("assignee")),
            "priority": name_of(f.get("priority")).lower(),
        })
    return [i for i in issues if i["created"]]


def percentile(sorted_values, pct):
    if not sorted_values:
        return None
    rank = max(1, math.ceil(pct / 100 * len(sorted_values)))
    return sorted_values[rank - 1]


def flow_report(issues, as_of, sle_days, forecast_items, seed):
    done = [i for i in issues if i["done"] and i["resolved"]]
    wip = [i for i in issues if not i["done"] and i["started"]]
    cycles = sorted(max((i["resolved"] - i["created"]).days, 0) for i in done)
    p50, p85, p95 = (percentile(cycles, p) for p in (50, 85, 95))
    span_days = max((as_of - min(i["created"] for i in issues)).days, 7) if issues else 7
    weeks = max(span_days / 7.0, 1.0)
    # Weekly throughput over the FULL observed span (first resolution → as_of),
    # zero-filled: dead weeks are real observations and must be sampleable, or the
    # Monte Carlo forecast biases optimistic (Vacanti).
    weekly_counts = []
    if done:
        first_resolved = min(i["resolved"] for i in done)
        observed_weeks = max(((as_of - first_resolved).days // 7) + 1, 1)
        weekly_counts = [0] * observed_weeks
        for i in done:
            idx = min((i["resolved"] - first_resolved).days // 7, observed_weeks - 1)
            weekly_counts[idx] += 1
    sle = sle_days if sle_days else p85
    conformance = (
        round(100 * sum(1 for c in cycles if c <= sle) / len(cycles), 1)
        if cycles and sle is not None else None
    )
    aging = sorted(
        ({"key": i["key"], "summary": i["summary"][:60],
          "age_days": (as_of - i["created"]).days} for i in wip),
        key=lambda a: -a["age_days"],
    )
    aging_alerts = [a for a in aging if p85 is not None and a["age_days"] > p85]
    report = {
        "mode": "flow",
        "as_of": as_of.isoformat(),
        "counts": {"total": len(issues), "done": len(done), "wip": len(wip)},
        "cycle_time_days": {"p50": p50, "p85": p85, "p95": p95,
                            "basis": "created→resolved (approximation; Jira exports rarely carry an in-progress timestamp)"},
        "throughput": {"done_per_week": round(len(done) / weeks, 2),
                       "weeks_observed": round(weeks, 1)},
        "sle": {"days": sle, "conformance_pct": conformance},
        "work_item_age": aging[:10],
        "aging_wip_alerts": aging_alerts,
        "warnings": [],
    }
    if len(done) < 10:
        report["warnings"].append(
            f"only {len(done)} completed items — flow percentiles are low-confidence below 10")
    if forecast_items:
        if len(weekly_counts) < 4 or len(done) < 10:
            report["warnings"].append(
                "forecast refused: need >= 10 completed items across >= 4 observed calendar "
                "weeks (Vacanti: throughput sampling needs real history; zero-throughput "
                "weeks count as observations)")
        else:
            rng = random.Random(seed)
            samples = weekly_counts
            trials = []
            for _ in range(10000):
                remaining, wk = forecast_items, 0
                while remaining > 0 and wk < 520:
                    remaining -= rng.choice(samples)
                    wk += 1
                trials.append(wk)
            trials.sort()
            report["forecast"] = {
                "items": forecast_items,
                "method": "Monte Carlo over historical weekly throughput (10k trials, seeded)",
                "weeks": {f"p{p}": percentile(trials, p) for p in (50, 70, 85, 95)},
            }
    return report


def sprint_export(issues):
    by_sprint = {}
    for i in issues:
        if i["sprint"]:
            by_sprint.setdefault(i["sprint"], []).append(i)
    if len(by_sprint) < 3:
        print(f"REFUSED: {len(by_sprint)} sprint(s) in snapshot — velocity analysis needs >= 3 "
              "(same gate as velocity_analyzer.py). Widen the JQL date range.", file=sys.stderr)
        return None
    ordered = sorted(by_sprint.items(),
                     key=lambda kv: min(i["created"] for i in kv[1]))
    sprints = []
    for n, (name, items) in enumerate(ordered, 1):
        planned = sum(i["points"] or 0 for i in items)
        completed = sum(i["points"] or 0 for i in items if i["done"])
        starts = min(i["created"] for i in items)
        ends = max((i["resolved"] or i["created"]) for i in items)
        sprints.append({
            "sprint_number": n, "sprint_name": name,
            "start_date": starts.isoformat(), "end_date": ends.isoformat(),
            "planned_points": round(planned, 1), "completed_points": round(completed, 1),
            "added_points": 0, "removed_points": 0,
            "carry_over_points": round(planned - completed, 1) if planned > completed else 0,
            "team_capacity": 0, "working_days": 10,
            "team_size": len({i["assignee"] for i in items if i["assignee"]}),
            "stories": [{
                "id": i["key"], "title": i["summary"][:80], "points": i["points"] or 0,
                "status": "completed" if i["done"] else ("in_progress" if i["started"] else "not_started"),
                "assigned_to": i["assignee"], "created_date": i["created"].isoformat(),
                **({"completed_date": i["resolved"].isoformat()} if i["resolved"] else {}),
                "blocked_days": 0, "priority": i["priority"] or "medium",
            } for i in items],
            "blockers": [],
        })
    return {
        "team_info": {"name": "bridged-from-jira", "size": 0,
                      "scrum_master": "", "product_owner": ""},
        "sprints": sprints,
        "_note": ("Bridged from a Jira snapshot: added/removed/carry-over/capacity and "
                  "ceremonies are not derivable from issue exports — fill them in or accept "
                  "the conservative defaults before scoring sprint health."),
    }


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Bridge a saved Jira MCP search result into flow metrics or "
                    "scrum-master sprint-record JSON.")
    ap.add_argument("--input", help="Path to the saved Jira search JSON ('-' for stdin).")
    ap.add_argument("--to", choices=["flow", "sprint"], default="flow")
    ap.add_argument("--points-field", help="Custom field id carrying story points "
                    "(e.g. customfield_10016).")
    ap.add_argument("--as-of", help="Analysis date YYYY-MM-DD (default: newest date in data).")
    ap.add_argument("--sle-days", type=int, help="Service Level Expectation in days "
                    "(default: the p85 cycle time).")
    ap.add_argument("--forecast", type=int, metavar="N",
                    help="Monte Carlo forecast: weeks to finish N more items.")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--sample", action="store_true",
                    help="Print a sample input snapshot and exit 0.")
    args = ap.parse_args()

    if args.sample:
        print(json.dumps(SAMPLE_SNAPSHOT, indent=2))
        return 0
    if not args.input:
        ap.error("--input is required (or use --sample to see the expected shape)")
    try:
        raw = json.load(sys.stdin if args.input == "-" else open(args.input, encoding="utf-8"))
        issues = normalize(raw, args.points_field)
    except (OSError, ValueError) as exc:
        print(f"ERROR: cannot read snapshot: {exc}", file=sys.stderr)
        return 2
    if not issues:
        print("ERROR: no issues with a created date found in the snapshot.", file=sys.stderr)
        return 2

    if args.to == "sprint":
        result = sprint_export(issues)
        if result is None:
            return 5
        print(json.dumps(result, indent=2))
        return 0

    as_of = parse_date(args.as_of) if args.as_of else max(
        (i["resolved"] or i["created"]) for i in issues)
    if as_of is None:
        print(f"ERROR: --as-of '{args.as_of}' is not a valid YYYY-MM-DD date.",
              file=sys.stderr)
        return 2
    report = flow_report(issues, as_of, args.sle_days, args.forecast, args.seed)
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
