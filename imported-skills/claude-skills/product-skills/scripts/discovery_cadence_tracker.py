#!/usr/bin/env python3
"""discovery_cadence_tracker.py — score a team's continuous-discovery habit.

Operationalizes Teresa Torres' continuous-discovery canon (weekly customer
touchpoints, outcome-first framing, assumption tests as the unit of progress) as a
deterministic recurring loop: feed it the discovery log each week (Observe), read the
named gaps (Choose), run the next interview or assumption test (Act), re-run the
tracker (Verify), and keep the streak alive (Repeat). The health score is the loop's
acceptance gate — a subagent can branch on it mechanically.

Input JSON (see --sample):
  {"outcome": "increase paid conversion from 9% to 12% by Q4",
   "interviews": [{"date": "YYYY-MM-DD", "participant": str,
                   "outcome_linked": bool, "assumptions_tested": [str]}],
   "assumption_tests": [{"date": "YYYY-MM-DD", "assumption": str,
                         "result": "validated|invalidated|inconclusive"}]}

Scoring (0–100): weekly streak 30 · week coverage 30 · outcome linkage 20 ·
assumption-test throughput 20. Verdicts: HEALTHY >= 70 · AT-RISK 40–69 · DORMANT < 40.

Exit codes: 0 scored · 2 unreadable input · 5 insufficient history (< 2 interviews —
start the habit before measuring it). Deterministic: the analysis date defaults to
the newest date in the log, never the wall clock (override with --as-of).
Stdlib only.
"""

import argparse
import json
import sys
from datetime import date, timedelta

SAMPLE_LOG = {
    "outcome": "increase paid conversion from 9% to 12% by Q4",
    "interviews": [
        {"date": "2026-05-05", "participant": "P1", "outcome_linked": True,
         "assumptions_tested": ["users understand the trial limits"]},
        {"date": "2026-05-12", "participant": "P2", "outcome_linked": True,
         "assumptions_tested": []},
        {"date": "2026-05-26", "participant": "P3", "outcome_linked": False,
         "assumptions_tested": ["pricing page is the drop-off point"]},
        {"date": "2026-06-02", "participant": "P4", "outcome_linked": True,
         "assumptions_tested": ["annual plan framing increases upgrades"]},
    ],
    "assumption_tests": [
        {"date": "2026-05-15", "assumption": "users understand the trial limits",
         "result": "invalidated"},
        {"date": "2026-06-05", "assumption": "annual plan framing increases upgrades",
         "result": "inconclusive"},
    ],
}


def parse_date(value):
    try:
        return date.fromisoformat(str(value)[:10])
    except (TypeError, ValueError):
        return None


def week_of(d: date):
    return d.isocalendar()[:2]


def analyze(log: dict, as_of: date) -> dict:
    interviews = [
        {**i, "date": parse_date(i.get("date"))}
        for i in log.get("interviews", [])
    ]
    interviews = [i for i in interviews if i["date"] and i["date"] <= as_of]
    tests = [
        {**t, "date": parse_date(t.get("date"))}
        for t in log.get("assumption_tests", [])
    ]
    tests = [t for t in tests if t["date"] and t["date"] <= as_of]

    interview_weeks = {week_of(i["date"]) for i in interviews}
    first = min(i["date"] for i in interviews)
    total_weeks = max(((as_of - first).days // 7) + 1, 1)

    # Streak: consecutive weeks with >= 1 interview, counting back from as_of's week.
    streak, cursor = 0, as_of
    while week_of(cursor) in interview_weeks:
        streak += 1
        cursor -= timedelta(days=7)

    coverage = len(interview_weeks) / total_weeks
    linked = sum(1 for i in interviews if i.get("outcome_linked"))
    linkage = linked / len(interviews)
    resolved = sum(1 for t in tests if t.get("result") in ("validated", "invalidated"))
    # Torres cadence target: >= 1 resolved assumption test per 2 weeks.
    test_target = max(total_weeks / 2, 1)
    throughput = min(resolved / test_target, 1.0)

    score = round(
        min(streak / 4, 1.0) * 30 + coverage * 30 + linkage * 20 + throughput * 20, 1)
    verdict = "HEALTHY" if score >= 70 else ("AT-RISK" if score >= 40 else "DORMANT")

    gaps = []
    if streak == 0:
        gaps.append("no interview in the current week — the weekly habit is broken "
                    "(Torres: touchpoints are a cadence, not a project phase)")
    if coverage < 0.75:
        missed = total_weeks - len(interview_weeks)
        gaps.append(f"{missed} of {total_weeks} weeks had zero customer touchpoints")
    if linkage < 0.8:
        gaps.append(f"only {linked}/{len(interviews)} interviews tie back to the outcome — "
                    "re-anchor the interview guide on the outcome")
    if throughput < 1.0:
        gaps.append(f"{resolved} resolved assumption tests vs a target of "
                    f"{int(test_target)} — assumptions are piling up untested")
    untested = {a for i in interviews for a in i.get("assumptions_tested", [])}
    tested = {t.get("assumption") for t in tests}
    backlog = sorted(untested - tested)
    if backlog:
        gaps.append(f"assumptions surfaced but never tested: {'; '.join(backlog[:3])}")

    return {
        "outcome": log.get("outcome", ""),
        "as_of": as_of.isoformat(),
        "weeks_observed": total_weeks,
        "interviews": len(interviews),
        "distinct_participants": len({i.get("participant") for i in interviews}),
        "weekly_streak": streak,
        "week_coverage_pct": round(coverage * 100, 1),
        "outcome_linkage_pct": round(linkage * 100, 1),
        "assumption_tests_resolved": resolved,
        "health_score": score,
        "verdict": verdict,
        "gaps": gaps,
        "next_loop_action": (gaps[0] if gaps else
                             "cadence healthy — book next week's touchpoint before this one ends"),
    }


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Score a continuous-discovery log for cadence health (Torres canon).")
    ap.add_argument("--input", help="Path to the discovery log JSON ('-' for stdin).")
    ap.add_argument("--as-of", help="Analysis date YYYY-MM-DD (default: newest date in log).")
    ap.add_argument("--output", choices=["json", "human"], default="json")
    ap.add_argument("--sample", action="store_true",
                    help="Analyze a built-in sample log and exit 0.")
    args = ap.parse_args()

    if args.sample:
        log = SAMPLE_LOG
    elif args.input:
        try:
            log = json.load(sys.stdin if args.input == "-"
                            else open(args.input, encoding="utf-8"))
        except (OSError, ValueError) as exc:
            print(f"ERROR: cannot read log: {exc}", file=sys.stderr)
            return 2
    else:
        ap.error("--input is required (or use --sample)")

    interview_dates = [d for d in
                       (parse_date(i.get("date")) for i in log.get("interviews", [])) if d]
    all_dates = interview_dates + [
        d for d in (parse_date(t.get("date")) for t in log.get("assumption_tests", [])) if d]
    as_of = parse_date(args.as_of) if args.as_of else (max(all_dates) if all_dates else None)
    if as_of is None or sum(1 for d in interview_dates if d <= as_of) < 2:
        print("REFUSED: fewer than 2 dated interviews on or before the analysis date — "
              "there is no cadence to measure yet. Book the first two weekly touchpoints "
              "(or widen --as-of), then re-run.", file=sys.stderr)
        return 5
    report = analyze(log, as_of)

    if args.output == "json":
        print(json.dumps(report, indent=2))
    else:
        print(f"Discovery health: {report['health_score']}/100 ({report['verdict']})")
        print(f"Streak: {report['weekly_streak']} wk · coverage "
              f"{report['week_coverage_pct']}% · linkage {report['outcome_linkage_pct']}% "
              f"· tests resolved {report['assumption_tests_resolved']}")
        for g in report["gaps"]:
            print(f"  gap: {g}")
        print(f"Next: {report['next_loop_action']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
