#!/usr/bin/env python3
"""Generate a structured chaos experiment postmortem.

Takes an experiment plan (JSON from experiment_designer.py) plus a results
file (free-form text or structured key=value lines), and produces a markdown
postmortem with hypothesis verdict, learning, surprises, and follow-up actions.
Catches common postmortem failure modes: no learning, no follow-up, blame-laden
language.
"""
import argparse
import json
import os
import re
import sys
from datetime import datetime, timezone

BLAME_PHRASES = [
    "fault of",
    "should have known",
    "stupid",
    "incompetent",
    "obvious",
    "lazy",
    "didn't bother",
]

REQUIRED_RESULT_FIELDS = {
    "outcome": "Did the hypothesis hold? (held|refuted|inconclusive)",
    "duration_actual_min": "Actual experiment duration in minutes",
    "aborted": "Was the experiment aborted? (true|false)",
}


def _parse_results(path):
    """Parse a results file. Lines like 'key=value' OR free text. Returns dict."""
    if not os.path.isfile(path):
        return {"_raw_text": ""}
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        text = f.read()
    parsed = {}
    for line in text.splitlines():
        m = re.match(r"^\s*([\w_.\-]+)\s*=\s*(.+?)\s*$", line)
        if m:
            parsed[m.group(1)] = m.group(2)
    parsed["_raw_text"] = text
    return parsed


def _check_blame(text):
    found = []
    low = text.lower()
    for phrase in BLAME_PHRASES:
        if phrase in low:
            found.append(phrase)
    return found


def build_postmortem(plan, results, follow_ups):
    raw_text = results.get("_raw_text", "")
    blame = _check_blame(raw_text)
    pm = {
        "experiment_id": plan.get("experiment_id", "?"),
        "target": plan.get("target", "?"),
        "created": datetime.now(timezone.utc).isoformat(),
        "hypothesis": plan.get("hypothesis", "?"),
        "outcome": results.get("outcome", "<UNRECORDED — must record>"),
        "aborted": results.get("aborted", "<unrecorded>"),
        "duration_actual_min": results.get("duration_actual_min", "<unrecorded>"),
        "duration_planned_min": plan.get("attack", {}).get("duration_min", "?"),
        "what_we_learned": results.get("learned", "<UNRECORDED — must record at least one learning>"),
        "what_surprised_us": results.get("surprised", "<unrecorded>"),
        "what_failed": results.get("failed", "<none recorded>"),
        "what_held": results.get("held", "<none recorded>"),
        "follow_ups": follow_ups,
        "blame_warnings": blame,
        "raw_results_excerpt": raw_text[:500],
    }
    return pm


def render_markdown(pm):
    lines = []
    lines.append(f"# Postmortem: {pm['experiment_id']}")
    lines.append("")
    lines.append(f"- **Target:** `{pm['target']}`")
    lines.append(f"- **Postmortem date:** {pm['created']}")
    lines.append(f"- **Outcome:** {pm['outcome']}")
    lines.append(f"- **Aborted:** {pm['aborted']}")
    lines.append(f"- **Duration:** planned={pm['duration_planned_min']}min, actual={pm['duration_actual_min']}min")
    lines.append("")
    lines.append("## Hypothesis")
    lines.append(f"> {pm['hypothesis']}")
    lines.append("")
    lines.append("## What we learned")
    lines.append(pm["what_we_learned"])
    lines.append("")
    lines.append("## What surprised us")
    lines.append(pm["what_surprised_us"])
    lines.append("")
    lines.append("## What failed")
    lines.append(pm["what_failed"])
    lines.append("")
    lines.append("## What held")
    lines.append(pm["what_held"])
    lines.append("")
    lines.append("## Follow-up actions")
    if pm["follow_ups"]:
        for f in pm["follow_ups"]:
            lines.append(f"- [ ] {f}")
    else:
        lines.append("- _none recorded — every experiment should produce ≥1 follow-up_")
    if pm["blame_warnings"]:
        lines.append("")
        lines.append("## ⚠️ Blame warning")
        lines.append("Blame-laden language detected — postmortems should be blameless.")
        for b in pm["blame_warnings"]:
            lines.append(f"- '{b}'")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--plan", required=True, help="Path to experiment plan JSON (from experiment_designer.py --format json)")
    ap.add_argument("--result-log", required=True, help="Path to result log (free-form text OR key=value lines)")
    ap.add_argument("--follow-up", action="append", default=[], help="A follow-up action; repeat for multiple")
    ap.add_argument("--format", choices=["markdown", "json"], default="markdown")
    args = ap.parse_args()

    if not os.path.isfile(args.plan):
        print(f"ERROR: plan not found: {args.plan}", file=sys.stderr)
        return 2
    with open(args.plan, "r", encoding="utf-8") as f:
        plan = json.load(f)
    results = _parse_results(args.result_log)
    pm = build_postmortem(plan, results, args.follow_up)
    if args.format == "json":
        print(json.dumps(pm, indent=2))
    else:
        print(render_markdown(pm))
    return 0


if __name__ == "__main__":
    sys.exit(main())
