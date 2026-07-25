#!/usr/bin/env python3
"""Generate a structured chaos engineering experiment plan.

Enforces the required sections (hypothesis, steady-state metric, blast radius,
abort criteria, rollback). Output is markdown by default; JSON available for
piping into experiment_postmortem.py.
"""
import argparse
import json
import sys
from datetime import datetime, timezone

ATTACK_DEFAULTS = {
    "latency": {"magnitude_hint": "+200ms", "tooling_hint": "tc / Chaos Mesh NetworkChaos"},
    "error": {"magnitude_hint": "10% of requests return 5xx", "tooling_hint": "Toxiproxy / Chaos Mesh HTTPChaos"},
    "cpu": {"magnitude_hint": "80% sustained", "tooling_hint": "stress-ng / Chaos Mesh StressChaos"},
    "memory": {"magnitude_hint": "+1GiB pressure", "tooling_hint": "stress-ng / Chaos Mesh StressChaos"},
    "disk": {"magnitude_hint": "fill /var to 95%", "tooling_hint": "stress-ng / Chaos Mesh IOChaos"},
    "network-partition": {"magnitude_hint": "drop 100% to peer X", "tooling_hint": "Chaos Mesh NetworkChaos partition"},
    "dependency-failure": {"magnitude_hint": "100% timeout to dependency", "tooling_hint": "service mesh fault injection"},
    "time-skew": {"magnitude_hint": "+5 minutes", "tooling_hint": "libfaketime / Chaos Mesh TimeChaos"},
    "kill-instance": {"magnitude_hint": "1 of N instances", "tooling_hint": "AWS FIS / Chaos Monkey"},
}


def build_plan(args):
    attack_meta = ATTACK_DEFAULTS.get(args.attack, {})
    magnitude = args.magnitude or attack_meta.get("magnitude_hint", "<set magnitude>")
    tooling = args.tooling or attack_meta.get("tooling_hint", "<set tooling>")
    plan = {
        "experiment_id": f"chaos-{args.target}-{args.attack}-{int(datetime.now(timezone.utc).timestamp())}",
        "created": datetime.now(timezone.utc).isoformat(),
        "target": args.target,
        "hypothesis": args.hypothesis,
        "steady_state": {
            "metric": args.steady_metric or "<must define before experiment>",
            "baseline_window": "5 minutes pre-experiment",
            "tolerance": args.tolerance or "within ±5% of baseline",
        },
        "attack": {
            "type": args.attack,
            "magnitude": magnitude,
            "duration_min": args.duration_min,
            "tooling": tooling,
        },
        "blast_radius": {
            "scope": args.blast_radius or "<must define before experiment>",
            "rollback_immediately_if": args.abort_if or "<must define abort criteria>",
        },
        "abort_criteria": _parse_abort_criteria(args.abort_if),
        "rollback_procedure": args.rollback or "Disable fault injection; verify steady state recovers within 2 minutes.",
        "monitoring_dashboard": args.dashboard or "<paste dashboard URL>",
        "owner": args.owner or "<assign owner>",
        "on_call_acknowledged": False,
        "learning_question": args.learning or "What did we learn that we did not know before?",
    }
    return plan


def _parse_abort_criteria(raw):
    if not raw:
        return []
    parts = [p.strip() for p in raw.split(" OR ")]
    return [{"signal": p, "action": "abort"} for p in parts if p]


def render_markdown(plan):
    lines = []
    lines.append(f"# Chaos Experiment: {plan['experiment_id']}")
    lines.append("")
    lines.append(f"- **Target:** `{plan['target']}`")
    lines.append(f"- **Created:** {plan['created']}")
    lines.append(f"- **Owner:** {plan['owner']}")
    lines.append("")
    lines.append("## Hypothesis")
    lines.append(f"> {plan['hypothesis']}")
    lines.append("")
    lines.append("## Steady-state metric")
    lines.append(f"- **Metric:** {plan['steady_state']['metric']}")
    lines.append(f"- **Baseline window:** {plan['steady_state']['baseline_window']}")
    lines.append(f"- **Tolerance:** {plan['steady_state']['tolerance']}")
    lines.append("")
    lines.append("## Attack")
    a = plan["attack"]
    lines.append(f"- **Type:** {a['type']}")
    lines.append(f"- **Magnitude:** {a['magnitude']}")
    lines.append(f"- **Duration:** {a['duration_min']} minutes")
    lines.append(f"- **Tooling:** {a['tooling']}")
    lines.append("")
    lines.append("## Blast radius")
    lines.append(f"- **Scope:** {plan['blast_radius']['scope']}")
    lines.append("")
    lines.append("## Abort criteria")
    if plan["abort_criteria"]:
        for c in plan["abort_criteria"]:
            lines.append(f"- {c['signal']}")
    else:
        lines.append("- **WARNING: no abort criteria defined — DO NOT RUN**")
    lines.append("")
    lines.append("## Rollback procedure")
    lines.append(plan["rollback_procedure"])
    lines.append("")
    lines.append("## Monitoring")
    lines.append(f"- Dashboard: {plan['monitoring_dashboard']}")
    lines.append("")
    lines.append("## Learning question")
    lines.append(f"> {plan['learning_question']}")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--target", required=True, help="Target system or service")
    ap.add_argument("--hypothesis", required=True, help='Hypothesis: "When X, metric Y stays Z"')
    ap.add_argument("--attack", required=True, choices=list(ATTACK_DEFAULTS.keys()))
    ap.add_argument("--magnitude", help="Attack magnitude (default: per-attack hint)")
    ap.add_argument("--duration-min", type=int, default=15)
    ap.add_argument("--steady-metric", help="Steady-state metric name (e.g., 'p99 latency')")
    ap.add_argument("--tolerance", help="Tolerance vs baseline (e.g., 'within ±5%%')")
    ap.add_argument("--blast-radius", help="Blast radius (e.g., '5%% of US traffic')")
    ap.add_argument("--abort-if", dest="abort_if", help='Abort criteria, OR-separated (e.g., "p99 > 1000ms OR error_rate > +1pp")')
    ap.add_argument("--rollback", help="Rollback procedure")
    ap.add_argument("--tooling", help="Chaos tool to use (default: per-attack hint)")
    ap.add_argument("--dashboard", help="Monitoring dashboard URL")
    ap.add_argument("--owner", help="Experiment owner")
    ap.add_argument("--learning", help="Learning question")
    ap.add_argument("--format", choices=["markdown", "json"], default="markdown")
    args = ap.parse_args()

    plan = build_plan(args)
    if args.format == "json":
        print(json.dumps(plan, indent=2))
    else:
        print(render_markdown(plan))
    return 0 if plan["abort_criteria"] else 1


if __name__ == "__main__":
    sys.exit(main())
