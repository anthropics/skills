#!/usr/bin/env python3
"""Generate a structured SLO definition.

Enforces required fields (service, SLI type + definition, target, window,
owner, error budget policy reference). Refuses to render if required fields
are missing — exit 1 forces the caller to provide them.

Output is markdown by default. JSON output is consumed by slo_review.py.
"""
import argparse
import json
import sys
from datetime import datetime, timezone

SLI_TYPES = {
    "request-success-rate": {
        "numerator": "count(http_requests_total{status=~\"2..|3..\"})",
        "denominator": "count(http_requests_total)",
        "user_question": "Did the request succeed?",
    },
    "request-latency": {
        "numerator": "count(http_request_duration_seconds < 0.5)",
        "denominator": "count(http_request_duration_seconds)",
        "user_question": "Was the response fast enough?",
    },
    "availability-time": {
        "numerator": "(window_seconds - sum(up_down_seconds))",
        "denominator": "window_seconds",
        "user_question": "Was the service up?",
    },
    "data-freshness": {
        "numerator": "count(data_age_seconds < freshness_threshold)",
        "denominator": "count(data_age_seconds)",
        "user_question": "Is the data current?",
    },
    "correctness": {
        "numerator": "count(correct_outputs)",
        "denominator": "count(total_outputs)",
        "user_question": "Was the answer correct?",
    },
}


def build_slo(args):
    sli_meta = SLI_TYPES.get(args.sli_type, {})
    slo = {
        "slo_id": f"slo-{args.service}-{args.sli_type}-{int(datetime.now(timezone.utc).timestamp())}",
        "created": datetime.now(timezone.utc).isoformat(),
        "service": args.service,
        "owner": args.owner or "<must define before SLO is live>",
        "user_journey": args.user_journey or f"<{sli_meta.get('user_question', 'describe the user journey this SLO protects')}>",
        "sli": {
            "type": args.sli_type,
            "numerator": args.sli_numerator or sli_meta.get("numerator", "<must define>"),
            "denominator": args.sli_denominator or sli_meta.get("denominator", "<must define>"),
            "labels": args.sli_labels.split(",") if args.sli_labels else [],
        },
        "target_percent": args.target,
        "window_days": args.window_days,
        "error_budget": {
            "minutes_per_window": _budget_minutes(args.target, args.window_days),
            "policy_doc": args.policy_doc or "<link to error budget policy required before SLO is live>",
        },
        "alerts": {
            "fast_burn_threshold": "see error_budget_calculator.py",
            "slow_burn_threshold": "see error_budget_calculator.py",
        },
        "review_cadence": args.review_cadence,
    }
    return slo


def _budget_minutes(target_pct, window_days):
    bad_fraction = max(0.0, (100 - target_pct) / 100)
    return round(bad_fraction * window_days * 24 * 60, 2)


def _missing_required(slo):
    missing = []
    if not slo["owner"] or slo["owner"].startswith("<"):
        missing.append("owner")
    if not slo["error_budget"]["policy_doc"] or slo["error_budget"]["policy_doc"].startswith("<"):
        missing.append("error_budget.policy_doc")
    if slo["sli"]["numerator"].startswith("<") or slo["sli"]["denominator"].startswith("<"):
        missing.append("sli.numerator/denominator")
    return missing


def render_markdown(slo):
    lines = []
    lines.append(f"# SLO: {slo['slo_id']}")
    lines.append("")
    lines.append(f"- **Service:** `{slo['service']}`")
    lines.append(f"- **Owner:** {slo['owner']}")
    lines.append(f"- **Created:** {slo['created']}")
    lines.append(f"- **User journey:** {slo['user_journey']}")
    lines.append("")
    lines.append("## SLI")
    lines.append(f"- **Type:** {slo['sli']['type']}")
    lines.append(f"- **Numerator:** `{slo['sli']['numerator']}`")
    lines.append(f"- **Denominator:** `{slo['sli']['denominator']}`")
    if slo["sli"]["labels"]:
        lines.append(f"- **Labels:** {', '.join(slo['sli']['labels'])}")
    lines.append("")
    lines.append("## Target")
    lines.append(f"- **Target:** {slo['target_percent']}% over {slo['window_days']} days")
    lines.append(f"- **Error budget:** {slo['error_budget']['minutes_per_window']} minutes per window")
    lines.append(f"- **Policy:** {slo['error_budget']['policy_doc']}")
    lines.append("")
    lines.append("## Alerts")
    lines.append("Run `error_budget_calculator.py --target {} --window-days {}` for burn-rate thresholds.".format(
        slo["target_percent"], slo["window_days"]
    ))
    lines.append("")
    lines.append(f"## Review cadence: {slo['review_cadence']}")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--service", required=True, help="Service name (e.g., checkout-svc)")
    ap.add_argument("--sli-type", required=True, choices=list(SLI_TYPES.keys()))
    ap.add_argument("--target", type=float, required=True, help="Target percent (e.g., 99.9)")
    ap.add_argument("--window-days", type=int, default=28, help="Compliance window in days (default: 28)")
    ap.add_argument("--user-journey", help="The user journey this SLO protects")
    ap.add_argument("--sli-numerator", help="Override default SLI numerator expression")
    ap.add_argument("--sli-denominator", help="Override default SLI denominator expression")
    ap.add_argument("--sli-labels", help="Comma-separated labels (e.g., env=prod,region=us-east-1)")
    ap.add_argument("--owner", help="Owning team / handle")
    ap.add_argument("--policy-doc", help="URL or path to error budget policy")
    ap.add_argument("--review-cadence", default="quarterly", help="How often to review (default: quarterly)")
    ap.add_argument("--format", choices=["markdown", "json"], default="markdown")
    args = ap.parse_args()

    if not 50 <= args.target <= 100:
        print(f"ERROR: --target must be between 50 and 100, got {args.target}", file=sys.stderr)
        return 2
    if args.window_days < 1:
        print(f"ERROR: --window-days must be >= 1", file=sys.stderr)
        return 2

    slo = build_slo(args)
    missing = _missing_required(slo)

    if args.format == "json":
        print(json.dumps(slo, indent=2))
    else:
        print(render_markdown(slo))
        if missing:
            print("")
            print(f"WARNING: missing required fields: {', '.join(missing)}", file=sys.stderr)
            print("SLO is NOT live until these are filled.", file=sys.stderr)

    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
