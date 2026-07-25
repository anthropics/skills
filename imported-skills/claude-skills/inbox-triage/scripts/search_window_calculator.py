#!/usr/bin/env python3
"""search_window_calculator.py — Compute the email-search window from cadence + now.

Stdlib-only. The triage skill's Step 1. Given the user's run cadence (from
email-taxonomy.md S1.Q5) and the current time, compute:

  - window_start: ISO timestamp for "after this point"
  - window_end:   ISO timestamp for "up to this point" (typically now)
  - run_label:    "Morning" / "Afternoon" / "Evening" based on hour-of-day
  - hours_back:   the lookback in hours (for logging)

Cadence-to-default-window mapping:

  once daily       → 26h lookback (slight overlap)
  2x daily         → 9h lookback (standard; ~half-day with overlap)
  3x daily         → 6h lookback (third-day with overlap)
  on-demand        → 24h lookback default; user can override via Q1

Q1 override allows arbitrary `--override-hours N` to widen or narrow.

NO LLM CALLS. Pure datetime arithmetic.

Usage:
    python search_window_calculator.py --cadence 2x-daily --now 2026-05-15T14:00
    python search_window_calculator.py --cadence on-demand --override-hours 24 --now 2026-05-15T09:00
    python search_window_calculator.py --cadence 2x-daily --output json
"""

import argparse
import json
import sys
from datetime import datetime, timedelta, timezone
from typing import Any, Dict, List


CADENCE_DEFAULT_HOURS = {
    "once-daily": 26,
    "2x-daily": 9,
    "3x-daily": 6,
    "on-demand": 24,
}


def cadence_to_hours(cadence: str, override_hours: int = None) -> int:
    """Map cadence string to default lookback hours. Override wins if provided."""
    if override_hours is not None:
        if override_hours <= 0:
            raise ValueError(f"--override-hours must be positive, got {override_hours}")
        if override_hours > 24 * 30:
            sys.stderr.write(f"warning: override-hours {override_hours} is > 30 days; triage is recurring-cadence-oriented.\n")
        return override_hours
    key = cadence.lower().strip()
    if key not in CADENCE_DEFAULT_HOURS:
        raise ValueError(f"Unknown cadence '{cadence}'. Expected one of {list(CADENCE_DEFAULT_HOURS.keys())} or use --override-hours.")
    return CADENCE_DEFAULT_HOURS[key]


def run_label(hour_of_day: int) -> str:
    if hour_of_day < 12:
        return "Morning"
    if hour_of_day < 17:
        return "Afternoon"
    return "Evening"


def compute(cadence: str, now: datetime, override_hours: int = None) -> Dict[str, Any]:
    hours = cadence_to_hours(cadence, override_hours)
    window_start = now - timedelta(hours=hours)
    return {
        "cadence": cadence,
        "override_hours": override_hours,
        "hours_back": hours,
        "now": now.isoformat(),
        "window_start": window_start.isoformat(),
        "window_end": now.isoformat(),
        "run_label": run_label(now.hour),
        "search_filter_after_unix": int(window_start.timestamp()),
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Cadence:           {result['cadence']}")
    if result["override_hours"]:
        out.append(f"Override hours:    {result['override_hours']}  (Q1 override active)")
    out.append(f"Hours lookback:    {result['hours_back']}")
    out.append(f"Now:               {result['now']}")
    out.append(f"Window start:      {result['window_start']}")
    out.append(f"Window end:        {result['window_end']}")
    out.append(f"Run label:         {result['run_label']}")
    out.append("")
    out.append("Use in email search:")
    out.append(f"  Gmail: q=after:{result['window_start'][:10]} (or after:{result['search_filter_after_unix']} for unix-time)")
    out.append(f"  Outlook: $filter=receivedDateTime ge {result['window_start']}")
    out.append(f"  IMAP: SINCE {result['window_start'][:10]}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--cadence", help="One of: once-daily | 2x-daily | 3x-daily | on-demand")
    parser.add_argument("--override-hours", type=int, help="(Q1 override) explicit lookback hours")
    parser.add_argument("--now", help="ISO timestamp for current time (default: actual now)")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if not args.cadence and args.override_hours is None:
        parser.print_help(); return 0

    if args.now:
        try:
            # Accept naive ISO (treat as UTC) or with tz
            now = datetime.fromisoformat(args.now)
            if now.tzinfo is None:
                now = now.replace(tzinfo=timezone.utc)
        except ValueError:
            print(f"error: invalid --now '{args.now}', expected ISO format like 2026-05-15T14:00", file=sys.stderr); return 2
    else:
        now = datetime.now(timezone.utc)

    cadence = args.cadence or "on-demand"

    try:
        result = compute(cadence, now, args.override_hours)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr); return 2

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
