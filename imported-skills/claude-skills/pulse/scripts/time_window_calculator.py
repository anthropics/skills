#!/usr/bin/env python3
"""time_window_calculator.py — Compute search-window timestamps deterministically.

Stdlib-only. Given a window string like '7d' / '14d' / '30d' / '60d' / '90d',
compute the values pulse needs for its parallel platform queries:

  - hn_created_at_min:    Unix timestamp (int) for HN Algolia's
                          numericFilters=created_at_i>{ts}
  - reddit_t_param:       The 't=' parameter for reddit.com/search.json
                          ('hour' / 'day' / 'week' / 'month' / 'year' / 'all')
  - web_search_after:     ISO date (YYYY-MM-DD) for the after: operator
  - human_label:          "last N days" for use in output

The mapping from window string to Reddit's coarse-grained 't=' parameter
is the closest defensible bucket (Reddit doesn't accept arbitrary day counts):

  7d  → t=week
  14d → t=week  (the next bucket is 'month'; week is closer for 14 days)
  30d → t=month
  60d → t=month  (next bucket is 'year'; month is closer for 60 days)
  90d → t=year   (closer to year than month)

NO LLM CALLS. Pure datetime arithmetic.

Usage:
    python time_window_calculator.py --window 30d
    python time_window_calculator.py --window 7d --output json
    python time_window_calculator.py --window 30d --reference-date 2026-05-15
"""

import argparse
import json
import re
import sys
from datetime import datetime, timezone, timedelta
from typing import Any, Dict, List


WINDOW_RE = re.compile(r"^(\d+)\s*d(?:ays?)?$", re.IGNORECASE)


def parse_window(window: str) -> int:
    """Return days as int, or raise ValueError."""
    m = WINDOW_RE.match(window.strip())
    if not m:
        raise ValueError(
            f"Invalid window '{window}'. Expected format like '7d', '14d', '30d', '60d', '90d'."
        )
    days = int(m.group(1))
    if days <= 0:
        raise ValueError(f"Window must be positive, got {days}d.")
    if days > 365:
        # Soft cap — pulse is recency-oriented; >1y windows defeat the purpose
        sys.stderr.write(
            f"warning: window {days}d is unusually large; pulse is recency-oriented. Consider <= 90d.\n"
        )
    return days


def reddit_t_param(days: int) -> str:
    """Map day count to closest Reddit 't=' bucket."""
    if days <= 1:
        return "day"
    if days <= 14:
        return "week"
    if days <= 60:
        return "month"
    if days <= 180:
        return "year"
    return "all"


def calculate(window: str, reference_date: datetime) -> Dict[str, Any]:
    days = parse_window(window)
    cutoff = reference_date - timedelta(days=days)
    return {
        "window": window,
        "days": days,
        "reference_date": reference_date.isoformat(),
        "hn_created_at_min": int(cutoff.timestamp()),
        "reddit_t_param": reddit_t_param(days),
        "web_search_after": cutoff.strftime("%Y-%m-%d"),
        "human_label": f"last {days} days",
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Window:                 {result['window']} ({result['days']} days)")
    out.append(f"Reference date:         {result['reference_date']}")
    out.append(f"HN created_at_i>{result['hn_created_at_min']}")
    out.append(f"Reddit t param:         {result['reddit_t_param']}")
    out.append(f"Web search after:       {result['web_search_after']}")
    out.append(f"Human label:            {result['human_label']}")
    out.append("")
    out.append("Use in queries:")
    out.append(f"  Reddit:  reddit.com/search.json?q=<topic>&sort=top&t={result['reddit_t_param']}")
    out.append(f"  HN:      hn.algolia.com/api/v1/search?query=<topic>&numericFilters=created_at_i>{result['hn_created_at_min']}")
    out.append(f"  Web:     \"<topic>\" after:{result['web_search_after']}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--window", help="Time window (e.g., '30d', '7d', '90d')")
    parser.add_argument(
        "--reference-date",
        help="ISO date to use as 'now' (default: actual current time). Useful for deterministic tests.",
    )
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if not args.window:
        parser.print_help()
        return 0

    if args.reference_date:
        try:
            ref = datetime.fromisoformat(args.reference_date).replace(tzinfo=timezone.utc)
        except ValueError:
            print(f"error: invalid --reference-date '{args.reference_date}', expected YYYY-MM-DD or ISO format", file=sys.stderr)
            return 2
    else:
        ref = datetime.now(timezone.utc)

    try:
        result = calculate(args.window, ref)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
