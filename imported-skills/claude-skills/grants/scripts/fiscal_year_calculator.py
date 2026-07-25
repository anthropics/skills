#!/usr/bin/env python3
"""fiscal_year_calculator.py — Current NIH fiscal year + lookback window.

Stdlib-only. NIH FY = year of next Sep 30. October starts a new FY.

NIH RePORTER queries need a `fiscal_years` array. Hardcoding values produces
stale skill behavior over time. This script computes them at runtime.

Default window: current FY + 3 prior (4 years total). User can override.

Usage:
    python fiscal_year_calculator.py
    python fiscal_year_calculator.py --window 4 --output json
    python fiscal_year_calculator.py --reference-date 2026-10-15
    python fiscal_year_calculator.py --reference-date 2026-09-15
"""

import argparse
import json
import sys
from datetime import date, datetime
from typing import Any, Dict, List, Optional


def fiscal_year(reference: date) -> int:
    """Return the fiscal year that the given date falls within.

    NIH FY runs Oct 1 → Sep 30. FY 2026 = Oct 1 2025 → Sep 30 2026.
    """
    if reference.month >= 10:
        return reference.year + 1
    return reference.year


def calculate(reference: date, window_years: int) -> Dict[str, Any]:
    if window_years < 1:
        raise ValueError(f"--window must be >= 1, got {window_years}")
    current_fy = fiscal_year(reference)
    years = list(range(current_fy - window_years + 1, current_fy + 1))
    fy_start_date = date(current_fy - 1, 10, 1)
    fy_end_date = date(current_fy, 9, 30)
    return {
        "reference_date": reference.isoformat(),
        "calendar_year": reference.year,
        "current_fiscal_year": current_fy,
        "current_fy_start": fy_start_date.isoformat(),
        "current_fy_end": fy_end_date.isoformat(),
        "window_years": window_years,
        "window_fiscal_years": years,
        "reporter_payload_snippet": f'"fiscal_years": {json.dumps(years)}',
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Reference date:        {result['reference_date']}")
    out.append(f"Calendar year:         {result['calendar_year']}")
    out.append(f"Current fiscal year:   FY {result['current_fiscal_year']} ({result['current_fy_start']} → {result['current_fy_end']})")
    out.append(f"Window:                {result['window_years']} years")
    out.append(f"FY values for query:   {result['window_fiscal_years']}")
    out.append("")
    out.append("Use in RePORTER POST body:")
    out.append(f"  {result['reporter_payload_snippet']}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--reference-date", help="ISO date (default: today)")
    parser.add_argument("--window", type=int, default=4, help="Years to include (default: 4 = current + 3 prior)")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.reference_date:
        try:
            ref = datetime.strptime(args.reference_date, "%Y-%m-%d").date()
        except ValueError:
            print(f"error: invalid --reference-date '{args.reference_date}', expected YYYY-MM-DD", file=sys.stderr); return 2
    else:
        ref = date.today()

    try:
        result = calculate(ref, args.window)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr); return 2

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
