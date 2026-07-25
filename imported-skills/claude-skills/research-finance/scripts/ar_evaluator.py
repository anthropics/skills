#!/usr/bin/env python3
"""ar_evaluator.py - Autoresearch evaluator for the research-finance skill (OPT-IN).

Stdlib-only. The ISOLATED bridge to engineering/autoresearch-agent. It does NOT call
autoresearch; it is the ground-truth evaluator an autoresearch loop runs after editing
the target ledger/budget. It reads a ledger JSON, computes runway via burn_runway_tracker,
and prints ONE metric line:

    runway_months: <float>   (higher is better)

Optimize a program plan to maximize runway (e.g., resequencing spend) while the agent
edits the target. The user opts in explicitly:
    /ar:setup --domain custom --name extend-runway \\
      --target ledger.json --eval "python3 ar_evaluator.py --target ledger.json" \\
      --metric runway_months --direction higher

Direct use:
    python3 ar_evaluator.py --sample
    python3 ar_evaluator.py --target ledger.json
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import config_loader as cfg  # noqa: E402
import burn_runway_tracker as brt  # noqa: E402

METRIC = "runway_months"


def main(argv: list[str] | None = None) -> int:
    c = cfg.load_config()
    p = argparse.ArgumentParser(description="Autoresearch evaluator: R&D program runway in months.")
    p.add_argument("--target", help="path to ledger JSON (or env AR_TARGET)")
    p.add_argument("--threshold-months", type=float, default=None)
    p.add_argument("--sample", action="store_true")
    args = p.parse_args(argv)

    threshold = args.threshold_months if args.threshold_months is not None \
        else c.get("runway_threshold_months", 6)

    if args.sample:
        data = brt.SAMPLE
    else:
        target = args.target or os.environ.get("AR_TARGET")
        if not target:
            print("error: provide --target <ledger.json> or set AR_TARGET", file=sys.stderr)
            return 2
        try:
            with open(target) as f:
                data = json.load(f)
        except (OSError, json.JSONDecodeError) as e:
            print(f"{METRIC}: N/A")
            print(f"error: {e}", file=sys.stderr)
            return 1

    try:
        result = brt.analyze(data, threshold)
    except ValueError as e:
        print(f"{METRIC}: N/A")
        print(f"error: {e}", file=sys.stderr)
        return 1

    print(f"{METRIC}: {result['runway_months_approx']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
