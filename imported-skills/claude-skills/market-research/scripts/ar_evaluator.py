#!/usr/bin/env python3
"""ar_evaluator.py - Autoresearch evaluator for the market-research skill (OPT-IN).

Stdlib-only. The ISOLATED bridge to engineering/autoresearch-agent. It does NOT call
autoresearch; it is the ground-truth evaluator an autoresearch loop runs after editing
the target market model. It reads a market-model JSON, runs market_sizer in "both" mode,
and prints ONE metric line:

    tam_divergence: <fraction>   (LOWER is better — top-down and bottoms-up should agree)

Optimize a market model so the two sizing methods triangulate (reconcile assumptions),
while the agent edits the target. The user opts in explicitly:
    /ar:setup --domain custom --name tam-triangulation \\
      --target market.json --eval "python3 ar_evaluator.py --target market.json" \\
      --metric tam_divergence --direction lower

Direct use:
    python3 ar_evaluator.py --sample
    python3 ar_evaluator.py --target market.json --profile enterprise
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import config_loader as cfg  # noqa: E402
import market_sizer as ms  # noqa: E402

METRIC = "tam_divergence"


def main(argv: list[str] | None = None) -> int:
    c = cfg.load_config()
    p = argparse.ArgumentParser(description="Autoresearch evaluator: TAM triangulation divergence.")
    p.add_argument("--target", help="path to market-model JSON (or env AR_TARGET)")
    p.add_argument("--profile", default=None, help="overrides onboarding default_profile")
    p.add_argument("--sample", action="store_true")
    args = p.parse_args(argv)

    profile = args.profile or c.get("default_profile", "b2b-saas")
    if args.sample:
        data = ms.SAMPLE
    else:
        target = args.target or os.environ.get("AR_TARGET")
        if not target:
            print("error: provide --target <market.json> or set AR_TARGET", file=sys.stderr)
            return 2
        try:
            with open(target) as f:
                data = json.load(f)
        except (OSError, json.JSONDecodeError) as e:
            print(f"{METRIC}: N/A")
            print(f"error: {e}", file=sys.stderr)
            return 1

    try:
        result = ms.size_market(data, "both", profile)
    except ValueError as e:
        print(f"{METRIC}: N/A")
        print(f"error: {e}", file=sys.stderr)
        return 1

    div = result.get("tam_divergence")
    if div is None:
        print(f"{METRIC}: N/A")
        print("error: need both top_down and bottoms_up blocks to triangulate", file=sys.stderr)
        return 1
    print(f"{METRIC}: {div}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
