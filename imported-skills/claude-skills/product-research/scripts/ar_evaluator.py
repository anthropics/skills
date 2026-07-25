#!/usr/bin/env python3
"""ar_evaluator.py - Autoresearch evaluator for the product-research skill (OPT-IN).

Stdlib-only. The ISOLATED bridge to engineering/autoresearch-agent. It does NOT call
autoresearch; it is the ground-truth evaluator an autoresearch loop runs after editing
the target coded-observations file. It reads an observations JSON, runs insight_synthesizer
at the configured source threshold, and prints ONE metric line:

    validated_insights: <int>   (higher is better — clusters that clear the source threshold)

This optimizes the CODING/synthesis of a fixed evidence set (merging/splitting tags so
cross-participant patterns surface) — not the evidence itself. The user opts in explicitly:
    /ar:setup --domain custom --name insight-synthesis \\
      --target observations.json --eval "python3 ar_evaluator.py --target observations.json" \\
      --metric validated_insights --direction higher

Direct use:
    python3 ar_evaluator.py --sample
    python3 ar_evaluator.py --target observations.json --min-sources 3
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import config_loader as cfg  # noqa: E402
import insight_synthesizer as isyn  # noqa: E402

METRIC = "validated_insights"


def main(argv: list[str] | None = None) -> int:
    c = cfg.load_config()
    p = argparse.ArgumentParser(description="Autoresearch evaluator: count of validated insights.")
    p.add_argument("--target", help="path to observations JSON (or env AR_TARGET)")
    p.add_argument("--min-sources", type=int, default=None, help="overrides onboarding insight_min_sources")
    p.add_argument("--sample", action="store_true")
    args = p.parse_args(argv)

    min_sources = args.min_sources if args.min_sources is not None else int(c.get("insight_min_sources", 3))

    if args.sample:
        data = isyn.SAMPLE
    else:
        target = args.target or os.environ.get("AR_TARGET")
        if not target:
            print("error: provide --target <observations.json> or set AR_TARGET", file=sys.stderr)
            return 2
        try:
            with open(target) as f:
                data = json.load(f)
        except (OSError, json.JSONDecodeError) as e:
            print(f"{METRIC}: N/A")
            print(f"error: {e}", file=sys.stderr)
            return 1

    result = isyn.synthesize(data, min_sources)
    count = sum(1 for c2 in result["candidates"] if c2["classification"] == "INSIGHT")
    print(f"{METRIC}: {count}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
