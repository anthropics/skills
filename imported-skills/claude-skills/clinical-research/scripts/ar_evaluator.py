#!/usr/bin/env python3
"""ar_evaluator.py - Autoresearch evaluator for the clinical-research skill (OPT-IN).

Stdlib-only. This is the ISOLATED bridge to engineering/autoresearch-agent. It does
NOT call autoresearch; it is the ground-truth evaluator that an autoresearch loop runs
after editing the target study plan. It reads a study-plan JSON (the file the loop
optimizes), scores it with phase_gate_scorer, and prints ONE metric line to stdout:

    feasibility_composite: <0-100>   (higher is better)

Usage inside autoresearch (the user opts in explicitly):
    /ar:setup --domain custom --name trial-feasibility \\
      --target study.json --eval "python3 ar_evaluator.py --target study.json" \\
      --metric feasibility_composite --direction higher

Direct use:
    python3 ar_evaluator.py --sample
    python3 ar_evaluator.py --target study.json --profile drug
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import config_loader as cfg  # noqa: E402
import phase_gate_scorer as pgs  # noqa: E402

METRIC = "feasibility_composite"


def evaluate_target(study: dict, profile: str, phase: int) -> float:
    result = pgs.evaluate(study, profile, phase)
    return float(result["composite"])


def main(argv: list[str] | None = None) -> int:
    c = cfg.load_config()
    p = argparse.ArgumentParser(description="Autoresearch evaluator: study-plan feasibility composite.")
    p.add_argument("--target", help="path to study-plan JSON (or env AR_TARGET)")
    p.add_argument("--profile", default=None, help="overrides onboarding default_profile")
    p.add_argument("--phase", type=int, default=2, choices=[1, 2, 3, 4])
    p.add_argument("--sample", action="store_true", help="evaluate the embedded sample plan")
    args = p.parse_args(argv)

    profile = args.profile or c.get("default_profile", "drug")
    if args.sample:
        study = pgs.SAMPLE
    else:
        target = args.target or os.environ.get("AR_TARGET")
        if not target:
            print("error: provide --target <study.json> or set AR_TARGET", file=sys.stderr)
            return 2
        try:
            with open(target) as f:
                study = json.load(f)
        except (OSError, json.JSONDecodeError) as e:
            # autoresearch treats a crash as DISCARD; emit N/A and non-zero.
            print(f"{METRIC}: N/A")
            print(f"error: {e}", file=sys.stderr)
            return 1

    phase = study.get("phase", args.phase)
    value = evaluate_target(study, profile, phase)
    # The single machine-readable metric line autoresearch parses:
    print(f"{METRIC}: {value}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
