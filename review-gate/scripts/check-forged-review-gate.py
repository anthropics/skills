#!/usr/bin/env python3
"""Review Gate's forged-check step: the vendored aec detector, scoped to the `Review Gate` name.

check-forged-gate-names.py is vendored byte-identical from
bernierllc/agents-environment-config@46580faae5150afbe7707987295b5bdaf8a9d884
(scripts/check-forged-gate-names.py; plan plans/2026-11-16-unforgeable-required-checks.md, step S5).
Re-vendor it by copying that file unchanged; never edit it here.

Its PROTECTED map also lists "PRs into main must come from staging" with no trusted Actions pair.
Several downstream repos still publish that name from a plain `pull_request` Actions job, so
checking it here would fail every main promotion in those repos. That name stays the job of the
repo's own main-via-staging guard; this step checks only `Review Gate`, whose one trusted source is
(.github/workflows/review-gate.yml, pull_request_target).

stdin: `set -o pipefail; gh api "repos/$REPO/commits/$SHA/check-runs?per_page=100&filter=all" --paginate`
Exit 0: none forged. 1: forged (listed on stderr). 2: could not evaluate (fails closed).
"""
import importlib.util
import sys
from pathlib import Path


def main():
    try:
        spec = importlib.util.spec_from_file_location(
            "check_forged_gate_names", Path(__file__).with_name("check-forged-gate-names.py")
        )
        detector = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(detector)
        detector.PROTECTED = {"Review Gate": detector.PROTECTED["Review Gate"]}
    except (OSError, ImportError, KeyError, SyntaxError) as exc:
        print(f"::error::could not load the forged-check detector, failing closed: {exc}", file=sys.stderr)
        return 2
    return detector.main()


if __name__ == "__main__":
    sys.exit(main())
