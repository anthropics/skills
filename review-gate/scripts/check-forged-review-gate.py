#!/usr/bin/env python3
"""Review Gate's forged-check step: the vendored aec detector, scoped to the `Review Gate` name.

check-forged-gate-names.py is vendored byte-identical from
bernierllc/agents-environment-config@46580faae5150afbe7707987295b5bdaf8a9d884
(scripts/check-forged-gate-names.py; plan plans/2026-11-16-unforgeable-required-checks.md, step S5).
Re-vendor it by copying that file unchanged; never edit it here.

WHY THIS WRAPPER EXISTS: the vendored PROTECTED map also protects "PRs into main must come from
staging" with no trusted pair (set()). Several downstream repos still publish that name from a plain
`pull_request` Actions job, so running the detector unscoped would fail every main promotion in those
repos. The map stays unchanged; this wrapper checks only `Review Gate`. The other name stays the job
of each repo's own main-via-staging guard.

NO TRUSTED ACTIONS PAIR FOR `Review Gate`: the vendored map trusts (.github/workflows/review-gate.yml,
pull_request_target), but a pull_request_target job attaches to the base SHA, and a stacked child PR's
base is the outer PR's head. That child's trusted-pair success would satisfy the outer PR. So the job is
named review-gate-runner and the real result is only the Checks API run; any Actions job named
`Review Gate` is forged here.

DELETE THIS WRAPPER when Option A or B of the aec plan lands (a required workflow or a distinct
publisher app, making the required checks unforgeable through the Checks API). The detector is then
retired or kept as defence in depth (plan step S4) and review-gate.yml calls it directly or not at all.

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
        detector.PROTECTED["Review Gate"]  # KeyError if a re-vendor drops the name: fail closed
        detector.PROTECTED = {"Review Gate": set()}
    except (OSError, ImportError, KeyError, SyntaxError) as exc:
        print(f"::error::could not load the forged-check detector, failing closed: {exc}", file=sys.stderr)
        return 2
    return detector.main()


if __name__ == "__main__":
    sys.exit(main())
