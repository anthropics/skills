#!/usr/bin/env python3
"""Review Gate's forged-check step: the vendored aec detector, scoped to the `Review Gate` name.

check-forged-gate-names.py is vendored byte-identical from
bernierllc/agents-environment-config@dba592dbf5a95d89a19d7b4dfaf2ea11fdf44821 (aec #154: exits 2 on
empty, malformed or runless input) (scripts/check-forged-gate-names.py; plan
plans/2026-11-16-unforgeable-required-checks.md, step S5).
Re-vendor it by copying that file unchanged; never edit it here.

WHY THIS WRAPPER EXISTS: the vendored PROTECTED map also protects "PRs into main must come from
staging" with no trusted pair (set()). Several downstream repos still publish that name from a plain
`pull_request` Actions job, so running the detector unscoped would fail every main promotion in those
repos. The map stays unchanged; this wrapper checks only `Review Gate`. The other name stays the job
of each repo's own main-via-staging guard.

THE GATE'S OWN JOB IS THE RESULT (3.2.8): the vendored map trusts (.github/workflows/review-gate.yml,
pull_request_target), and that job publishes `Review Gate`. A pull_request_target job's check run is on
the PR HEAD, in its own workflow run's suite (email_demo #1068: job 133165097976 on head 6402d452, suite
118647401541), not on the base as 3.2.0-3.2.7 assumed. A Checks API POST cannot pick a suite and lands in
the head's oldest one, which the required-status rule does not read (BLOCKED "expected", #104), so the
job is the only placement that holds. Another PR's gate job reaches this head when a PR shares the head
sha (open, merged, or closed: `commits/{sha}/pulls` omits closed-unmerged PRs, so a PR listing cannot
rule them out). So a trusted-pair job is accepted only when its workflow run is THIS PR's: the run's
display_title is the workflow's run-name, `Review Gate - PR #<n>` (RUN_TITLE), fixed from the event when
the run is created and set only by the trusted default-branch workflow (confirmed live, nevar-auth #23).
Any other Actions job named `Review Gate` is forged.

DELETE THIS WRAPPER when Option A or B of the aec plan lands (a required workflow or a distinct
publisher app, making the required checks unforgeable through the Checks API). The detector is then
retired or kept as defence in depth (plan step S4) and review-gate.yml calls it directly or not at all.

A missing or malformed PR_NUMBER, or a failed run lookup, exits 2.

env: REPO (required), PR_NUMBER (needed to accept the gate's own job).
stdin: `set -o pipefail; gh api "repos/$REPO/commits/$SHA/check-runs?per_page=100&filter=all" --paginate`
Exit 0: none forged. 1: forged (listed on stderr). 2: could not evaluate (fails closed).
"""
import importlib.util
import os
import re
import subprocess
import sys
from pathlib import Path


RUN_TITLE = "Review Gate - PR #{pr}"  # = run-name in review-gate.yml; a test parses both and compares


class Ambiguous(Exception):
    """A run's PR could not be established: fail closed with exit 2."""


def _gh(*args):
    try:
        return subprocess.run(["gh", "api", *args], capture_output=True, text=True, check=True).stdout
    except subprocess.CalledProcessError as exc:
        raise Ambiguous(f"gh api {args[0]} failed: {exc.stderr.strip()}") from exc


def foreign_run(repo, pr, run_id):
    """None when workflow run `run_id` is PR #pr's own gate run; else why its job is not this PR's."""
    title = _gh(f"repos/{repo}/actions/runs/{run_id}", "--jq", ".display_title").strip()
    want = RUN_TITLE.format(pr=pr)
    return None if title == want else f"run {run_id} is titled {title!r}, not {want!r}"


def main():
    try:
        spec = importlib.util.spec_from_file_location(
            "check_forged_gate_names", Path(__file__).with_name("check-forged-gate-names.py")
        )
        detector = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(detector)
        trusted = detector.PROTECTED["Review Gate"]  # KeyError if a re-vendor drops the name: fail closed
        scoped = {"Review Gate": set()}  # every job is looked at; trusted pairs are then checked below
    except (OSError, ImportError, KeyError, SyntaxError) as exc:
        print(f"::error::could not load the forged-check detector, failing closed: {exc}", file=sys.stderr)
        return 2
    repo = os.environ.get("REPO")
    if not repo:
        print("::error::REPO is required", file=sys.stderr)
        return 2
    try:
        lookup = detector._gh_run_lookup(repo)
        flagged = []
        for check_run in detector._load_check_runs(sys.stdin.read()):
            seen = []

            def record(run_id):
                seen.append((run_id, lookup(run_id)))
                return seen[-1][1]
            for name, where in detector.forged([check_run], record, scoped):
                flagged.append((name, where, *seen[-1]))
        bad = []
        for name, where, run_id, pair in flagged:
            if pair not in trusted:
                bad.append((name, where, "untrusted workflow"))
                continue
            pr = os.environ.get("PR_NUMBER", "")
            if not re.fullmatch(r"[1-9][0-9]*", pr):
                raise Ambiguous(f"PR_NUMBER is missing or malformed ({pr!r}); it is needed to accept the gate's job")
            why = foreign_run(repo, pr, run_id)
            if why:
                bad.append((name, where, why))
    except (ValueError, KeyError, TypeError, subprocess.CalledProcessError, Ambiguous) as exc:
        print(f"::error::could not evaluate check runs, failing closed: {exc}", file=sys.stderr)
        return 2
    for name, where, why in bad:
        print(f"::error::forged check '{name}' from an untrusted Actions job: {where} ({why})", file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
