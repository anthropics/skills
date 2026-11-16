#!/usr/bin/env python3
"""Detect a forged required check: a PR-controlled Actions job that borrows a protected check name.

Required checks are matched by NAME (plus the GitHub Actions app id), and a same-repo PR runs the
workflows in its own head. So a PR can add a job named exactly like a required check, with
`run: true`, and Actions publishes a success under that name.

A legitimate result for a protected name is either published through the Checks API (its
details_url is `.../runs/<id>`, no `/actions/`) or comes from one pinned trusted workflow
(path + event). Any other Actions-job check run bearing a protected name is forged.

This is DETECTION, not prevention: the forged success still sits beside our result. The
unforgeable fix is a required workflow or a distinct publisher app (plans/2026-11-16-unforgeable-required-checks.md).
It exists so the guard, and the merge step of whoever merges, fail loudly instead of trusting a name.

KNOWN LIMIT: a PR workflow with `checks: write` can also POST the name straight to the Checks API. That
check run has no job URL, so it looks exactly like our own guard's publication (same app, same name) and
this script cannot tell them apart; reruns and `edited` events legitimately add same-name runs too. Only
provenance (required workflow or a distinct publisher app) closes it. Pinned by
test_api_published_guard_check_is_not_forged_known_limit.

SCOPE: the only invoker in this repo is main-via-staging.yml, which runs for PRs into main. PRs into other
branches are covered only by the merger's merge-time run of this script; review-gate.yml invoking it is plan step S5.

TIMING: the guard workflow runs this once. A PR job that publishes its forged name after that scan is
not seen by it, so whoever merges runs this again immediately before the merge.

Usage (filter=all: the default lists only the latest run per name and can hide an earlier same-name one):
  set -o pipefail; gh api "repos/$REPO/commits/$SHA/check-runs?per_page=100&filter=all" --paginate | \
    REPO=$REPO python3 scripts/check-forged-gate-names.py
`pipefail` is required: a failed or truncated listing must not reach this script as empty input.
Exit 0: none forged. Exit 1: forged names listed on stderr. Exit 2: could not evaluate (fails closed).
"""
import json
import os
import re
import subprocess
import sys

# name -> allowed (workflow path, event) pairs for an Actions-job check run bearing that name.
# An empty set means no Actions job may use the name: only the Checks API publishes it.
PROTECTED = {
    "PRs into main must come from staging": set(),
    "Review Gate": {(".github/workflows/review-gate.yml", "pull_request_target")},
}
_JOB_URL = re.compile(r"/actions/runs/(\d+)/job/")


def job_run_id(check_run):
    """Return the workflow run id when this check run was created by an Actions job, else None."""
    for key in ("details_url", "html_url"):
        match = _JOB_URL.search(check_run.get(key) or "")
        if match:
            return match.group(1)
    return None


def forged(check_runs, run_lookup, protected=None):
    """Names/ids of check runs created by an untrusted Actions job under a protected name.

    run_lookup(run_id) -> (workflow path, event); it may raise, which propagates (fail closed).
    """
    protected = PROTECTED if protected is None else protected
    found = []
    for check_run in check_runs:
        name = check_run.get("name")
        if name not in protected:
            continue
        run_id = job_run_id(check_run)
        if run_id is None:
            continue
        if run_lookup(run_id) not in protected[name]:
            found.append((name, check_run.get("html_url") or run_id))
    return found


def _gh_run_lookup(repo):
    def lookup(run_id):
        out = subprocess.run(
            ["gh", "api", f"repos/{repo}/actions/runs/{run_id}", "--jq", "[.path,.event]|@tsv"],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
        path, event = out.split("\t")
        # Required/reusable workflow runs report `path@ref`; compare the file path only.
        return path.split("@", 1)[0], event

    return lookup


def _load_check_runs(text):
    """`gh api --paginate` concatenates one JSON object per page."""
    decoder, index, runs = json.JSONDecoder(), 0, []
    while index < len(text):
        while index < len(text) and text[index].isspace():
            index += 1
        if index >= len(text):
            break
        page, index = decoder.raw_decode(text, index)
        runs.extend(page["check_runs"])
    return runs


def main():
    repo = os.environ.get("REPO")
    if not repo:
        print("::error::REPO is required", file=sys.stderr)
        return 2
    try:
        bad = forged(_load_check_runs(sys.stdin.read()), _gh_run_lookup(repo))
    except (ValueError, KeyError, subprocess.CalledProcessError) as exc:
        print(f"::error::could not evaluate check runs, failing closed: {exc}", file=sys.stderr)
        return 2
    for name, where in bad:
        print(f"::error::forged check '{name}' from an untrusted Actions job: {where}", file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
