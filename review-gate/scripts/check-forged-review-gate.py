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

NO TRUSTED ACTIONS PAIR FOR `Review Gate`: the vendored map trusts (.github/workflows/review-gate.yml,
pull_request_target), but a pull_request_target job attaches to the base SHA, and a stacked child PR's
base is the outer PR's head. That child's trusted-pair success would satisfy the outer PR. So the job is
named review-gate-runner and the real result is only the Checks API run; any Actions job named
`Review Gate` is forged here. A job from the formerly trusted pair is almost always a pre-3.2.0
review-gate.yml still naming its job `Review Gate`, so the wrapper adds a reinstall hint for it.

DELETE THIS WRAPPER when Option A or B of the aec plan lands (a required workflow or a distinct
publisher app, making the required checks unforgeable through the Checks API). The detector is then
retired or kept as defence in depth (plan step S4) and review-gate.yml calls it directly or not at all.

BOOTSTRAP (nevar-integrations #11): the PR that installs 3.2.x is itself evaluated by the default
branch's legacy workflow, whose job is still named `Review Gate`. Such a job is accepted, with a
notice, only when ALL hold: it ran from a formerly trusted (path, pull_request_target) pair; that path
is on the default branch; and this PR (PR_NUMBER) modifies, removes or renames that file. A missing or
malformed PR_NUMBER, or a failed PR-files or default-branch lookup, exits 2; any other failed condition
leaves the job forged (exit 1).

env: REPO (required), PR_NUMBER (needed only to accept a legacy job), DEFAULT_BRANCH (else looked up).
stdin: `set -o pipefail; gh api "repos/$REPO/commits/$SHA/check-runs?per_page=100&filter=all" --paginate`
Exit 0: none forged. 1: forged (listed on stderr). 2: could not evaluate (fails closed).
"""
import importlib.util
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HINT = ("::error::a job named `Review Gate` ran from review-gate.yml (pull_request_target): that is a "
        "pre-3.2.0 workflow. Reinstall the 3.2.0+ workflow (`aec run-script skill:review-gate "
        "install-workflow.py --force`) and merge it to the default branch.")


class Ambiguous(Exception):
    """The bootstrap conditions could not be evaluated: fail closed with exit 2."""


def _gh(*args):
    try:
        return subprocess.run(["gh", "api", *args], capture_output=True, text=True, check=True).stdout
    except subprocess.CalledProcessError as exc:
        raise Ambiguous(f"gh api {args[0]} failed: {exc.stderr.strip()}") from exc


def _pr_files(repo, pr):
    """`gh api --paginate` concatenates one JSON array per page."""
    text, decoder, index, files = _gh(f"repos/{repo}/pulls/{pr}/files?per_page=100", "--paginate"), \
        json.JSONDecoder(), 0, []
    try:
        while index < len(text):
            if text[index].isspace():
                index += 1
                continue
            page, index = decoder.raw_decode(text, index)
            if not isinstance(page, list) or not all(isinstance(f, dict) and isinstance(f.get("filename"), str)
                                                     for f in page):
                raise ValueError("not a list of PR files")
            files.extend(page)
    except ValueError as exc:
        raise Ambiguous(f"could not parse PR {pr} files: {exc}") from exc
    return files


def bootstrap_refusal(repo, path):
    """None when the legacy job from `path` is this PR's own bootstrap run; else why it stays forged."""
    pr = os.environ.get("PR_NUMBER", "")
    if not re.fullmatch(r"[1-9][0-9]*", pr):
        raise Ambiguous(f"PR_NUMBER is missing or malformed ({pr!r}); it is needed to accept a legacy job")
    touched = any((f["filename"] == path and f.get("status") != "added") or f.get("previous_filename") == path
                  for f in _pr_files(repo, pr))
    if not touched:
        return f"PR #{pr} does not change {path}"
    branch = os.environ.get("DEFAULT_BRANCH") or _gh(f"repos/{repo}", "--jq", ".default_branch").strip()
    if not branch:
        raise Ambiguous("could not determine the default branch")
    try:
        subprocess.run(["gh", "api", f"repos/{repo}/contents/{path}?ref={branch}"],
                       capture_output=True, text=True, check=True)
    except subprocess.CalledProcessError:
        return f"{path} is not on the default branch {branch}"
    return None


def main():
    try:
        spec = importlib.util.spec_from_file_location(
            "check_forged_gate_names", Path(__file__).with_name("check-forged-gate-names.py")
        )
        detector = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(detector)
        legacy_pairs = detector.PROTECTED["Review Gate"]  # KeyError if a re-vendor drops the name: fail closed
        scoped = {"Review Gate": set()}
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
                seen.append(lookup(run_id))
                return seen[-1]
            for name, where in detector.forged([check_run], record, scoped):
                flagged.append((name, where, seen[-1]))
        bad = []
        for name, where, pair in flagged:
            refusal = bootstrap_refusal(repo, pair[0]) if pair in legacy_pairs else "untrusted workflow"
            if refusal is None:
                print(f"::notice::bootstrap: `{name}` job {where} ran {pair[0]} ({pair[1]}) from the default "
                      "branch, and this PR replaces that file; accepted as the legacy workflow it upgrades.",
                      file=sys.stderr)
            else:
                bad.append((name, where, pair, refusal))
    except (ValueError, KeyError, TypeError, subprocess.CalledProcessError, Ambiguous) as exc:
        print(f"::error::could not evaluate check runs, failing closed: {exc}", file=sys.stderr)
        return 2
    for name, where, _, refusal in bad:
        print(f"::error::forged check '{name}' from an untrusted Actions job: {where} ({refusal})", file=sys.stderr)
    if any(pair in legacy_pairs for _, _, pair, _ in bad):
        print(HINT, file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
