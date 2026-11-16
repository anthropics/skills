#!/usr/bin/env python3
"""Warn when a repo is missing review-gate wiring.

Exit 0 always for v1 (warnings only) so AEC/CI can adopt gradually.
Prints WARN / OK lines on stdout.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

REVIEW_GATE_CONTEXT = "Review Gate"
# Branches the install instructions say must carry Review Gate + conversation rules.
MERGE_BRANCHES = ("main", "staging")


MAIN_REVIEW_LABEL = "review:high"  # must stay in check-review-gate.py MAIN_REVIEW_LABELS (pinned by a test)


def gh_json(args: list[str]) -> object | None:
    proc = subprocess.run(["gh", *args], capture_output=True, text=True)
    if proc.returncode != 0:
        return None
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return None


def ruleset_is_enforcing(detail: dict) -> bool:
    """True when the ruleset actively blocks merges (not disabled/evaluate)."""
    return detail.get("enforcement") == "active"


def _github_path_fnmatch(name: str, pat: str) -> bool:
    """Match ``name`` against ``pat`` with GitHub ruleset pathname semantics.

    ``*`` and ``?`` do not cross ``/``. Recursive traversal requires ``**/``
    (GitHub/Ruby ``FNM_PATHNAME``); a bare ``**`` is pathname-local like ``*``.
    See GitHub ruleset fnmatch docs (not Python ``fnmatch``, which treats ``/``
    as an ordinary character).
    """
    i = 0
    out: list[str] = []
    while i < len(pat):
        if pat.startswith("**/", i):
            out.append("(?:.*/)?")
            i += 3
            continue
        if pat.startswith("**", i):
            # Bare ``**`` does not cross ``/`` (``File.fnmatch("refs/**",
            # "refs/heads/main", FNM_PATHNAME)`` is false).
            out.append("[^/]*")
            i += 2
            continue
        ch = pat[i]
        if ch == "*":
            out.append("[^/]*")
            i += 1
            continue
        if ch == "?":
            out.append("[^/]")
            i += 1
            continue
        if ch == "[":
            j = i + 1
            if j < len(pat) and pat[j] in ("!", "^"):
                j += 1
            if j < len(pat) and pat[j] == "]":
                j += 1
            while j < len(pat) and pat[j] != "]":
                j += 1
            if j >= len(pat):
                out.append(re.escape(ch))
                i += 1
            else:
                klass = pat[i : j + 1]
                # fnmatch ``[!abc]`` → regex ``[^abc]`` (GitHub/Ruby FNMATCH).
                if len(klass) > 2 and klass[1] == "!":
                    klass = "[^" + klass[2:]
                out.append(klass)
                i = j + 1
            continue
        out.append(re.escape(ch))
        i += 1
    return re.fullmatch("".join(out), name) is not None


def _fnmatch_ref(
    pat: str, ref: str, branch: str, *, default_branch: str = "main"
) -> bool:
    """True when a GitHub ruleset fnmatch pattern matches ``ref`` / ``branch``."""
    if pat == "~ALL":
        return True
    if pat == "~DEFAULT_BRANCH":
        return branch == default_branch
    if _github_path_fnmatch(ref, pat) or _github_path_fnmatch(branch, pat):
        return True
    return False


def _branch_covered_by_ref_name(
    branch: str,
    include: list[str],
    exclude: list[str],
    *,
    default_branch: str = "main",
) -> bool:
    ref = f"refs/heads/{branch}"
    # Exclusions use the same fnmatch semantics as GitHub rulesets.
    for pat in exclude:
        if _fnmatch_ref(pat, ref, branch, default_branch=default_branch):
            return False
    if not include:
        return False
    return any(
        _fnmatch_ref(pat, ref, branch, default_branch=default_branch) for pat in include
    )


def ruleset_covered_branches(
    detail: dict, *, default_branch: str = "main"
) -> list[str]:
    """Return ``main``/``staging`` branches this ruleset's ref conditions cover."""
    conditions = detail.get("conditions") or {}
    ref_name = conditions.get("ref_name") or {}
    include = [str(x) for x in (ref_name.get("include") or [])]
    exclude = [str(x) for x in (ref_name.get("exclude") or [])]
    if not include:
        return []
    return [
        b
        for b in MERGE_BRANCHES
        if _branch_covered_by_ref_name(
            b, include, exclude, default_branch=default_branch
        )
    ]


def ruleset_targets_merge_branches(
    detail: dict, *, default_branch: str = "main"
) -> bool:
    """True when ruleset ``conditions.ref_name`` covers ``main`` and/or ``staging``."""
    return bool(ruleset_covered_branches(detail, default_branch=default_branch))


def ruleset_requires_review_gate(detail: dict) -> bool:
    """True when a ruleset detail requires the ``Review Gate`` status check."""
    for rule in detail.get("rules") or []:
        if rule.get("type") != "required_status_checks":
            continue
        params = rule.get("parameters") or {}
        for check in params.get("required_status_checks") or []:
            if not isinstance(check, dict):
                continue
            if check.get("context") == REVIEW_GATE_CONTEXT:
                return True
    return False


def ruleset_requires_conversation_resolution(detail: dict) -> bool:
    """True when a ruleset requires review-thread resolution on pull requests."""
    for rule in detail.get("rules") or []:
        if rule.get("type") != "pull_request":
            continue
        params = rule.get("parameters") or {}
        if params.get("required_review_thread_resolution") is True:
            return True
    return False


def main() -> int:
    root = Path.cwd()
    wf = root / ".github" / "workflows" / "review-gate.yml"
    if wf.is_file():
        print(f"OK workflow {wf.relative_to(root)}")
    else:
        print(
            "WARN missing .github/workflows/review-gate.yml — copy from "
            "skill review-gate/templates/review-gate.yml"
        )
    for name in ("check-review-gate.py", "check-forged-gate-names.py", "check-forged-review-gate.py"):
        script = root / "scripts" / name
        if script.is_file():
            print(f"OK trusted script {script.relative_to(root)}")
        else:
            print(
                f"WARN missing scripts/{name} — the workflow loads this from the "
                "default branch and fails closed without it; re-run install-workflow.py"
            )

    rulesets = gh_json(["api", "repos/{owner}/{repo}/rulesets", "--jq", "."])
    # gh doesn't expand {owner}/{repo} in all versions; resolve explicitly.
    repo = subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
        capture_output=True,
        text=True,
    )
    if repo.returncode != 0:
        print("WARN could not resolve repo via gh; skip ruleset check")
        return 0
    full = repo.stdout.strip()
    labels = gh_json(["label", "list", "-R", full, "--search", MAIN_REVIEW_LABEL, "--json", "name"])
    if isinstance(labels, list) and any(lb.get("name") == MAIN_REVIEW_LABEL for lb in labels):
        print(f"OK label {MAIN_REVIEW_LABEL!r} exists")
    else:
        print(
            f"WARN label {MAIN_REVIEW_LABEL!r} missing (or unreadable): every PR into main fails the gate; "
            f"gh label create {MAIN_REVIEW_LABEL} -R {full}"
        )
    default_branch_proc = subprocess.run(
        [
            "gh",
            "repo",
            "view",
            full,
            "--json",
            "defaultBranchRef",
            "-q",
            ".defaultBranchRef.name",
        ],
        capture_output=True,
        text=True,
    )
    default_branch = (
        default_branch_proc.stdout.strip()
        if default_branch_proc.returncode == 0 and default_branch_proc.stdout.strip()
        else "main"
    )
    rulesets = gh_json(["api", f"repos/{full}/rulesets"])
    if rulesets is None:
        print("WARN could not list rulesets (need admin:repo_hook or similar)")
        return 0
    if not isinstance(rulesets, list):
        print("WARN unexpected rulesets payload")
        return 0

    branch_state = {
        b: {"resolution": False, "gate": False, "seen": False} for b in MERGE_BRANCHES
    }
    skipped_non_enforcing = 0
    skipped_wrong_branch = 0
    for rs in rulesets:
        rid = rs.get("id")
        name = rs.get("name")
        detail = gh_json(["api", f"repos/{full}/rulesets/{rid}"])
        if not isinstance(detail, dict):
            continue
        if not ruleset_is_enforcing(detail):
            skipped_non_enforcing += 1
            enf = detail.get("enforcement") or "unknown"
            print(
                f"WARN ruleset {name!r} enforcement={enf!r} "
                "(disabled/evaluate does not block merges); ignored"
            )
            continue
        covered = ruleset_covered_branches(detail, default_branch=default_branch)
        if not covered:
            skipped_wrong_branch += 1
            print(
                f"WARN ruleset {name!r} does not target main/staging "
                "(conditions.ref_name); ignored for Review Gate coverage"
            )
            continue
        has_resolution = ruleset_requires_conversation_resolution(detail)
        has_gate = ruleset_requires_review_gate(detail)
        has_status_rule = any(
            rule.get("type") == "required_status_checks"
            for rule in (detail.get("rules") or [])
        )
        for branch in covered:
            branch_state[branch]["seen"] = True
            if has_resolution:
                branch_state[branch]["resolution"] = True
                print(
                    f"OK ruleset {name!r} requires conversation resolution "
                    f"on {branch}"
                )
            if has_gate:
                branch_state[branch]["gate"] = True
                print(
                    f"OK ruleset {name!r} requires status check "
                    f"{REVIEW_GATE_CONTEXT!r} on {branch}"
                )
            elif has_status_rule:
                print(
                    f"WARN ruleset {name!r} has required_status_checks on {branch} "
                    f"but missing context {REVIEW_GATE_CONTEXT!r}"
                )
            if not has_resolution:
                # pull_request rule present without the flag
                if any(
                    rule.get("type") == "pull_request"
                    for rule in (detail.get("rules") or [])
                ):
                    print(
                        f"WARN ruleset {name!r} has pull_request rule on {branch} but "
                        f"required_review_thread_resolution is not true"
                    )

    if not any(st["seen"] for st in branch_state.values()):
        bits: list[str] = []
        if skipped_non_enforcing:
            bits.append(f"{skipped_non_enforcing} disabled/evaluate")
        if skipped_wrong_branch:
            bits.append(f"{skipped_wrong_branch} not targeting main/staging")
        suffix = f" (saw {', '.join(bits)})" if bits else ""
        print(f"WARN no actively enforcing main/staging rulesets found{suffix}")

    for branch in MERGE_BRANCHES:
        st = branch_state[branch]
        if not st["seen"]:
            print(
                f"WARN branch {branch!r} has no enforcing ruleset with Review Gate "
                "wiring"
            )
            continue
        if not st["resolution"]:
            print(
                f"WARN branch {branch!r} missing required_review_thread_resolution "
                "on an enforcing ruleset"
            )
        if not st["gate"]:
            print(
                f"WARN branch {branch!r} missing required status check "
                f"{REVIEW_GATE_CONTEXT!r}"
            )
    return 0


if __name__ == "__main__":
    sys.exit(main())
