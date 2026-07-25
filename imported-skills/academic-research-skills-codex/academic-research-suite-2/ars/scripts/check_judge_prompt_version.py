#!/usr/bin/env python3
"""Judge-prompt-version drift guard (#361).

The judge cache key includes a `prompt_version` component so a judge-prompt
revision invalidates stale cache entries automatically (issue #361). That gate
keys on `JUDGE_PROMPT_SHA256` — the prompt's own fingerprint — so invalidation
only works if that hash actually tracks the prompt text. If the hash could drift
from the prompt, an edited prompt would still hash-match an old cache key and a
stale verdict would be served, silently re-opening the exact bug #361 closes.

This lint is the backstop: it recomputes the SHA-256 of the canonical judge-prompt
section (the text between the JUDGE-PROMPT-CANONICAL-START / -END markers in
`academic-pipeline/agents/claim_ref_alignment_audit_agent.md`) and compares it to
`JUDGE_PROMPT_SHA256` in `scripts/_claim_audit_constants.py`. On drift it fails,
instructing the author to re-pin the hash AND bump the `JUDGE_PROMPT_VERSION`
human-readable label (a log/diff aid, not the cache key) in the same change.

It does NOT (and cannot) verify that the version literal itself changed — that is
a human judgment about whether the edit is behavior-affecting. What it guarantees
is that a prompt edit cannot land WITHOUT the author touching the version machinery
at all: the hash line and the version line live two lines apart, so updating the
hash makes the missing version bump glaringly visible in the diff.

Usage:
    python scripts/check_judge_prompt_version.py
    python scripts/check_judge_prompt_version.py --root PATH   (for test fixtures)

Exit codes:
    0 — prompt section hash matches the pinned constant
    1 — hash drift (prompt changed without re-pinning) — bump version + hash
    2 — invocation error (markers missing, file missing, constant unreadable)
"""
from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]

_AGENT_REL = "academic-pipeline/agents/claim_ref_alignment_audit_agent.md"
_CONSTANTS_REL = "scripts/_claim_audit_constants.py"

_SECTION_RE = re.compile(
    r"<!-- JUDGE-PROMPT-CANONICAL-START.*?-->(.*?)<!-- JUDGE-PROMPT-CANONICAL-END",
    re.DOTALL,
)
_PINNED_RE = re.compile(r'^JUDGE_PROMPT_SHA256\s*=\s*"([0-9a-f]{64})"', re.MULTILINE)


def _extract_prompt_section(agent_md: str) -> str | None:
    """Return the stripped canonical prompt text between the markers, or None."""
    m = _SECTION_RE.search(agent_md)
    if m is None:
        return None
    return m.group(1).strip()


def _pinned_hash(constants_src: str) -> str | None:
    m = _PINNED_RE.search(constants_src)
    return m.group(1) if m else None


def check(root: Path) -> int:
    agent_path = root / _AGENT_REL
    constants_path = root / _CONSTANTS_REL

    for p in (agent_path, constants_path):
        if not p.is_file():
            print(f"ERROR: required file missing: {p}", file=sys.stderr)
            return 2

    section = _extract_prompt_section(agent_path.read_text(encoding="utf-8"))
    if section is None:
        print(
            "ERROR: JUDGE-PROMPT-CANONICAL-START/END markers not found in "
            f"{agent_path}. The markers delimit the hashed prompt section; "
            "removing them disables the #361 drift guard.",
            file=sys.stderr,
        )
        return 2

    pinned = _pinned_hash(constants_path.read_text(encoding="utf-8"))
    if pinned is None:
        print(
            f"ERROR: JUDGE_PROMPT_SHA256 = \"<64-hex>\" not found in {constants_path}.",
            file=sys.stderr,
        )
        return 2

    actual = hashlib.sha256(section.encode("utf-8")).hexdigest()
    if actual != pinned:
        print(
            "FAIL (#361): the canonical judge prompt changed but its pinned hash "
            "was not updated.\n"
            f"  expected (pinned JUDGE_PROMPT_SHA256): {pinned}\n"
            f"  actual   (recomputed from prompt):     {actual}\n"
            "Fix: in scripts/_claim_audit_constants.py, set JUDGE_PROMPT_SHA256 to "
            "the actual hash above AND bump JUDGE_PROMPT_VERSION, so stale judge-"
            "cache entries written under the old prompt are not served against the "
            "new prompt logic.",
            file=sys.stderr,
        )
        return 1

    print("OK (#361): judge prompt section hash matches the pinned constant.")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Judge-prompt-version drift guard (#361).")
    parser.add_argument(
        "--root",
        type=Path,
        default=REPO_ROOT,
        help="Repo root to check (for test fixtures). Defaults to the repo root.",
    )
    args = parser.parse_args(argv)
    return check(args.root)


if __name__ == "__main__":
    sys.exit(main())
