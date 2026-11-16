#!/usr/bin/env python3
"""Copy the review-gate workflow + trusted checker into the current repo."""
from __future__ import annotations

import hashlib
import shutil
import sys
from pathlib import Path


# Vendored byte-identical from agents-environment-config. A differing repo copy is replaced (with
# --force) only when it is a known older aec version; a newer or custom one is KEPT.
VENDORED = "check-forged-gate-names.py"
# sha256 of every aec scripts/check-forged-gate-names.py before dba592db (aec #154). 7dff1b48 is
# aec 46580fa/7561972, the copy review-gate 3.2.0/3.2.1 bundled. Add the old hash on each re-vendor.
KNOWN_OLD = frozenset({
    "7dff1b48f058d0e1d6a0089e0376b768ce44d276a5929a9eb2e1b166d1c32f74",  # aec 46580fa, 7561972
    "f71a599eba2d177c59ac5990a6291475eb48cb2cb6dba730327ba70ed7c5d2db",  # aec b84feda
    "6524947e719fc820bf371527880cab689c65fe71fe84108e1a4e88e3a8c97330",  # aec 9abcdae
    "f4b52a7ed9e44a6921ed17dcc8c99076f0baf4734d7f42879c72cff0abdb4932",  # aec bd3b923
    "38ff18b9ea81d5d952ff7a040207f57308d0610d1882489a8e522e9cd76efcb7",  # aec aa2bbb3
    "9c9bb27b42012952bfb74f82f17e804bf49b6afdc0a21b7d5471513a200438f5",  # aec a9be4dd
    "33315bb0adb6e535ff98ee7105e3fe91fec9797a7d67446c634ab94c814163ce",  # aec 5054ef7
    "06cae65f3e93f2bca211ed248969392d07331a2cd396084d4481ceea56117c65",  # aec dba592db, review-gate 3.2.2/3.2.3
})


def _copy(src: Path, dest: Path, force: bool) -> bool:
    """Return True if written. Skip existing unless force; never replace a newer or custom vendored detector."""
    if dest.is_file() and dest.read_bytes() == src.read_bytes():
        print(f"unchanged: {dest}")
        return False
    if (src.name == VENDORED and dest.is_file()
            and hashlib.sha256(dest.read_bytes()).hexdigest() not in KNOWN_OLD):
        print(f"KEPT {dest}: it differs from this skill's copy (vendored from aec) and is not a known "
              f"older version, so it was not overwritten. If yours is older, copy scripts/{VENDORED} "
              "from the newest agents-environment-config by hand.", file=sys.stderr)
        return False
    if dest.exists() and not force:
        print(f"already exists: {dest} (pass --force to overwrite)")
        return False
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dest)
    print(f"wrote {dest}")
    return True


def main() -> int:
    skill_root = Path(__file__).resolve().parents[1]
    force = "--force" in sys.argv
    workflow_src = skill_root / "templates" / "review-gate.yml"
    # The workflow loads each of these from the default branch.
    scripts = ("check-review-gate.py", "check-forged-gate-names.py", "check-forged-review-gate.py")
    script_srcs = [skill_root / "scripts" / name for name in scripts]
    for src in (workflow_src, *script_srcs):
        if not src.is_file():
            print(f"missing: {src}", file=sys.stderr)
            return 1

    root = Path.cwd()
    _copy(workflow_src, root / ".github" / "workflows" / "review-gate.yml", force)
    # Scripts must live on the default branch; the workflow loads only that ref.
    for src in script_srcs:
        _copy(src, root / "scripts" / src.name, force)
    print("Next: add 'Review Gate' as a required status check on staging/main rulesets.")
    print("Doctor: python3", skill_root / "scripts" / "doctor-review-gate.py")
    return 0


if __name__ == "__main__":
    sys.exit(main())
