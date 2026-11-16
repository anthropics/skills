#!/usr/bin/env python3
"""Copy the review-gate workflow + trusted checker into the current repo."""
from __future__ import annotations

import shutil
import sys
from pathlib import Path


# Vendored byte-identical from agents-environment-config. A repo may already hold a newer (or
# otherwise different) aec copy, so the installer never replaces a differing one, even with --force.
VENDORED = "check-forged-gate-names.py"


def _copy(src: Path, dest: Path, force: bool) -> bool:
    """Return True if written. Skip existing unless force; never replace a differing vendored detector."""
    if src.name == VENDORED and dest.is_file() and dest.read_bytes() != src.read_bytes():
        print(f"KEPT {dest}: it differs from this skill's copy (vendored from aec), so it was not "
              f"overwritten. If yours is older, copy scripts/{VENDORED} from the newest "
              "agents-environment-config by hand.", file=sys.stderr)
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
