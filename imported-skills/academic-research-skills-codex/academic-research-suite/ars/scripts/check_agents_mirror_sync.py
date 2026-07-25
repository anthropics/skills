#!/usr/bin/env python3
"""Lint: plugin-root agents/ mirrors stay byte-identical REAL files (#413).

agents/ held relative symlinks into deep-research/agents/ from v3.7.0 Phase
2.1 until #413: on Windows checkouts without developer mode / `core.symlinks`,
and in zip-download installs, a relative symlink materialises as a one-line
text file containing the link path — silently breaking the three plugin
agents. The symlinks are now real byte-identical copies, and this lint takes
over the guarantee the symlinks used to provide structurally: the v3.7.0
notes chose symlinks-not-copies precisely so the plugin surface could never
drift from the v3.6.7-hardened sources (the Pattern C3 surface that the §6
inversion sweep + INV-1/2/3 lint closed). A copy CAN drift; CI byte-equality
closes that again.

Invariants:
  1. agents/*.md is exactly the MIRRORS roster (set equality). A deleted
     mirror silently un-ships a plugin agent; an unrostered addition has no
     declared source to stay in sync with. Editing the roster is a deliberate
     plugin-surface change, made here in lockstep with the tree.
  2. Every mirror is a regular file, never a symlink — the #413 regression.
     Checked before byte-equality (a symlink byte-matches its own target).
  3. Every mirror is byte-identical to its canonical source. To change an
     agent: edit the SOURCE under deep-research/agents/, then re-copy
     (`cp <source> <mirror>`). Never edit the mirror.

Related: check_version_consistency.py invariant 8 excludes agents/ from the
unique-agent count, and check_v3_10_134_write_scope.py I5 maps agents/ files
back to their deep-research sources — both rely on THIS lint pinning the
mirror set to byte-identical aliases.
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# mirror (plugin surface) -> canonical source. Keys must be the full contents
# of agents/*.md (invariant 1).
MIRRORS = {
    "agents/report_compiler_agent.md":
        "deep-research/agents/report_compiler_agent.md",
    "agents/research_architect_agent.md":
        "deep-research/agents/research_architect_agent.md",
    "agents/synthesis_agent.md":
        "deep-research/agents/synthesis_agent.md",
}


def check(root: Path) -> list[str]:
    errors: list[str] = []

    roster = set(MIRRORS)
    agents_dir = root / "agents"
    on_disk = (
        {p.relative_to(root).as_posix() for p in agents_dir.glob("*.md")}
        if agents_dir.is_dir() else set()
    )
    for mirror in sorted(roster - on_disk):
        errors.append(
            f"{mirror}: rostered mirror is missing — the plugin would "
            f"silently un-ship this agent (restore with `cp "
            f"{MIRRORS[mirror]} {mirror}`)"
        )
    for extra in sorted(on_disk - roster):
        errors.append(
            f"{extra}: not in the MIRRORS roster — an unrostered agents/ "
            "file has no declared source to stay in sync with. Add it to "
            "the roster in check_agents_mirror_sync.py (a deliberate "
            "plugin-surface change) or remove it."
        )

    for mirror, source in sorted(MIRRORS.items()):
        mp = root / mirror
        if not mp.exists() and not mp.is_symlink():
            # Truly absent — already reported missing above. A BROKEN symlink
            # has exists()==False but is_symlink()==True and must fall through
            # to the symlink branch; collapsing this to `not mp.exists()`
            # would silently skip broken links — the #413 regression itself.
            continue
        if mp.is_symlink():
            errors.append(
                f"{mirror}: is a symlink — #413 regression (breaks Windows "
                f"checkouts and zip installs). Replace with a real copy: "
                f"`rm {mirror} && cp {source} {mirror}`"
            )
            continue
        sp = root / source
        if not sp.is_file():
            errors.append(
                f"{source}: canonical source for {mirror} is missing"
            )
            continue
        if mp.read_bytes() != sp.read_bytes():
            errors.append(
                f"{mirror}: byte-drift from {source} — edit the source, "
                f"then re-copy: `cp {source} {mirror}`"
            )

    return errors


def main() -> int:
    errors = check(REPO_ROOT)
    if errors:
        print("agents/ mirror sync check failed (#413):")
        for err in errors:
            print(f"- {err}")
        return 1
    print("agents/ mirror sync check passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
