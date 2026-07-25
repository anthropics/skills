#!/usr/bin/env python3
"""Tests for check_agents_mirror_sync.py (#413).

Mutation discipline: every invariant has a passing case (green fixture tree +
the real repo tree) and a failing case proving the check fires when the
guarded property is broken. The symlink case is the load-bearing one: a
symlink trivially byte-matches its own target, so a byte-equality-only lint
would silently re-admit the #413 regression.
"""
from __future__ import annotations

from pathlib import Path

import pytest

from check_agents_mirror_sync import MIRRORS, REPO_ROOT, check


def make_tree(root: Path) -> None:
    """A green fixture tree: every rostered mirror is a real byte-identical
    copy of its source."""
    for mirror, source in MIRRORS.items():
        src = root / source
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_text(f"---\nname: {Path(source).stem}\n---\nbody\n",
                       encoding="utf-8")
        dst = root / mirror
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(src.read_bytes())


def first_mirror() -> tuple[str, str]:
    mirror, source = sorted(MIRRORS.items())[0]
    return mirror, source


# --- invariant 0: the real tree is green -------------------------------------

def test_real_repo_passes():
    assert check(REPO_ROOT) == []


# --- green fixture ------------------------------------------------------------

def test_green_tree_passes(tmp_path):
    make_tree(tmp_path)
    assert check(tmp_path) == []


# --- invariant 1: set equality -------------------------------------------------

def test_missing_mirror_fails(tmp_path):
    # A deleted mirror silently un-ships a plugin agent.
    make_tree(tmp_path)
    mirror, _ = first_mirror()
    (tmp_path / mirror).unlink()
    errs = check(tmp_path)
    assert errs and any(mirror in e and "missing" in e for e in errs)


def test_unrostered_extra_fails(tmp_path):
    # An unrostered agents/*.md has no declared source to stay in sync with.
    make_tree(tmp_path)
    (tmp_path / "agents" / "rogue_agent.md").write_text("rogue\n",
                                                        encoding="utf-8")
    errs = check(tmp_path)
    assert errs and any("rogue_agent.md" in e for e in errs)


def test_agents_dir_absent_reports_all_mirrors(tmp_path):
    make_tree(tmp_path)
    for mirror in MIRRORS:
        (tmp_path / mirror).unlink()
    (tmp_path / "agents").rmdir()
    errs = check(tmp_path)
    assert len([e for e in errs if "missing" in e]) == len(MIRRORS)


# --- invariant 2: regular file, never a symlink --------------------------------

def test_symlink_mirror_fails(tmp_path):
    # The #413 regression itself. Checked BEFORE byte-equality: a symlink
    # byte-matches its own target, so equality alone would pass it.
    make_tree(tmp_path)
    mirror, source = first_mirror()
    mp = tmp_path / mirror
    mp.unlink()
    try:
        mp.symlink_to(tmp_path / source)
    except OSError:
        pytest.skip("symlinks unavailable on this platform")
    errs = check(tmp_path)
    assert errs and any(mirror in e and "symlink" in e for e in errs)


# --- invariant 3: byte equality with the canonical source ----------------------

def test_drifted_mirror_fails_with_cp_hint(tmp_path):
    make_tree(tmp_path)
    mirror, source = first_mirror()
    (tmp_path / mirror).write_text("drifted\n", encoding="utf-8")
    errs = check(tmp_path)
    assert errs
    hit = next(e for e in errs if mirror in e)
    # The fix hint names the copy direction: source -> mirror, never backwards.
    assert f"cp {source} {mirror}" in hit


def test_drifted_source_also_fails(tmp_path):
    # Symmetric: editing the SOURCE without re-copying must fail too — that
    # is the Pattern C3 drift the retired symlinks used to make impossible.
    make_tree(tmp_path)
    mirror, source = first_mirror()
    (tmp_path / source).write_text("hardened update\n", encoding="utf-8")
    errs = check(tmp_path)
    assert errs and any(mirror in e for e in errs)


def test_missing_source_fails(tmp_path):
    make_tree(tmp_path)
    mirror, source = first_mirror()
    (tmp_path / source).unlink()
    errs = check(tmp_path)
    assert errs and any(source in e and "source" in e for e in errs)


# --- roster shape ---------------------------------------------------------------

def test_roster_is_the_three_plugin_agents():
    # v3.7.0 Phase 2.1 shipped exactly these three; a roster edit is a
    # deliberate plugin-surface change, not drift.
    assert set(MIRRORS) == {
        "agents/report_compiler_agent.md",
        "agents/research_architect_agent.md",
        "agents/synthesis_agent.md",
    }
    assert all(s.startswith("deep-research/agents/") for s in MIRRORS.values())
