"""Tests for skill-creator package_skill."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from package_skill import should_exclude


def test_excludes_pycache_anywhere():
    # arcname is relative to skill_path.parent, so parts[0] is the skill name
    assert should_exclude(Path("my-skill/__pycache__/foo.pyc"))


def test_excludes_node_modules_anywhere():
    assert should_exclude(Path("my-skill/sub/node_modules/pkg/index.js"))


def test_excludes_pyc_glob():
    assert should_exclude(Path("my-skill/scripts/app.pyc"))


def test_excludes_ds_store():
    assert should_exclude(Path("my-skill/.DS_Store"))


def test_excludes_evals_at_root_only():
    # evals at the skill root (parts[1]) is excluded
    assert should_exclude(Path("my-skill/evals/run.json"))
    # evals nested deeper is NOT excluded
    assert not should_exclude(Path("my-skill/sub/evals/run.json"))


def test_keeps_regular_files():
    assert not should_exclude(Path("my-skill/SKILL.md"))
    assert not should_exclude(Path("my-skill/scripts/app.py"))
    assert not should_exclude(Path("my-skill/assets/logo.png"))


def test_import_works_direct():
    """Regression: `from scripts.quick_validate import validate_skill` failed
    when package_skill.py was run directly (the scripts package was not on the
    path). The module must now import without error either way."""
    import package_skill as mod
    assert callable(mod.validate_skill)
    assert callable(mod.package_skill)
