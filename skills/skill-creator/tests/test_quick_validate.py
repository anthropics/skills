"""Tests for the progressive-disclosure skill validator.

Run with:  python -m pytest skills/skill-creator/tests/
"""

import sys
from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS_DIR))

from quick_validate import (  # noqa: E402
    DEFAULT_MAX_LINES,
    DEFAULT_MAX_TOKENS,
    estimate_tokens,
    validate_skill,
    validate_skill_detailed,
)


def make_skill(tmp_path, body, name="my-skill", description="Does a thing.", **frontmatter):
    """Create a minimal skill directory; returns its Path."""
    skill_dir = tmp_path / name
    skill_dir.mkdir()
    frontmatter.setdefault("name", name)
    frontmatter.setdefault("description", description)
    lines = ["---"] + [f"{k}: {v}" for k, v in frontmatter.items()] + ["---", ""]
    (skill_dir / "SKILL.md").write_text("\n".join(lines) + body + "\n", encoding="utf-8")
    return skill_dir


# ---------------------------------------------------------------------------
# Frontmatter hard requirements
# ---------------------------------------------------------------------------


def test_valid_skill_passes(tmp_path):
    skill_dir = make_skill(tmp_path, "\n# My Skill\n\nInstructions here.\n")
    assert validate_skill(skill_dir) == (True, "Skill is valid!")


def test_missing_skill_md_fails(tmp_path):
    empty = tmp_path / "empty"
    empty.mkdir()
    valid, message = validate_skill(empty)
    assert not valid
    assert "SKILL.md not found" in message


def test_name_must_be_kebab_case(tmp_path):
    skill_dir = make_skill(tmp_path, "\nbody\n", name="My_Skill")
    assert not validate_skill(skill_dir)[0]


def test_name_no_leading_or_double_hyphen(tmp_path):
    assert not validate_skill(make_skill(tmp_path, "\nbody\n", name="-lead"))[0]
    assert not validate_skill(make_skill(tmp_path, "\nbody\n", name="a--b"))[0]


def test_name_max_64_chars(tmp_path):
    long_name = "a" * 65
    assert not validate_skill(make_skill(tmp_path, "\nbody\n", name=long_name))[0]


def test_description_required(tmp_path):
    skill_dir = make_skill(tmp_path, "\nbody\n")
    (skill_dir / "SKILL.md").write_text("---\nname: my-skill\n---\n\nbody\n", encoding="utf-8")
    assert not validate_skill(skill_dir)[0]


def test_description_max_1024_chars(tmp_path):
    skill_dir = make_skill(tmp_path, "\nbody\n", description="x" * 1025)
    valid, message = validate_skill(skill_dir)
    assert not valid
    assert "1024" in message


def test_description_no_angle_brackets(tmp_path):
    skill_dir = make_skill(tmp_path, "\nbody\n", description="Use when <foo> happens")
    valid, message = validate_skill(skill_dir)
    assert not valid
    assert "angle brackets" in message


def test_unexpected_frontmatter_key_fails(tmp_path):
    skill_dir = make_skill(tmp_path, "\nbody\n", **{"bogus": "true"})
    valid, message = validate_skill(skill_dir)
    assert not valid
    assert "bogus" in message


def test_compatibility_max_500_chars(tmp_path):
    skill_dir = make_skill(tmp_path, "\nbody\n", compatibility="c" * 501)
    assert not validate_skill(skill_dir)[0]


# ---------------------------------------------------------------------------
# Reference integrity
# ---------------------------------------------------------------------------


def test_broken_directory_scoped_reference_is_error(tmp_path):
    skill_dir = make_skill(tmp_path, "\nSee `references/guide.md` for details.\n")
    result = validate_skill_detailed(skill_dir)
    errors = [f for f in result.findings if f.level == "error"]
    assert any("references/guide.md" in f.message for f in errors)


def test_resolved_reference_passes(tmp_path):
    skill_dir = make_skill(tmp_path, "\nSee `references/guide.md` for details.\n")
    (skill_dir / "references").mkdir()
    (skill_dir / "references" / "guide.md").write_text("Guide.\n", encoding="utf-8")
    assert validate_skill(skill_dir)[0]


def test_lang_placeholder_reference_resolves(tmp_path):
    skill_dir = make_skill(tmp_path, "\nRead `{lang}/claude-api/README.md`.\n")
    (skill_dir / "python").mkdir(parents=True)
    (skill_dir / "python" / "claude-api").mkdir()
    (skill_dir / "python" / "claude-api" / "README.md").write_text("x", encoding="utf-8")
    result = validate_skill_detailed(skill_dir)
    assert result.valid


def test_lang_placeholder_with_no_matching_language_is_error(tmp_path):
    skill_dir = make_skill(tmp_path, "\nRead `{lang}/claude-api/README.md`.\n")
    result = validate_skill_detailed(skill_dir)
    assert not result.valid
    assert any("no language directory" in f.message for f in result.findings)


def test_glob_reference_resolves(tmp_path):
    skill_dir = make_skill(tmp_path, "\nSee `shared/managed-agents-*.md`.\n")
    (skill_dir / "shared").mkdir()
    (skill_dir / "shared" / "managed-agents-core.md").write_text("x", encoding="utf-8")
    assert validate_skill(skill_dir)[0]


def test_bare_filename_prose_mention_is_not_an_error(tmp_path):
    # `README.md` / `CLAUDE.md` in prose are ambiguous, not pointers.
    skill_dir = make_skill(tmp_path, "\nEdit the `CLAUDE.md` file, see `README.md`.\n")
    result = validate_skill_detailed(skill_dir)
    assert result.valid
    assert not any(f.level == "error" for f in result.findings)


# ---------------------------------------------------------------------------
# Progressive-disclosure budgets
# ---------------------------------------------------------------------------


def test_line_budget_warns_by_default_errors_strict(tmp_path):
    body = "\n".join(f"line {i}" for i in range(DEFAULT_MAX_LINES + 10))
    skill_dir = make_skill(tmp_path, "\n" + body + "\n")
    assert validate_skill(skill_dir)[0]  # warning only by default
    assert not validate_skill(skill_dir, strict=True)[0]


def test_token_budget_warns_by_default_errors_strict(tmp_path):
    big_body = "\n" + ("content " * (DEFAULT_MAX_TOKENS * 2)) + "\n"
    skill_dir = make_skill(tmp_path, big_body)
    assert validate_skill(skill_dir)[0]  # warning by default
    assert not validate_skill(skill_dir, strict=True)[0]


def test_within_budget_passes_strict(tmp_path):
    skill_dir = make_skill(tmp_path, "\nSmall skill body.\n")
    result = validate_skill_detailed(skill_dir, strict=True)
    assert result.valid


def test_payload_metrics_reported(tmp_path):
    skill_dir = make_skill(tmp_path, "\nbody\n")
    (skill_dir / "refs").mkdir()
    (skill_dir / "refs" / "a.md").write_text("a" * 400, encoding="utf-8")
    result = validate_skill_detailed(skill_dir)
    m = result.metrics
    assert m["skill_md_tokens"] == estimate_tokens(m["skill_md_chars"])
    assert m["bundled_md_files"] == 1
    assert m["bundled_md_tokens"] == estimate_tokens(m["bundled_md_chars"])
    assert m["payload_tokens"] == estimate_tokens(m["payload_chars"])


def test_estimate_tokens():
    assert estimate_tokens("") == 0
    assert estimate_tokens("abcdefgh") == 2  # 8 chars / 4
    assert estimate_tokens(4000) == 1000  # int char count accepted


# ---------------------------------------------------------------------------
# Encoding robustness (regression for the cp1252 crash on Windows)
# ---------------------------------------------------------------------------


def test_utf8_content_with_emoji_validates(tmp_path):
    skill_dir = make_skill(tmp_path, "\n# Warning ⚠️ 日本語\n\nbody\n")
    result = validate_skill_detailed(skill_dir)
    assert result.valid
