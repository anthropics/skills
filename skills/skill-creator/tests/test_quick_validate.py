"""Regression tests for quick_validate.py.

Covers the UTF-8 decoding fix: read_text() without an explicit encoding uses
the locale default (cp1252 on Windows) and crashes on UTF-8 SKILL.md files
whose bytes are undefined in that codec. Also guards the frontmatter parsing
behavior (LF and CRLF line endings - read_text normalizes CRLF - and missing
frontmatter rejection).
"""

import sys
from pathlib import Path

import pytest

SKILL_CREATOR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SKILL_CREATOR))

from scripts.quick_validate import validate_skill  # noqa: E402


FRONTMATTER = """\
---
name: test-skill
description: A test skill for validation.
---
"""


def _write_skill(skill_dir: Path, content: str, newline: str) -> None:
    skill_dir.mkdir()
    (skill_dir / "SKILL.md").write_bytes(content.replace("\n", newline).encode("utf-8"))


def test_lf_skill_is_valid(tmp_path: Path) -> None:
    _write_skill(tmp_path / "test-skill", FRONTMATTER, "\n")
    valid, message = validate_skill(tmp_path / "test-skill")
    assert valid, message


def test_crlf_skill_is_valid(tmp_path: Path) -> None:
    _write_skill(tmp_path / "test-skill", FRONTMATTER, "\r\n")
    valid, message = validate_skill(tmp_path / "test-skill")
    assert valid, message


def test_crlf_skill_with_utf8_content_is_valid(tmp_path: Path) -> None:
    # The warning sign's UTF-8 bytes include 0x9A, which is undefined in the
    # cp1252 locale default encoding on Windows - a bare read_text() crashes.
    content = FRONTMATTER.replace("test skill", "test skill \u26a0\ufe0f")
    _write_skill(tmp_path / "test-skill", content, "\r\n")
    valid, message = validate_skill(tmp_path / "test-skill")
    assert valid, message


def test_missing_frontmatter_is_invalid(tmp_path: Path) -> None:
    skill_dir = tmp_path / "test-skill"
    skill_dir.mkdir()
    (skill_dir / "SKILL.md").write_text("no frontmatter here", encoding="utf-8")
    valid, message = validate_skill(skill_dir)
    assert not valid
