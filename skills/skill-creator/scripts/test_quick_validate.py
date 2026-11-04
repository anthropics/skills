"""Tests for skill-creator quick_validate.validate_skill."""

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from quick_validate import validate_skill


def _write_skill(directory: Path, frontmatter: str, body: str = "# Body\n") -> Path:
    skill_dir = Path(directory)
    (skill_dir / "SKILL.md").write_text(f"---\n{frontmatter}\n---\n\n{body}")
    return skill_dir


def test_valid_skill(tmp_path):
    valid, msg = validate_skill(
        _write_skill(tmp_path, 'name: my-skill\ndescription: "A useful skill."')
    )
    assert valid, msg


def test_missing_skill_md(tmp_path):
    valid, msg = validate_skill(tmp_path)
    assert not valid
    assert "SKILL.md not found" in msg


def test_empty_name_rejected(tmp_path):
    """Regression: an empty name string passed the presence check and then
    skipped all format validation, so `name: ""` was accepted as valid."""
    valid, msg = validate_skill(
        _write_skill(tmp_path, 'name: ""\ndescription: "A skill"')
    )
    assert not valid
    assert "empty" in msg.lower()


def test_empty_description_rejected(tmp_path):
    valid, msg = validate_skill(
        _write_skill(tmp_path, 'name: my-skill\ndescription: ""')
    )
    assert not valid
    assert "empty" in msg.lower()


def test_non_string_name_rejected(tmp_path):
    valid, msg = validate_skill(
        _write_skill(tmp_path, "name: 123\ndescription: A skill")
    )
    assert not valid


def test_invalid_kebab_name_rejected(tmp_path):
    valid, msg = validate_skill(
        _write_skill(tmp_path, "name: My_Skill\ndescription: A skill")
    )
    assert not valid
    assert "kebab" in msg.lower()


def test_name_too_long_rejected(tmp_path):
    long_name = "a" * 65
    valid, msg = validate_skill(
        _write_skill(tmp_path, f"name: {long_name}\ndescription: A skill")
    )
    assert not valid
    assert "64" in msg


def test_description_angle_brackets_rejected(tmp_path):
    valid, msg = validate_skill(
        _write_skill(tmp_path, "name: my-skill\ndescription: 'use <tags>'")
    )
    assert not valid


def test_description_too_long_rejected(tmp_path):
    long_desc = "x" * 1025
    valid, msg = validate_skill(
        _write_skill(tmp_path, f"name: my-skill\ndescription: {long_desc}")
    )
    assert not valid
    assert "1024" in msg
