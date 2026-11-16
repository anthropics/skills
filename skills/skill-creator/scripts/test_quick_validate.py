"""Tests for quick_validate.validate_skill.

Run with:  python -m pytest skills/skill-creator/scripts/test_quick_validate.py
Requires:  pytest, pyyaml
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent))
from quick_validate import validate_skill  # noqa: E402

REPO_SKILLS_DIR = Path(__file__).resolve().parents[2]


def make_skill(tmp_path, frontmatter, body="# Skill\n"):
    """Write a SKILL.md with the given raw frontmatter text and return its directory."""
    skill_dir = tmp_path / "my-skill"
    skill_dir.mkdir()
    (skill_dir / "SKILL.md").write_text(f"---\n{frontmatter}\n---\n{body}", newline="\n")
    return skill_dir


def test_valid_minimal_skill(tmp_path):
    skill = make_skill(tmp_path, "name: my-skill\ndescription: Does a thing.")
    assert validate_skill(skill) == (True, "Skill is valid!")


def test_valid_with_all_optional_fields(tmp_path):
    skill = make_skill(
        tmp_path,
        "name: my-skill\n"
        "description: Does a thing.\n"
        "license: MIT\n"
        "allowed-tools: Read\n"
        "compatibility: Requires Python 3.10+\n"
        "metadata:\n  author: someone\n  version: 1",
    )
    valid, message = validate_skill(skill)
    assert valid, message


def test_missing_skill_md(tmp_path):
    assert validate_skill(tmp_path) == (False, "SKILL.md not found")


def test_no_frontmatter(tmp_path):
    (tmp_path / "SKILL.md").write_text("# Just a heading\n")
    assert validate_skill(tmp_path) == (False, "No YAML frontmatter found")


def test_unterminated_frontmatter(tmp_path):
    (tmp_path / "SKILL.md").write_text("---\nname: x\n", newline="\n")
    assert validate_skill(tmp_path) == (False, "Invalid frontmatter format")


def test_invalid_yaml(tmp_path):
    skill = make_skill(tmp_path, "name: [unclosed")
    valid, message = validate_skill(skill)
    assert not valid
    assert message.startswith("Invalid YAML in frontmatter")


def test_frontmatter_not_a_dict(tmp_path):
    skill = make_skill(tmp_path, "- just\n- a list")
    assert validate_skill(skill) == (False, "Frontmatter must be a YAML dictionary")


def test_unexpected_key(tmp_path):
    skill = make_skill(tmp_path, "name: my-skill\ndescription: x\nauthor: me")
    valid, message = validate_skill(skill)
    assert not valid
    assert "Unexpected key(s)" in message and "author" in message


@pytest.mark.parametrize("missing", ["name", "description"])
def test_missing_required_field(tmp_path, missing):
    fields = {"name": "name: my-skill", "description": "description: x"}
    del fields[missing]
    skill = make_skill(tmp_path, "\n".join(fields.values()))
    assert validate_skill(skill) == (False, f"Missing '{missing}' in frontmatter")


@pytest.mark.parametrize(
    "name",
    ["My-Skill", "my_skill", "my skill", "-leading", "trailing-", "double--hyphen", "a" * 65],
)
def test_invalid_names(tmp_path, name):
    skill = make_skill(tmp_path, f"name: '{name}'\ndescription: x")
    valid, _ = validate_skill(skill)
    assert not valid


@pytest.mark.parametrize("name", ["a", "my-skill", "skill2", "a" * 64])
def test_valid_names(tmp_path, name):
    skill = make_skill(tmp_path, f"name: '{name}'\ndescription: x")
    valid, message = validate_skill(skill)
    assert valid, message


def test_name_must_be_string(tmp_path):
    skill = make_skill(tmp_path, "name: 123\ndescription: x")
    assert validate_skill(skill) == (False, "Name must be a string, got int")


def test_description_must_be_string(tmp_path):
    skill = make_skill(tmp_path, "name: my-skill\ndescription: [a, b]")
    assert validate_skill(skill) == (False, "Description must be a string, got list")


@pytest.mark.parametrize("desc", ["Use <tag> here", "a > b"])
def test_description_rejects_angle_brackets(tmp_path, desc):
    skill = make_skill(tmp_path, f"name: my-skill\ndescription: '{desc}'")
    assert validate_skill(skill) == (False, "Description cannot contain angle brackets (< or >)")


def test_description_length_limit(tmp_path):
    ok = make_skill(tmp_path, f"name: my-skill\ndescription: {'a' * 1024}")
    assert validate_skill(ok)[0]

    (ok / "SKILL.md").unlink()
    (ok / "SKILL.md").write_text(f"---\nname: my-skill\ndescription: {'a' * 1025}\n---\n", newline="\n")
    valid, message = validate_skill(ok)
    assert not valid and "too long (1025" in message


def test_compatibility_length_limit(tmp_path):
    skill = make_skill(tmp_path, f"name: my-skill\ndescription: x\ncompatibility: {'a' * 501}")
    valid, message = validate_skill(skill)
    assert not valid and "Compatibility is too long" in message


def test_compatibility_must_be_string(tmp_path):
    skill = make_skill(tmp_path, "name: my-skill\ndescription: x\ncompatibility: [a]")
    assert validate_skill(skill) == (False, "Compatibility must be a string, got list")


@pytest.mark.parametrize(
    "skill_dir",
    sorted(p.parent for p in REPO_SKILLS_DIR.glob("*/SKILL.md")),
    ids=lambda p: p.name,
)
def test_repo_skills_are_valid(skill_dir):
    """Every skill shipped in this repo should pass its own validator."""
    valid, message = validate_skill(skill_dir)
    assert valid, f"{skill_dir.name}: {message}"
