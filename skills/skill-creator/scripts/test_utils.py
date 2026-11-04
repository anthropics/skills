"""Tests for skill-creator utils.parse_skill_md."""

import tempfile
from pathlib import Path

from utils import parse_skill_md


def _write_skill(directory: Path, frontmatter: str, body: str = "# Body\n") -> Path:
    skill_dir = Path(directory)
    (skill_dir / "SKILL.md").write_text(f"---\n{frontmatter}\n---\n\n{body}")
    return skill_dir


def test_single_line_description(tmp_path):
    skill_dir = _write_skill(tmp_path, 'name: my-skill\ndescription: "A short skill."')
    name, description, _ = parse_skill_md(skill_dir)
    assert name == "my-skill"
    assert description == "A short skill."


def test_folded_scalar_description(tmp_path):
    skill_dir = _write_skill(
        tmp_path,
        "name: my-skill\ndescription: >-\n  First paragraph.\n  Second paragraph.",
    )
    _, description, _ = parse_skill_md(skill_dir)
    assert "First paragraph." in description
    assert "Second paragraph." in description


def test_folded_scalar_with_blank_line_keeps_both_paragraphs(tmp_path):
    """Regression: a blank line inside a folded/literal block scalar must not
    truncate the description. Previously the continuation loop stopped at the
    first blank line, dropping everything after it."""
    skill_dir = _write_skill(
        tmp_path,
        "name: my-skill\ndescription: >-\n  First paragraph.\n\n  Second paragraph.",
    )
    _, description, _ = parse_skill_md(skill_dir)
    assert "First paragraph." in description
    assert "Second paragraph." in description


def test_literal_scalar_description(tmp_path):
    skill_dir = _write_skill(
        tmp_path,
        "name: my-skill\ndescription: |-\n  Line one.\n  Line two.",
    )
    _, description, _ = parse_skill_md(skill_dir)
    assert "Line one." in description
    assert "Line two." in description


def test_returns_full_content(tmp_path):
    skill_dir = _write_skill(tmp_path, "name: my-skill\ndescription: A skill.")
    _, _, content = parse_skill_md(skill_dir)
    assert "# Body" in content
