"""Frontmatter key tests for ``scripts/quick_validate.py``.

The accepted key set must match the SKILL.md frontmatter reference at
https://code.claude.com/docs/en/skills.md (section "Frontmatter reference").
"""

from pathlib import Path

import pytest

from scripts.quick_validate import validate_skill

# Every key the Claude Code skills documentation lists, with a valid value.
DOCUMENTED_FRONTMATTER = """\
name: full-frontmatter
description: Exercises every documented frontmatter key.
when_to_use: When the user asks for a frontmatter demo.
argument-hint: "[issue-number]"
arguments: issue branch
disable-model-invocation: false
user-invocable: true
allowed-tools: Read, Grep
disallowed-tools: Bash
model: inherit
effort: high
context: fork
agent: Explore
background: false
hooks:
  PreToolUse: []
paths: "src/**/*.py"
shell: bash
metadata:
  author: Example Author
license: MIT
compatibility: Requires git.
"""


def write_skill(skill_dir: Path, frontmatter: str) -> Path:
    skill_dir.mkdir(parents=True, exist_ok=True)
    (skill_dir / "SKILL.md").write_text(f"---\n{frontmatter}---\n\n# Body\n")
    return skill_dir


def test_accepts_every_documented_key(tmp_path):
    skill_dir = write_skill(tmp_path / "full-frontmatter", DOCUMENTED_FRONTMATTER)

    valid, message = validate_skill(skill_dir)

    assert valid, message


@pytest.mark.parametrize("undocumented_key", ["version", "tags", "author"])
def test_rejects_undocumented_key(tmp_path, undocumented_key):
    frontmatter = f"name: demo\ndescription: Demo.\n{undocumented_key}: x\n"
    skill_dir = write_skill(tmp_path / "demo", frontmatter)

    valid, message = validate_skill(skill_dir)

    assert not valid
    assert "Unexpected key" in message
    assert undocumented_key in message
