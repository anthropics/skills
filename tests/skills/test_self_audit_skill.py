"""Tests for skills/self-audit/SKILL.md

Validates SKILL.md metadata, structure, and HARDLINE rule compliance.
"""

import re
from pathlib import Path

import pytest


def _load_yaml():
    import yaml as _yaml
    return _yaml


SKILL_DIR = (
    Path(__file__).resolve().parents[2]
    / "skills"
    / "self-audit"
)
SKILL_MD = SKILL_DIR / "SKILL.md"


def _read_skill():
    yaml = _load_yaml()
    text = SKILL_MD.read_text(encoding="utf-8")
    parts = text.split("---", 2)
    if len(parts) < 3:
        raise ValueError("SKILL.md missing YAML frontmatter delimiters")
    frontmatter = yaml.safe_load(parts[1])
    body = parts[2]
    return frontmatter, body


class TestSkillExists:
    def test_skill_md_present(self):
        assert SKILL_MD.exists(), f"SKILL.md not found at {SKILL_MD}"
        assert SKILL_MD.is_file()

    def test_no_scripts_dir(self):
        scripts = SKILL_DIR / "scripts"
        assert not scripts.exists(), (
            "This is a pure prompt-pattern skill. "
            "Remove scripts/ — if scripts are needed, add them with tests."
        )


class TestFrontmatter:
    @pytest.fixture(autouse=True)
    def load(self):
        self.fm, self.body = _read_skill()

    def test_name_matches_directory(self):
        assert self.fm["name"] == "self-audit"

    def test_description_length(self):
        desc = self.fm["description"]
        assert len(desc) <= 120, (
            f"description is {len(desc)} chars (max 120): {desc!r}"
        )

    def test_description_ends_with_period(self):
        assert self.fm["description"].endswith(".")

    def test_version_present(self):
        assert "version" in self.fm

    def test_author_not_hermes_agent(self):
        author = self.fm.get("author", "")
        if author:
            assert author != "Hermes Agent"

    def test_tags_present(self):
        tags = self.fm.get("tags", [])
        assert len(tags) >= 2, "skill should have at least 2 tags"


class TestRequiredSections:
    REQUIRED = [
        "When to Use",
        "Step 0",
        "The Four Questions",
        "Process",
        "Failure Modes",
        "Common Rationalizations",
        "Red Flags",
        "Verification",
        "Background",
    ]

    @pytest.fixture(autouse=True)
    def load(self):
        self.fm, self.body = _read_skill()

    @pytest.mark.parametrize("section", REQUIRED)
    def test_section_present(self, section):
        assert f"## {section}" in self.body, (
            f"Missing required section: ## {section}"
        )

    def test_section_order(self):
        positions = {}
        for section in self.REQUIRED:
            idx = self.body.find(f"## {section}")
            if idx >= 0:
                positions[section] = idx
        ordered = sorted(positions.items(), key=lambda x: x[1])
        ordered_names = [name for name, _ in ordered]
        present_required = [s for s in self.REQUIRED if s in positions]
        assert ordered_names == present_required, (
            f"Sections out of order. Expected: {present_required}, "
            f"Got: {ordered_names}"
        )


class TestBodyQuality:
    @pytest.fixture(autouse=True)
    def load(self):
        self.fm, self.body = _read_skill()

    def test_line_count(self):
        lines = self.body.strip().split("\n")
        assert len(lines) <= 250, (
            f"Body is {len(lines)} lines — too long for a prompt-pattern skill"
        )

    def test_first_heading_is_title(self):
        for line in self.body.split("\n"):
            stripped = line.strip()
            if stripped.startswith("# "):
                assert "Self-Audit" in stripped
                break

    def test_step_zero_before_four_questions(self):
        """Step 0 must appear before The Four Questions section."""
        step0_idx = self.body.find("## Step 0")
        questions_idx = self.body.find("## The Four Questions")
        assert step0_idx >= 0, "Step 0 section missing"
        assert questions_idx >= 0, "The Four Questions section missing"
        assert step0_idx < questions_idx, (
            "Step 0 must appear before The Four Questions"
        )

    def test_file_read_tool_referenced_in_step_zero(self):
        step0_start = self.body.find("## Step 0")
        questions_start = self.body.find("## The Four Questions")
        step0_text = self.body[step0_start:questions_start]
        assert "file-read" in step0_text.lower() or "read_file" in step0_text.lower(), (
            "Step 0 must reference file-read tool for mechanical verification"
        )


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
