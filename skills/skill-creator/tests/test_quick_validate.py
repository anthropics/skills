"""Regression tests for optional compatibility frontmatter validation."""

import importlib.util
import tempfile
import unittest
from pathlib import Path

import yaml


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "quick_validate.py"
SPEC = importlib.util.spec_from_file_location("quick_validate", SCRIPT)
quick_validate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(quick_validate)


class CompatibilityValidationTests(unittest.TestCase):
    def validate(self, **extra_fields):
        frontmatter = {"name": "test-skill", "description": "A test skill."}
        frontmatter.update(extra_fields)
        with tempfile.TemporaryDirectory() as directory:
            skill_md = Path(directory) / "SKILL.md"
            skill_md.write_text(
                "---\n" + yaml.safe_dump(frontmatter) + "---\n# Test skill\n",
                encoding="utf-8",
            )
            return quick_validate.validate_skill(directory)

    def test_compatibility_can_be_omitted(self):
        self.assertEqual(self.validate(), (True, "Skill is valid!"))

    def test_rejects_falsy_non_string_compatibility(self):
        for value in (False, 0, None, [], {}):
            with self.subTest(value=value):
                self.assertEqual(
                    self.validate(compatibility=value),
                    (False, f"Compatibility must be a string, got {type(value).__name__}"),
                )

    def test_rejects_empty_compatibility(self):
        self.assertEqual(
            self.validate(compatibility=""),
            (False, "Compatibility cannot be empty"),
        )

    def test_compatibility_length_boundaries(self):
        for value in ("x", "x" * 500):
            with self.subTest(length=len(value)):
                self.assertEqual(
                    self.validate(compatibility=value), (True, "Skill is valid!")
                )
        self.assertEqual(
            self.validate(compatibility="x" * 501),
            (False, "Compatibility is too long (501 characters). Maximum is 500 characters."),
        )


if __name__ == "__main__":
    unittest.main()
