import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from scripts.quick_validate import validate_skill


class QuickValidateExtensionTests(unittest.TestCase):
    def _write_skill(self, root: Path, frontmatter: str) -> Path:
        skill_dir = root / "example-skill"
        skill_dir.mkdir()
        (skill_dir / "SKILL.md").write_text(
            f"---\n{frontmatter}\n---\n\n# Example\n",
            encoding="utf-8",
        )
        return skill_dir

    def test_standard_frontmatter_remains_valid_without_warning(self):
        with tempfile.TemporaryDirectory() as tmp:
            skill_dir = self._write_skill(
                Path(tmp),
                "name: example-skill\ndescription: Example skill",
            )
            stderr = io.StringIO()

            with contextlib.redirect_stderr(stderr):
                valid, message = validate_skill(skill_dir)

            self.assertTrue(valid)
            self.assertEqual(message, "Skill is valid!")
            self.assertEqual(stderr.getvalue(), "")

    def test_platform_extensions_warn_but_validate(self):
        with tempfile.TemporaryDirectory() as tmp:
            skill_dir = self._write_skill(
                Path(tmp),
                "\n".join(
                    [
                        "name: example-skill",
                        "description: Example skill",
                        "model: sonnet",
                        "context: fork",
                        "user-invocable: false",
                    ]
                ),
            )
            stderr = io.StringIO()

            with contextlib.redirect_stderr(stderr):
                valid, message = validate_skill(skill_dir)

            self.assertTrue(valid)
            self.assertEqual(message, "Skill is valid!")
            warning = stderr.getvalue()
            self.assertIn("non-standard SKILL.md frontmatter key(s)", warning)
            self.assertIn("context", warning)
            self.assertIn("model", warning)
            self.assertIn("user-invocable", warning)

    def test_unknown_extension_warns_instead_of_blocking_packaging(self):
        with tempfile.TemporaryDirectory() as tmp:
            skill_dir = self._write_skill(
                Path(tmp),
                "\n".join(
                    [
                        "name: example-skill",
                        "description: Example skill",
                        "custom-platform-field: enabled",
                    ]
                ),
            )
            stderr = io.StringIO()

            with contextlib.redirect_stderr(stderr):
                valid, message = validate_skill(skill_dir)

            self.assertTrue(valid)
            self.assertEqual(message, "Skill is valid!")
            self.assertIn("custom-platform-field", stderr.getvalue())

    def test_required_fields_still_fail_validation(self):
        with tempfile.TemporaryDirectory() as tmp:
            skill_dir = self._write_skill(
                Path(tmp),
                "name: example-skill\nmodel: sonnet",
            )

            valid, message = validate_skill(skill_dir)

            self.assertFalse(valid)
            self.assertEqual(message, "Missing 'description' in frontmatter")


if __name__ == "__main__":
    unittest.main()
