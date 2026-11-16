import sys
from pathlib import Path
import tempfile
import unittest

# Ensure scripts directory is on sys.path
SCRIPTS_DIR = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS_DIR))

from quick_validate import validate_skill
from package_skill import should_exclude
from utils import parse_skill_md


class TestSkillValidationAndPackaging(unittest.TestCase):

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.skill_dir = Path(self.temp_dir.name) / "test-skill"
        self.skill_dir.mkdir(parents=True, exist_ok=True)

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_utf8_non_ascii_skill_validation(self):
        """SKILL.md containing UTF-8 characters (em-dash, curly quotes, accents) must validate cleanly."""
        skill_md = self.skill_dir / "SKILL.md"
        content = (
            "---\n"
            "name: test-skill\n"
            'description: "A skill for testing \u2014 includes non-ASCII \u201cquotes\u201d and accents: caf\u00e9."\n'
            "---\n"
            "# Test Skill\n"
            "Body with Unicode: \u2022 bullet point and em\u2014dash.\n"
        )
        skill_md.write_bytes(content.encode("utf-8"))
        valid, msg = validate_skill(self.skill_dir)
        self.assertTrue(valid, f"Validation failed unexpectedly: {msg}")
        self.assertEqual(msg, "Skill is valid!")

    def test_crlf_frontmatter_validation(self):
        """SKILL.md formatted with Windows CRLF line endings must be parsed correctly."""
        skill_md = self.skill_dir / "SKILL.md"
        content = (
            b"---\r\n"
            b"name: test-crlf-skill\r\n"
            b"description: Validates CRLF line endings in YAML frontmatter.\r\n"
            b"---\r\n"
            b"# CRLF Heading\r\n"
        )
        skill_md.write_bytes(content)
        valid, msg = validate_skill(self.skill_dir)
        self.assertTrue(valid, f"CRLF validation failed: {msg}")

    def test_parse_skill_md_crlf_and_multiline(self):
        """parse_skill_md handles CRLF line endings and multiline description indicators."""
        skill_md = self.skill_dir / "SKILL.md"
        content = (
            b"---\r\n"
            b"name: multiline-skill\r\n"
            b"description: >-\r\n"
            b"  First line of description.\r\n"
            b"  Second line of description.\r\n"
            b"---\r\n"
            b"# Content\r\n"
        )
        skill_md.write_bytes(content)
        name, description, full_content = parse_skill_md(self.skill_dir)
        self.assertEqual(name, "multiline-skill")
        self.assertEqual(description, "First line of description. Second line of description.")
        self.assertIn("# Content", full_content)

    def test_package_skill_should_exclude(self):
        """should_exclude correctly filters out build artifacts, cache, and root evals."""
        self.assertTrue(should_exclude(Path("my-skill/__pycache__/cache.pyc")))
        self.assertTrue(should_exclude(Path("my-skill/.DS_Store")))
        self.assertTrue(should_exclude(Path("my-skill/module.pyc")))
        self.assertTrue(should_exclude(Path("my-skill/evals/test_eval.json")))
        self.assertFalse(should_exclude(Path("my-skill/scripts/helper.py")))
        self.assertFalse(should_exclude(Path("my-skill/SKILL.md")))


if __name__ == "__main__":
    unittest.main()
