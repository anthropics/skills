"""Tests for portable UTF-8 text IO in skill-creator scripts."""

import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.utils import parse_skill_md


class SkillCreatorUtf8IOTest(unittest.TestCase):
    def test_parse_skill_md_reads_utf8_skill_when_default_encoding_is_cp1252(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            skill_path = Path(tmpdir)
            (skill_path / "SKILL.md").write_text(
                "---\n"
                "name: utf8-skill\n"
                "description: Handles music symbol 𝄞 in UTF-8 metadata\n"
                "---\n\n"
                "Body with UTF-8 content: 𝄞\n",
                encoding="utf-8",
            )

            concrete_path_class = type(skill_path / "SKILL.md")
            original_read_text = concrete_path_class.read_text

            def cp1252_default_read_text(
                self,
                encoding=None,
                errors=None,
                newline=None,
            ):
                if encoding is None:
                    encoding = "cp1252"
                return original_read_text(self, encoding=encoding, errors=errors, newline=newline)

            with patch.object(concrete_path_class, "read_text", cp1252_default_read_text):
                name, description, content = parse_skill_md(skill_path)

        self.assertEqual(name, "utf8-skill")
        self.assertEqual(description, "Handles music symbol 𝄞 in UTF-8 metadata")
        self.assertIn("Body with UTF-8 content: 𝄞", content)


if __name__ == "__main__":
    unittest.main()
