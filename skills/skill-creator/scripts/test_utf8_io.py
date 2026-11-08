import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from quick_validate import validate_skill
from utils import parse_skill_md


UTF8_SKILL = """---
name: utf8-demo
description: Handles Unicode arrows and emoji
---

This skill includes UTF-8 content: → ✝.
"""


class Utf8FileIOTest(unittest.TestCase):
    def test_quick_validate_reads_skill_md_as_utf8(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            skill_dir = Path(temp_dir)
            (skill_dir / "SKILL.md").write_bytes(UTF8_SKILL.encode("utf-8"))

            valid, message = validate_skill(skill_dir)

        self.assertTrue(valid, message)

    def test_parse_skill_md_reads_skill_md_as_utf8_even_when_default_encoding_is_legacy(self):
        original_read_text = Path.read_text

        def legacy_default_read_text(path, *args, **kwargs):
            if kwargs.get("encoding") is None:
                return Path(path).read_bytes().decode("cp1252")
            return original_read_text(path, *args, **kwargs)

        with tempfile.TemporaryDirectory() as temp_dir:
            skill_dir = Path(temp_dir)
            (skill_dir / "SKILL.md").write_bytes(UTF8_SKILL.encode("utf-8"))

            with patch.object(Path, "read_text", legacy_default_read_text):
                name, description, content = parse_skill_md(skill_dir)

        self.assertEqual(name, "utf8-demo")
        self.assertEqual(description, "Handles Unicode arrows and emoji")
        self.assertIn("→ ✝", content)


if __name__ == "__main__":
    unittest.main()
