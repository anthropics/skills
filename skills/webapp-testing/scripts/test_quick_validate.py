#!/usr/bin/env python3
"""Tests for quick_validate.py. Run from the skill-creator directory:
    python -m unittest scripts/test_quick_validate.py -v
"""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from quick_validate import validate_skill  # noqa: E402


class QuickValidateTests(unittest.TestCase):
    def check(self, content: bytes, dirname: str = "my-skill"):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        d = Path(tmp.name) / dirname
        d.mkdir()
        (d / "SKILL.md").write_bytes(content)
        return validate_skill(d)

    def test_valid_skill(self):
        ok, msg = self.check(b"---\nname: my-skill\ndescription: Does a thing. Use when asked.\n---\n# Body\n")
        self.assertTrue(ok, msg)

    def test_empty_name_rejected(self):
        ok, msg = self.check(b'---\nname: ""\ndescription: x\n---\nbody\n')
        self.assertFalse(ok)
        self.assertIn("name", msg)

    def test_whitespace_only_description_rejected(self):
        ok, msg = self.check(b'---\nname: my-skill\ndescription: "   "\n---\nbody\n')
        self.assertFalse(ok)
        self.assertIn("description", msg)

    def test_null_name_rejected(self):
        # `name:` with no value parses to None
        ok, _ = self.check(b"---\nname:\ndescription: x\n---\nbody\n")
        self.assertFalse(ok)

    def test_utf8_bom_accepted(self):
        ok, msg = self.check(b"\xef\xbb\xbf---\nname: my-skill\ndescription: x\n---\nbody\n")
        self.assertTrue(ok, msg)

    def test_non_ascii_description_accepted(self):
        text = "---\nname: my-skill\ndescription: Résumé — café ☕ 日本語\n---\nbody\n"
        ok, msg = self.check(text.encode("utf-8"))
        self.assertTrue(ok, msg)

    def test_existing_rules_still_enforced(self):
        self.assertFalse(self.check(b"no frontmatter\n")[0])
        self.assertFalse(self.check(b"---\nname: Bad_Name\ndescription: x\n---\n")[0])
        self.assertFalse(self.check(b"---\nname: my-skill\ndescription: a <b> c\n---\n")[0])
        self.assertFalse(self.check(b"---\nname: my-skill\ndescription: x\nbogus: 1\n---\n")[0])
        long_desc = ("x" * 1025).encode()
        self.assertFalse(self.check(b"---\nname: my-skill\ndescription: " + long_desc + b"\n---\n")[0])


if __name__ == "__main__":
    unittest.main()
