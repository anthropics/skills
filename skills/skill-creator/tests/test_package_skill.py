import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path


SKILL_CREATOR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SKILL_CREATOR))

from scripts.package_skill import package_skill


class PackageSkillTests(unittest.TestCase):
    def test_rejects_symlink_to_file_outside_skill(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            skill = root / "demo"
            skill.mkdir()
            (skill / "SKILL.md").write_text(
                "---\nname: demo\ndescription: A test skill\n---\n",
                encoding="utf-8",
            )
            outside = root / "private.txt"
            outside.write_text("private content", encoding="utf-8")
            try:
                (skill / "reference.txt").symlink_to(outside)
            except OSError as exc:
                self.skipTest(f"symlinks unavailable: {exc}")

            output = root / "dist"
            with contextlib.redirect_stdout(io.StringIO()):
                result = package_skill(skill, output)

            self.assertIsNone(result)
            self.assertFalse((output / "demo.skill").exists())


if __name__ == "__main__":
    unittest.main()
