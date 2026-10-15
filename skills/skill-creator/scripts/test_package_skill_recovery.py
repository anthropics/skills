"""Packaging recovery tests with local fixtures and a fault-injected ZIP writer."""

import contextlib
import io
import subprocess
import sys
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest.mock import patch

from scripts import package_skill


class PackageSkillRecoveryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.skill = self.root / "demo"
        self.skill.mkdir()
        (self.skill / "SKILL.md").write_text("---\nname: demo\ndescription: Local fixture.\n---\nBody\n")
        self.output = self.root / "dist"
        self.output.mkdir()
        self.archive = self.output / "demo.skill"

    def invoke(self, *, failure="write", captured=None):
        class Writer:
            def __init__(self, path, *args):
                self.path = Path(path)
                self.path.write_bytes(b"PARTIAL NEW ARCHIVE")

            def __enter__(self):
                return self

            def write(self, *args):
                if failure == "write":
                    raise OSError("injected source read failure")

            def __exit__(self, *args):
                if failure == "close":
                    raise OSError("injected archive close failure")

        with patch.object(package_skill.zipfile, "ZipFile", Writer), contextlib.redirect_stdout(captured or io.StringIO()):
            return package_skill.package_skill(self.skill, self.output)

    def test_failed_write_or_close_preserves_previous_archive(self):
        for failure in ("write", "close"):
            with self.subTest(failure=failure):
                self.archive.write_bytes(b"PREVIOUS GOOD ARCHIVE")
                self.assertIsNone(self.invoke(failure=failure))
                self.assertEqual(self.archive.read_bytes(), b"PREVIOUS GOOD ARCHIVE")
                self.assertEqual(list(self.output.iterdir()), [self.archive])

    def test_failed_first_package_leaves_no_partial_output(self):
        self.assertIsNone(self.invoke())
        self.assertFalse(self.archive.exists())
        self.assertEqual(list(self.output.iterdir()), [])

    def test_failed_promotion_preserves_previous_archive(self):
        self.archive.write_bytes(b"PREVIOUS GOOD ARCHIVE")
        with patch.object(Path, "replace", side_effect=OSError("injected promotion failure")):
            self.assertIsNone(self.invoke(failure="none"))
        self.assertEqual(self.archive.read_bytes(), b"PREVIOUS GOOD ARCHIVE")
        self.assertEqual(list(self.output.iterdir()), [self.archive])

    def test_failed_staging_cleanup_preserves_previous_and_reports_leftover(self):
        self.archive.write_bytes(b"PREVIOUS GOOD ARCHIVE")
        captured = io.StringIO()
        with patch.object(Path, "unlink", side_effect=OSError("injected cleanup failure")):
            self.assertIsNone(self.invoke(captured=captured))
        self.assertEqual(self.archive.read_bytes(), b"PREVIOUS GOOD ARCHIVE")
        leftovers = [path for path in self.output.iterdir() if path != self.archive]
        self.assertEqual(len(leftovers), 1)
        self.assertIn(str(leftovers[0]), captured.getvalue())

    def test_success_publishes_a_readable_archive_after_replacement(self):
        self.archive.write_bytes(b"PREVIOUS GOOD ARCHIVE")
        with contextlib.redirect_stdout(io.StringIO()):
            result = package_skill.package_skill(self.skill, self.output)
        self.assertEqual(result, self.archive)
        with zipfile.ZipFile(result) as archive:
            self.assertEqual(archive.namelist(), ["demo/SKILL.md"])
            self.assertEqual(archive.read("demo/SKILL.md"), (self.skill / "SKILL.md").read_bytes())
        self.assertEqual(list(self.output.iterdir()), [self.archive])

    def test_output_inside_skill_does_not_include_its_staging_file(self):
        with contextlib.redirect_stdout(io.StringIO()):
            result = package_skill.package_skill(self.skill, self.skill)
        with zipfile.ZipFile(result) as archive:
            self.assertEqual(archive.namelist(), ["demo/SKILL.md"])

    def test_name_directory_mismatch_does_not_publish_or_replace_archive(self):
        (self.skill / "SKILL.md").write_text("---\nname: other-name\ndescription: Local fixture.\n---\nBody\n")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertIsNone(package_skill.package_skill(self.skill, self.output))
        self.assertEqual(list(self.output.iterdir()), [])
        self.archive.write_bytes(b"PREVIOUS GOOD ARCHIVE")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertIsNone(package_skill.package_skill(self.skill, self.output))
        self.assertEqual(self.archive.read_bytes(), b"PREVIOUS GOOD ARCHIVE")

    def test_matching_name_validation_accepts_current_directory_path(self):
        script = Path(package_skill.__file__).with_name("quick_validate.py")
        result = subprocess.run([sys.executable, "-B", str(script), "."], cwd=self.skill, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
