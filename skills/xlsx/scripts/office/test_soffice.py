"""Tests for office.soffice.find_soffice / run_soffice.

No LibreOffice needed: the install locations are faked with mocks.
Run from skills/xlsx/scripts:  python3 -m unittest office.test_soffice -v
"""

import os
import sys
import unittest
from unittest import mock

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from office.soffice import find_soffice, run_soffice


class FindSofficeTest(unittest.TestCase):
    def test_path_hit_wins(self):
        with mock.patch("office.soffice.shutil.which", return_value="/usr/bin/soffice"):
            self.assertEqual(find_soffice(), "/usr/bin/soffice")

    def test_macos_app_bundle_found_when_not_on_path(self):
        app = "/Applications/LibreOffice.app/Contents/MacOS/soffice"
        with (
            mock.patch("office.soffice.shutil.which", return_value=None),
            mock.patch.object(sys, "platform", "darwin"),
            mock.patch("office.soffice.os.path.isfile", side_effect=lambda p: p == app),
            mock.patch("office.soffice.os.access", return_value=True),
        ):
            self.assertEqual(find_soffice(), app)

    def test_macos_app_bundle_ignored_when_not_executable(self):
        with (
            mock.patch("office.soffice.shutil.which", return_value=None),
            mock.patch.object(sys, "platform", "darwin"),
            mock.patch("office.soffice.os.path.isfile", return_value=True),
            mock.patch("office.soffice.os.access", return_value=False),
        ):
            self.assertIsNone(find_soffice())

    def test_windows_program_files_found_when_not_on_path(self):
        exe = r"C:\Program Files\LibreOffice\program\soffice.exe"
        with (
            mock.patch("office.soffice.shutil.which", return_value=None),
            mock.patch.object(sys, "platform", "win32"),
            mock.patch.dict(os.environ, {"ProgramFiles": r"C:\Program Files"}),
            mock.patch("office.soffice.os.path.isfile", side_effect=lambda p: p == exe),
            mock.patch("office.soffice.os.access", return_value=True),
        ):
            self.assertEqual(find_soffice(), exe)

    def test_nothing_anywhere_returns_none(self):
        with (
            mock.patch("office.soffice.shutil.which", return_value=None),
            mock.patch("office.soffice.os.path.isfile", return_value=False),
        ):
            self.assertIsNone(find_soffice())


class RunSofficeTest(unittest.TestCase):
    def test_missing_soffice_raises_file_not_found(self):
        with (
            mock.patch("office.soffice.find_soffice", return_value=None),
            mock.patch("office.soffice.subprocess.run") as run,
        ):
            with self.assertRaises(FileNotFoundError) as ctx:
                run_soffice(["--version"])
            self.assertIn("LibreOffice", str(ctx.exception))
            run.assert_not_called()

    def test_found_soffice_is_invoked(self):
        fake = mock.Mock(returncode=0)
        with (
            mock.patch("office.soffice.find_soffice", return_value="/opt/lo/soffice"),
            mock.patch("office.soffice.subprocess.run", return_value=fake) as run,
        ):
            self.assertIs(run_soffice(["--version"]), fake)
            self.assertEqual(run.call_args[0][0][0], "/opt/lo/soffice")


if __name__ == "__main__":
    unittest.main()
