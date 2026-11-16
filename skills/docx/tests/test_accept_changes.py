import importlib
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

SCRIPT_DIR = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPT_DIR))
accept_changes = importlib.import_module("accept_changes")


class LibreOfficeProfileTests(unittest.TestCase):
    def test_profile_uses_the_system_temp_directory(self):
        self.assertEqual(
            accept_changes.LIBREOFFICE_PROFILE,
            Path(tempfile.gettempdir()) / "libreoffice_docx_profile",
        )

    def test_profile_uri_is_used_for_setup_and_processing(self):
        with tempfile.TemporaryDirectory(prefix="libreoffice profile ") as temp_dir:
            profile = Path(temp_dir) / "profile"
            macro_dir = profile / "user" / "basic" / "Standard"
            input_path = Path(temp_dir) / "input.docx"
            output_path = Path(temp_dir) / "output.docx"
            input_path.write_bytes(b"docx fixture")
            completed = subprocess.CompletedProcess([], 0, stdout="", stderr="")

            with patch.object(accept_changes, "LIBREOFFICE_PROFILE", profile), \
                    patch.object(accept_changes, "MACRO_DIR", macro_dir), \
                    patch.object(accept_changes, "get_soffice_env", return_value={}), \
                    patch.object(
                        accept_changes.subprocess,
                        "run",
                        side_effect=[completed, completed],
                    ) as run:
                _, message = accept_changes.accept_changes(
                    str(input_path), str(output_path)
                )

            self.assertIn("Successfully", message)
            self.assertTrue(output_path.exists())
            expected_arg = f"-env:UserInstallation={profile.as_uri()}"
            self.assertEqual(
                [call.args[0][2] for call in run.call_args_list],
                [expected_arg, expected_arg],
            )

    def test_setup_timeout_returns_error_without_copying_output(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            profile = Path(temp_dir) / "profile"
            macro_dir = profile / "user" / "basic" / "Standard"
            input_path = Path(temp_dir) / "input.docx"
            output_path = Path(temp_dir) / "output.docx"
            input_path.write_bytes(b"docx fixture")

            with patch.object(accept_changes, "LIBREOFFICE_PROFILE", profile), \
                    patch.object(accept_changes, "MACRO_DIR", macro_dir), \
                    patch.object(accept_changes, "get_soffice_env", return_value={}), \
                    patch.object(
                        accept_changes.subprocess,
                        "run",
                        side_effect=subprocess.TimeoutExpired("soffice", timeout=10),
                    ):
                _, message = accept_changes.accept_changes(
                    str(input_path), str(output_path)
                )

            self.assertIn("Error: Failed to setup", message)
            self.assertFalse(output_path.exists())


if __name__ == "__main__":
    unittest.main()
