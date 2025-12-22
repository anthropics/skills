#!/usr/bin/env python3
"""Tests for validate.py"""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


class TestValidate(unittest.TestCase):

    def test_xlsx_not_implemented(self):
        """Test that .xlsx files get a clear 'not implemented' message."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Create dummy xlsx file and unpacked dir
            xlsx_file = Path(tmpdir) / "test.xlsx"
            xlsx_file.touch()
            unpacked_dir = Path(tmpdir) / "unpacked"
            unpacked_dir.mkdir()

            # Run validate.py
            result = subprocess.run(
                [sys.executable, "validate.py", str(unpacked_dir), "--original", str(xlsx_file)],
                capture_output=True,
                text=True,
                cwd=Path(__file__).parent,
            )

            self.assertEqual(result.returncode, 1)
            self.assertIn("XLSX validation is not yet implemented", result.stdout)


if __name__ == "__main__":
    unittest.main()
