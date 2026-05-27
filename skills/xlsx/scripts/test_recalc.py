import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import recalc


class RecalcTests(unittest.TestCase):
    def test_timeout_does_not_scan_stale_formula_cache(self) -> None:
        with tempfile.NamedTemporaryFile(suffix=".xlsx") as tmp:
            workbook_path = Path(tmp.name)
            completed = subprocess.CompletedProcess(
                args=["timeout", "1", "soffice"],
                returncode=124,
                stdout="",
                stderr="",
            )

            with mock.patch.object(
                recalc, "setup_libreoffice_macro", return_value=True
            ), mock.patch.object(
                recalc, "get_soffice_env", return_value={}
            ), mock.patch.object(
                recalc.subprocess, "run", return_value=completed
            ), mock.patch.object(
                recalc, "load_workbook"
            ) as load_workbook:
                result = recalc.recalc(workbook_path, timeout=1)

        self.assertEqual(result["status"], "recalc_timeout")
        self.assertEqual(result["timeout_seconds"], 1)
        load_workbook.assert_not_called()


if __name__ == "__main__":
    unittest.main()
