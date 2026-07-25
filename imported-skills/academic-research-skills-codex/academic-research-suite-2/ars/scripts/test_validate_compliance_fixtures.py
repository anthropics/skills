"""Unit tests for validate_compliance_fixtures.py."""
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "validate_compliance_fixtures.py"
REAL_FIXTURES = Path(__file__).resolve().parent.parent / "examples" / "compliance"


class TestValidateComplianceFixtures(unittest.TestCase):
    def test_real_fixtures_all_pass(self) -> None:
        result = run_script(SCRIPT, str(REAL_FIXTURES))
        self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)
        self.assertIn("OK", result.stdout)
        self.assertNotIn("FAIL", result.stdout)
        self.assertNotIn("no fixture", result.stderr.lower())

    def test_empty_dir_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            result = run_script(SCRIPT, tmp)
            self.assertEqual(result.returncode, 1)
            self.assertIn("no fixture", result.stderr.lower())

    def test_invalid_fixture_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            bad = Path(tmp) / "fixture_invalid.yaml"
            bad.write_text("mode: not_a_valid_mode\n", encoding="utf-8")
            result = run_script(SCRIPT, tmp)
            self.assertEqual(result.returncode, 1)
            self.assertIn("FAIL", result.stdout)


if __name__ == "__main__":
    unittest.main()
