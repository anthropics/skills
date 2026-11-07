import io
import sys
import unittest
from pathlib import Path
from unittest.mock import patch


SKILL_CREATOR_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SKILL_CREATOR_DIR))

from scripts import run_loop  # noqa: E402


class OpenReportTests(unittest.TestCase):
    def test_returns_true_when_browser_opens_report(self) -> None:
        report = SKILL_CREATOR_DIR / "report.html"
        with patch("scripts.run_loop.webbrowser.open", return_value=True) as open_report:
            self.assertTrue(run_loop._open_report(report))  # noqa: SLF001

        open_report.assert_called_once_with(report.resolve().as_uri())

    def test_returns_false_and_continues_when_browser_is_unavailable(self) -> None:
        report = SKILL_CREATOR_DIR / "report.html"
        stderr = io.StringIO()
        with (
            patch("scripts.run_loop.webbrowser.open", side_effect=run_loop.webbrowser.Error("no display")),
            patch("sys.stderr", stderr),
        ):
            self.assertFalse(run_loop._open_report(report))  # noqa: SLF001

        self.assertIn("Could not open report in a browser", stderr.getvalue())

    def test_reports_a_false_browser_result_without_failing(self) -> None:
        report = SKILL_CREATOR_DIR / "report.html"
        stderr = io.StringIO()
        with (
            patch("scripts.run_loop.webbrowser.open", return_value=False),
            patch("sys.stderr", stderr),
        ):
            self.assertFalse(run_loop._open_report(report))  # noqa: SLF001

        self.assertIn("No browser was available", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
