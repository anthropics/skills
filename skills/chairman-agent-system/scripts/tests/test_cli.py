"""CLI behaviour, especially exit codes — they are the contract for CI use."""

from __future__ import annotations

import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from chairman.cli import main


class CliTestCase(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.db = str(Path(self._tmp.name) / "org.db")
        self.cli("init")

    def tearDown(self):
        self._tmp.cleanup()

    def cli(self, *args) -> tuple[int, str]:
        """Invoke the CLI in-process, returning ``(exit_code, output)``."""
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            code = main(["--db", self.db, *args])
        return code, buf.getvalue()

    def hire(self, name, level="operator", tools="finance",
             classification="confidential") -> str:
        self.cli("request", "--by", "chairman", "--name", name, "--level", level,
                 "--tools", tools, "--classification", classification,
                 "--purpose", "Reconcile the ledger", "--objective", "Daily close",
                 "--reporting", "Daily", "--risks", "Confidential ledger access")
        _, out = self.cli("requests", "--status", "pending")
        request_id = out.split()[0]
        self.cli("approve", request_id, "--by", "chairman")
        return request_id


class TestExitCodes(CliTestCase):
    def test_init_is_idempotent(self):
        code, out = self.cli("init")
        self.assertEqual(code, 0)
        self.assertIn("chairman", out)

    def test_permitted_check_exits_zero(self):
        self.hire("analyst")
        code, out = self.cli("check", "analyst", "--tool", "finance",
                             "--classification", "confidential")
        self.assertEqual(code, 0)
        self.assertIn("ALLOW", out)

    def test_denied_check_exits_one(self):
        """Exit 1 is what makes `check` usable as a CI gate."""
        self.hire("analyst")
        code, out = self.cli("check", "analyst", "--tool", "security",
                             "--classification", "public")
        self.assertEqual(code, 1)
        self.assertIn("DENY", out)

    def test_refused_command_exits_two(self):
        code, out = self.cli(
            "request", "--by", "chairman", "--name", "vague", "--level", "operator",
            "--tools", "finance", "--classification", "internal",
            "--purpose", "", "--reporting", "", "--risks", "",
        )
        self.assertEqual(code, 2)
        self.assertIn("REFUSED", out)

    def test_verify_exits_zero_on_intact_chain(self):
        code, out = self.cli("verify")
        self.assertEqual(code, 0)
        self.assertIn("intact", out)


class TestTaskLifecycle(CliTestCase):
    """Regression: update_task existed but no subcommand reached it, so a
    task could be created and never advanced, and `escalations` could never
    report anything."""

    def setUp(self):
        super().setUp()
        self.hire("analyst")
        self.cli("assign", "Ledger discrepancy", "--by", "chairman",
                 "--to", "analyst", "--tool", "finance",
                 "--classification", "confidential")
        _, out = self.cli("tasks")
        self.task_id = out.split()[0]

    def test_escalations_empty_exits_zero(self):
        code, out = self.cli("escalations")
        self.assertEqual(code, 0)
        self.assertIn("no open escalations", out)

    def test_raising_escalation_is_reachable_and_exits_one(self):
        code, _ = self.cli("task", self.task_id, "--by", "analyst",
                           "--escalation", "immediate", "--note", "Will not reconcile")
        self.assertEqual(code, 0)

        code, out = self.cli("escalations")
        self.assertEqual(code, 1)
        self.assertIn("IMMEDIATE", out)
        self.assertIn("Will not reconcile", out)

    def test_closing_the_task_clears_the_escalation(self):
        self.cli("task", self.task_id, "--by", "analyst", "--escalation", "immediate")
        self.cli("task", self.task_id, "--by", "analyst", "--status", "done")
        code, out = self.cli("escalations")
        self.assertEqual(code, 0)
        self.assertIn("no open escalations", out)

    def test_status_transitions_are_persisted(self):
        self.cli("task", self.task_id, "--by", "analyst", "--status", "in_progress")
        _, out = self.cli("tasks")
        self.assertIn("in_progress", out)


class TestOutputs(CliTestCase):
    def test_chart_shows_hierarchy_depth(self):
        self.hire("division-chair", level="executive", classification="restricted")
        _, out = self.cli("chart")
        lines = [l for l in out.splitlines() if l.strip()]
        self.assertTrue(lines[0].startswith("chairman"))
        self.assertTrue(any(l.startswith("  division-chair") for l in lines))

    def test_terminate_reports_the_cascade(self):
        self.hire("division-chair", level="executive", classification="restricted")
        code, out = self.cli("terminate", "division-chair", "--by", "chairman",
                             "--reason", "restructure")
        self.assertEqual(code, 0)
        self.assertIn("division-chair", out)

    def test_log_renders_entries(self):
        code, out = self.cli("log", "--limit", "2")
        self.assertEqual(code, 0)
        self.assertIn("install_chairman", out)

    def test_unknown_agent_is_refused_not_crashed(self):
        code, out = self.cli("check", "ghost", "--tool", "finance",
                             "--classification", "public")
        self.assertEqual(code, 2)
        self.assertIn("REFUSED", out)


if __name__ == "__main__":
    unittest.main()
