"""Failure paths must never become valid trigger measurements."""

import json
import os
import sys
import tempfile
import time
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest import mock

from scripts.run_eval import _raise_if_shadowed, run_eval, run_single_query
from scripts.tests.test_stream_probe import FakeProcess


class EvalFailureTests(unittest.TestCase):
    def probe(self, output, stderr=b""):
        process = FakeProcess(output, stderr)
        with mock.patch("scripts.run_eval.subprocess.Popen", return_value=process), mock.patch(
            "scripts.run_eval._stop_process_tree"
        ):
            return run_single_query("query", "pdf", 2, ".", claude_cli="fake")

    def test_error_result_is_not_a_negative_measurement(self):
        for subtype in ("error_during_execution", "error_max_turns"):
            with self.subTest(subtype=subtype):
                event = {"type": "result", "subtype": subtype,
                         "is_error": True, "errors": ["failure detail"]}
                with self.assertRaisesRegex(RuntimeError, "failure detail"):
                    self.probe((json.dumps(event) + "\n").encode())

    def test_truncated_stream_is_an_error_even_with_exit_zero(self):
        with self.assertRaisesRegex(RuntimeError, "without a result.*diagnostic"):
            self.probe(b"garbage\n", b"diagnostic")

    def test_success_without_trigger_remains_false(self):
        self.assertFalse(self.probe(b'{"type":"result","subtype":"success","is_error":false}\n'))

    def test_failed_negative_query_aborts_batch_and_cleans_artifact(self):
        with tempfile.TemporaryDirectory() as tmp:
            project = Path(tmp) / "probe"
            project.mkdir()
            with mock.patch("scripts.run_eval.resolve_claude_cli", return_value="fake"), mock.patch(
                "scripts.run_eval.create_eval_project", return_value=project
            ), mock.patch("scripts.run_eval.ProcessPoolExecutor", ThreadPoolExecutor), mock.patch(
                "scripts.run_eval.run_single_query", side_effect=RuntimeError("auth failed")
            ), self.assertRaisesRegex(RuntimeError, "Evaluation aborted.*auth failed"):
                run_eval([{"query": "negative", "should_trigger": False}], "pdf", "desc", 1, 1)
            self.assertFalse(project.exists())

    def test_custom_config_collision_is_detected(self):
        with tempfile.TemporaryDirectory() as tmp:
            config = Path(tmp) / "custom"
            (config / "skills" / "pdf").mkdir(parents=True)
            with mock.patch.dict(os.environ, {"CLAUDE_CONFIG_DIR": str(config)}), self.assertRaisesRegex(
                RuntimeError, "would shadow"
            ):
                _raise_if_shadowed("pdf")

    @unittest.skipUnless(os.name == "nt", "Windows npm shim regression")
    def test_timeout_kills_real_cmd_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            marker = root / "survived"
            child = root / "child.py"
            child.write_text(
                "import time\nfrom pathlib import Path\n"
                "print('ready', flush=True)\ntime.sleep(2)\n"
                f"Path({str(marker)!r}).write_text('alive')\n",
                encoding="utf-8",
            )
            shim = root / "claude.cmd"
            shim.write_text(f'@echo off\n"{sys.executable}" "{child}"\n')
            with self.assertRaisesRegex(RuntimeError, "timed out"):
                run_single_query("query", "pdf", 0.5, str(root), claude_cli=str(shim))
            time.sleep(2.2)
            self.assertFalse(marker.exists(), "The shim child survived probe cleanup")


if __name__ == "__main__":
    unittest.main()
