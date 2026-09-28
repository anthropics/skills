"""Regression tests for failures that must not count as negative passes."""

import io
import tempfile
import unittest
from concurrent.futures import Future
from pathlib import Path
from unittest.mock import patch

from scripts import run_eval, run_loop
from scripts.generate_report import generate_html


class FailedProcess:
    stdout = io.BytesIO()
    returncode = 2

    def poll(self):
        return self.returncode


class ErrorResultProcess:
    def __init__(self):
        self.stdout = self
        self.returncode = None

    def poll(self):
        return self.returncode

    def fileno(self):
        return 0

    def kill(self):
        self.returncode = -9

    def wait(self):
        return self.returncode


class FailedExecutor:
    def __init__(self, max_workers):
        pass

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        pass

    def submit(self, *args):
        future = Future()
        future.set_exception(RuntimeError("Claude failed"))
        return future


class EvalErrorTests(unittest.TestCase):
    def test_claude_exit_failure_is_not_a_nontrigger(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            with patch.object(run_eval.subprocess, "Popen", return_value=FailedProcess()):
                with self.assertRaisesRegex(RuntimeError, "claude -p exited 2"):
                    run_eval.run_single_query("query", "skill", "description", 1, tmpdir)

    def test_claude_error_result_is_not_a_nontrigger(self):
        process = ErrorResultProcess()
        event = b'{"type":"result","is_error":true,"subtype":"error_during_execution"}\n'
        with tempfile.TemporaryDirectory() as tmpdir:
            with patch.object(run_eval.subprocess, "Popen", return_value=process), \
                    patch.object(run_eval.select, "select", return_value=([process.stdout], [], [])), \
                    patch.object(run_eval.os, "read", return_value=event):
                with self.assertRaisesRegex(RuntimeError, "claude -p reported an error"):
                    run_eval.run_single_query("query", "skill", "description", 1, tmpdir)

    def test_worker_failure_cannot_pass_a_negative_query(self):
        eval_set = [{"query": "irrelevant query", "should_trigger": False}]

        with patch.object(run_eval, "ProcessPoolExecutor", FailedExecutor):
            output = run_eval.run_eval(eval_set, "skill", "description", 1, 1, Path.cwd())

        self.assertFalse(output["results"][0]["pass"])
        self.assertEqual(output["results"][0]["errors"], 1)

    def test_report_does_not_count_a_failed_negative_trial_as_correct(self):
        failed_result = {
            "query": "irrelevant query", "should_trigger": False,
            "triggers": 0, "runs": 1, "errors": 1, "pass": False,
        }
        data = {"history": [{
            "iteration": 1, "description": "description",
            "train_passed": 0, "train_total": 1,
            "train_results": [failed_result],
        }]}

        report = generate_html(data)

        self.assertIn('<span class="score score-bad">0/1</span>', report)

    def test_verbose_accuracy_does_not_count_failed_negative_trial(self):
        failed_result = {
            "query": "irrelevant query", "should_trigger": False,
            "triggers": 0, "runs": 1, "errors": 1, "pass": False,
        }
        eval_output = {"results": [failed_result], "summary": {"passed": 0, "failed": 1, "total": 1}}
        stderr = io.StringIO()
        with patch.object(run_loop, "find_project_root", return_value=Path.cwd()), \
                patch.object(run_loop, "parse_skill_md", return_value=("skill", "description", "content")), \
                patch.object(run_loop, "run_eval", return_value=eval_output), \
                patch.object(run_loop.sys, "stderr", stderr):
            run_loop.run_loop(
                eval_set=[{"query": "irrelevant query", "should_trigger": False}],
                skill_path=Path.cwd(), description_override=None,
                num_workers=1, timeout=1, max_iterations=1,
                runs_per_query=1, trigger_threshold=0.5, holdout=0,
                model="test", verbose=True,
            )

        self.assertIn("Train: 0/1 correct", stderr.getvalue())
        self.assertIn("accuracy=0%", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
