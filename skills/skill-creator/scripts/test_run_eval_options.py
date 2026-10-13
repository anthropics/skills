"""Regression tests for eval options that can produce false success."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from scripts.run_eval import run_eval


class RunEvalOptionTests(unittest.TestCase):
    def test_zero_runs_cannot_report_an_empty_success(self):
        eval_set = [{"query": "use the skill", "should_trigger": True}]

        with self.assertRaisesRegex(ValueError, "runs_per_query must be positive"):
            run_eval(eval_set, "example", "description", 1, 30, Path.cwd(), runs_per_query=0)

    def test_negative_runs_are_rejected(self):
        eval_set = [{"query": "use the skill", "should_trigger": True}]

        with self.assertRaisesRegex(ValueError, "runs_per_query must be positive"):
            run_eval(eval_set, "example", "description", 1, 30, Path.cwd(), runs_per_query=-2)


    def test_cli_validation_error_has_no_traceback(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / "SKILL.md").write_text("---\nname: synthetic\ndescription: synthetic\n---\ncontent\n")
            eval_file = path / "eval.json"
            eval_file.write_text(json.dumps([{"query": "synthetic", "should_trigger": True}]))
            root = Path(__file__).resolve().parent.parent
            for module in ("run_eval", "run_loop"):
                with self.subTest(module=module):
                    args = [sys.executable, "-m", "scripts." + module,
                            "--eval-set", str(eval_file), "--skill-path", str(path)] + ["--runs-per-query", "0"]
                    if module == "run_loop":
                        args += ["--model", "unused", "--report", "none", "--holdout", "0"]
                    result = subprocess.run(args, cwd=root, capture_output=True, text=True)
                    self.assertEqual(result.returncode, 1)
                    self.assertIn("Error: runs_per_query must be positive", result.stderr)
                    self.assertNotIn("Traceback", result.stderr)
                    self.assertEqual(result.stdout, "")

if __name__ == "__main__":
    unittest.main()
