"""Description length recovery regressions; all model calls are local mocks."""

import contextlib
import copy
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import improve_description


class ImproveDescriptionLengthTests(unittest.TestCase):
    def setUp(self):
        self.eval_results = {"results": [], "summary": {"passed": 0, "failed": 1, "total": 1}}
        self.history = [{"description": "Earlier valid description."}]

    def improve(self, **kwargs):
        return improve_description.improve_description(
            skill_name="example",
            skill_content="Existing skill body.",
            current_description="Existing valid description.",
            eval_results=self.eval_results,
            history=self.history,
            model="fake-model",
            **kwargs,
        )

    def test_valid_description_including_limit_needs_no_rewrite(self):
        for length in (1, 1024):
            with self.subTest(length=length):
                expected = "x" * length
                with patch.object(improve_description, "_call_claude", return_value=f"<new_description>{expected}</new_description>") as call:
                    self.assertEqual(self.improve(), expected)
                self.assertEqual(call.call_count, 1)

    def test_one_rewrite_can_return_exactly_the_limit(self):
        responses = ["<new_description>" + "x" * 1025 + "</new_description>",
                     "<new_description>" + "y" * 1024 + "</new_description>"]
        with patch.object(improve_description, "_call_claude", side_effect=responses) as call:
            self.assertEqual(self.improve(), "y" * 1024)
        self.assertEqual(call.call_count, 2)

    def test_failed_rewrite_raises_and_preserves_attempt_log_and_inputs(self):
        responses = ["<new_description>" + "x" * 1100 + "</new_description>",
                     "<new_description>" + "y" * 1100 + "</new_description>"]
        before = copy.deepcopy((self.eval_results, self.history))
        with tempfile.TemporaryDirectory() as directory:
            logs = Path(directory)
            with patch.object(improve_description, "_call_claude", side_effect=responses) as call:
                with self.assertRaisesRegex(ValueError, "1024"):
                    self.improve(log_dir=logs, iteration=2)
            self.assertEqual(call.call_count, 2)
            transcript = json.loads((logs / "improve_iter_2.json").read_text())
            self.assertEqual(transcript["response"], responses[0])
            self.assertEqual(transcript["rewrite_response"], responses[1])
            self.assertEqual(transcript["rewrite_char_count"], 1100)
        self.assertEqual((self.eval_results, self.history), before)

    def test_cli_failure_emits_no_result_and_preserves_existing_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            skill = root / "SKILL.md"
            skill.write_text("---\nname: example\ndescription: Existing description.\n---\nExisting body.\n")
            evaluation = root / "eval.json"
            evaluation.write_text(json.dumps(dict(self.eval_results, description="Existing description.")))
            history = root / "history.json"
            history.write_text(json.dumps(self.history))
            before = {path: path.read_bytes() for path in (skill, evaluation, history)}
            argv = ["improve_description", "--eval-results", str(evaluation),
                    "--skill-path", str(root), "--history", str(history), "--model", "fake-model"]
            responses = ["x" * 1100, "y" * 1100]
            output = io.StringIO()
            with patch.object(improve_description.sys, "argv", argv), \
                    patch.object(improve_description, "_call_claude", side_effect=responses) as call, \
                    contextlib.redirect_stdout(output):
                with self.assertRaisesRegex(ValueError, "1024"):
                    improve_description.main()
            self.assertEqual(call.call_count, 2)
            self.assertEqual(output.getvalue(), "")
            self.assertEqual({path: path.read_bytes() for path in before}, before)

    def test_model_call_failure_does_not_add_retries(self):
        with patch.object(improve_description, "_call_claude", side_effect=RuntimeError("fake CLI failure")) as call:
            with self.assertRaisesRegex(RuntimeError, "fake CLI failure"):
                self.improve()
        self.assertEqual(call.call_count, 1)


if __name__ == "__main__":
    unittest.main()
