"""Regression tests for final answers split across assistant text blocks."""

import asyncio
import unittest
from types import SimpleNamespace

from evaluation import evaluate_single_task


class Messages:
    def create(self, **kwargs):
        return SimpleNamespace(
            stop_reason="end_turn",
            content=[
                SimpleNamespace(type="text", text="<summary>Used the lookup tool.</summary>"),
                SimpleNamespace(type="text", text="<feedback>Worked.</feedback><response>42</response>"),
            ],
        )


class TextBlockTests(unittest.TestCase):
    def test_answer_in_later_text_block_is_scored(self):
        client = SimpleNamespace(messages=Messages())

        result = asyncio.run(evaluate_single_task(
            client, "test-model", {"question": "What is the answer?", "answer": "42"},
            [], None, 0,
        ))

        self.assertEqual(result["actual"], "42")
        self.assertEqual(result["score"], 1)
        self.assertEqual(result["feedback"], "Worked.")


if __name__ == "__main__":
    unittest.main()
