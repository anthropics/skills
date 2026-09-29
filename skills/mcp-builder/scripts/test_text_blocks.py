"""Regression tests for final answers split across assistant text blocks."""

import asyncio
import unittest
from types import SimpleNamespace

from evaluation import evaluate_single_task


class Messages:
    def __init__(self):
        self.calls = 0

    def create(self, **kwargs):
        self.calls += 1
        if self.calls == 1:
            return SimpleNamespace(
                stop_reason="tool_use",
                content=[SimpleNamespace(type="tool_use", name="lookup", id="call-1", input={})],
            )
        return SimpleNamespace(
            stop_reason="end_turn",
            content=[
                SimpleNamespace(type="text", text="<summary>Used the lookup tool.</summary>"),
                SimpleNamespace(type="text", text="<feedback>Worked.</feedback><response>42</response>"),
            ],
        )


class Connection:
    async def call_tool(self, name, arguments):
        return {"answer": 42}


class TextBlockTests(unittest.TestCase):
    def test_answer_in_later_text_block_is_scored(self):
        client = SimpleNamespace(messages=Messages())

        result = asyncio.run(evaluate_single_task(
            client, "test-model", {"question": "What is the answer?", "answer": "42"},
            [], Connection(), 0,
        ))

        self.assertEqual(result["actual"], "42")
        self.assertEqual(result["score"], 1)
        self.assertEqual(result["num_tool_calls"], 1)
        self.assertEqual(result["feedback"], "Worked.")


if __name__ == "__main__":
    unittest.main()
