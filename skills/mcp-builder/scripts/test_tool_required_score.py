"""Regression tests for evaluating tool-dependent questions."""

import asyncio
import unittest
from types import SimpleNamespace

from evaluation import evaluate_single_task


ANSWER = SimpleNamespace(
    stop_reason="end_turn",
    content=[SimpleNamespace(type="text", text="<response>42</response>")],
)


class Messages:
    def __init__(self, responses):
        self.responses = list(responses)

    def create(self, **kwargs):
        return self.responses.pop(0)


class Connection:
    async def call_tool(self, name, arguments):
        return {"answer": 42}


class ToolRequiredScoreTests(unittest.TestCase):
    def evaluate(self, responses):
        client = SimpleNamespace(messages=Messages(responses))
        return asyncio.run(evaluate_single_task(
            client, "test-model", {"question": "Look up the answer", "answer": "42"},
            [], Connection(), 0,
        ))

    def test_correct_guess_without_a_tool_does_not_pass(self):
        result = self.evaluate([ANSWER])

        self.assertEqual(result["actual"], "42")
        self.assertEqual(result["num_tool_calls"], 0)
        self.assertEqual(result["score"], 0)

    def test_correct_answer_after_a_tool_call_passes(self):
        call = SimpleNamespace(
            stop_reason="tool_use",
            content=[SimpleNamespace(type="tool_use", name="lookup", id="call-1", input={})],
        )

        result = self.evaluate([call, ANSWER])

        self.assertEqual(result["num_tool_calls"], 1)
        self.assertEqual(result["score"], 1)


if __name__ == "__main__":
    unittest.main()
