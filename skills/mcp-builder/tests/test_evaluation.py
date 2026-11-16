"""Regression tests for evaluation.py — issue #2201.

Stubbed Anthropic client only: no network calls, no API key.
Run with the project venv: pytest skills/mcp-builder/tests/test_evaluation.py
"""

import asyncio
import sys
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import AsyncMock, MagicMock

import pytest

# evaluation.py lives in skills/mcp-builder/scripts/ next to connections.py.
# connections.py imports an mcp client symbol that newer mcp releases no
# longer export, so stub it out: these tests only exercise evaluation.py.
sys.modules.setdefault("connections", MagicMock())

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import evaluation  # noqa: E402


def _text_block(text):
    return SimpleNamespace(type="text", text=text)


def _tool_use_block(block_id="toolu_1", name="get_data", tool_input=None):
    return SimpleNamespace(
        type="tool_use", id=block_id, name=name,
        input=tool_input if tool_input is not None else {},
    )


def _response(stop_reason, content):
    return SimpleNamespace(stop_reason=stop_reason, content=content)


def _client(*responses):
    client = MagicMock()
    client.messages.create.side_effect = list(responses)
    return client


def _connection():
    connection = MagicMock()
    connection.call_tool = AsyncMock(return_value={"result": "42"})
    return connection


def _run(coro):
    return asyncio.run(coro)


def test_max_tokens_is_incomplete_not_scored():
    """A max_tokens turn must not be treated as a final answer."""
    client = _client(_response("max_tokens", [_text_block("<response>Almost...")]))
    text, _metrics = _run(evaluation.agent_loop(
        client, "test-model", "What is 6x7?", [], _connection()))
    assert text is None

    result = _run(evaluation.evaluate_single_task(
        _client(_response("max_tokens", [_text_block("<response>Almost...")])),
        "test-model",
        {"question": "What is 6x7?", "answer": "42"},
        [], _connection(), 0))
    assert result["score"] == 0
    assert result["status"] == "incomplete"
    assert result["actual"] is None


def test_refusal_without_text_does_not_crash():
    """A refusal turn with no text blocks must not crash extract_xml_content."""
    client = _client(_response("refusal", []))
    text, _metrics = _run(evaluation.agent_loop(
        client, "test-model", "What is 6x7?", [], _connection()))
    assert text is None

    result = _run(evaluation.evaluate_single_task(
        _client(_response("refusal", [])),
        "test-model",
        {"question": "What is 6x7?", "answer": "42"},
        [], _connection(), 0))
    assert result["score"] == 0
    assert result["status"] == "incomplete"
    assert result["actual"] is None


def test_response_tag_in_later_text_block_is_scored():
    """A <response> tag in a later text block must be found, not missed."""
    content = [
        _text_block("Thinking..."),
        _text_block("<response>correct_answer</response>"),
    ]
    client = _client(_response("end_turn", content))
    text, _metrics = _run(evaluation.agent_loop(
        client, "test-model", "What is it?", [], _connection()))
    assert text is not None
    assert "<response>correct_answer</response>" in text

    result = _run(evaluation.evaluate_single_task(
        _client(_response("end_turn", content)),
        "test-model",
        {"question": "What is it?", "answer": "correct_answer"},
        [], _connection(), 0))
    assert result["score"] == 1
    assert result["status"] == "complete"


def test_end_turn_single_block_happy_path():
    """Normal end_turn answer still scores 1 and is complete."""
    content = [_text_block("<response>correct_answer</response>")]
    result = _run(evaluation.evaluate_single_task(
        _client(_response("end_turn", content)),
        "test-model",
        {"question": "What is it?", "answer": "correct_answer"},
        [], _connection(), 0))
    assert result["score"] == 1
    assert result["status"] == "complete"
    assert result["actual"] == "correct_answer"


def test_tool_use_still_answered_then_scores():
    """A single tool_use turn is still answered and the final answer scored."""
    tool_turn = _response("tool_use", [_tool_use_block()])
    final_turn = _response(
        "end_turn", [_text_block("<response>42</response>")])
    connection = _connection()
    result = _run(evaluation.evaluate_single_task(
        _client(tool_turn, final_turn),
        "test-model",
        {"question": "What is 6x7?", "answer": "42"},
        [], connection, 0))
    connection.call_tool.assert_awaited_once()
    assert result["score"] == 1
    assert result["status"] == "complete"
    assert result["num_tool_calls"] == 1


def test_pause_turn_continues_loop():
    """A pause_turn turn continues the loop instead of ending the run."""
    paused = _response("pause_turn", [_text_block("Pausing...")])
    final_turn = _response(
        "end_turn", [_text_block("<response>42</response>")])
    result = _run(evaluation.evaluate_single_task(
        _client(paused, final_turn),
        "test-model",
        {"question": "What is 6x7?", "answer": "42"},
        [], _connection(), 0))
    assert result["score"] == 1
    assert result["status"] == "complete"


def test_max_tokens_records_incomplete_reason():
    """A max_tokens run records incomplete_reason 'max_tokens'."""
    result = _run(evaluation.evaluate_single_task(
        _client(_response("max_tokens", [_text_block("<response>Almost...")])),
        "test-model",
        {"question": "What is 6x7?", "answer": "42"},
        [], _connection(), 0))
    assert result["status"] == "incomplete"
    assert result["incomplete_reason"] == "max_tokens"


def test_refusal_records_incomplete_reason():
    """A refusal run records incomplete_reason 'refusal'."""
    result = _run(evaluation.evaluate_single_task(
        _client(_response("refusal", [])),
        "test-model",
        {"question": "What is 6x7?", "answer": "42"},
        [], _connection(), 0))
    assert result["status"] == "incomplete"
    assert result["incomplete_reason"] == "refusal"


def test_unknown_stop_reason_is_incomplete_not_scored():
    """An unknown stop_reason must not be graded as a final answer."""
    client = _client(_response(
        "mystery_stop", [_text_block("<response>42</response>")]))
    text, _metrics = _run(evaluation.agent_loop(
        client, "test-model", "What is 6x7?", [], _connection()))
    assert text is None

    result = _run(evaluation.evaluate_single_task(
        _client(_response(
            "mystery_stop", [_text_block("<response>42</response>")])),
        "test-model",
        {"question": "What is 6x7?", "answer": "42"},
        [], _connection(), 0))
    assert result["score"] == 0
    assert result["status"] == "incomplete"
    assert result["incomplete_reason"] == "mystery_stop"
    assert result["actual"] is None


def test_max_tokens_uses_raised_limit():
    """Both messages.create calls request max_tokens=16384."""
    client = _client(
        _response("tool_use", [_tool_use_block()]),
        _response("end_turn", [_text_block("<response>42</response>")]),
    )
    _run(evaluation.agent_loop(
        client, "test-model", "What is 6x7?", [], _connection()))
    for call in client.messages.create.call_args_list:
        assert call.kwargs["max_tokens"] == 16384
