import asyncio
import importlib.util
import sys
import types
from pathlib import Path

import pytest


SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"


@pytest.mark.parametrize("fail_second", [False, True])
def test_agent_loop_returns_every_tool_result_in_one_message(monkeypatch, fail_second):
    anthropic = types.ModuleType("anthropic")
    anthropic.Anthropic = object
    connections = types.ModuleType("connections")
    connections.create_connection = lambda **kwargs: None
    monkeypatch.setitem(sys.modules, "anthropic", anthropic)
    monkeypatch.setitem(sys.modules, "connections", connections)

    spec = importlib.util.spec_from_file_location("mcp_evaluation", SCRIPTS / "evaluation.py")
    evaluation = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(evaluation)

    def tool_call(name, call_id):
        return types.SimpleNamespace(type="tool_use", name=name, id=call_id, input={})

    class Messages:
        calls = 0
        result_blocks = None

        def create(self, **kwargs):
            self.calls += 1
            if self.calls == 1:
                return types.SimpleNamespace(
                    stop_reason="tool_use",
                    content=[tool_call("first", "call-1"), tool_call("second", "call-2")],
                )
            self.result_blocks = kwargs["messages"][-1]["content"]
            assert [block["tool_use_id"] for block in self.result_blocks] == [
                "call-1",
                "call-2",
            ]
            return types.SimpleNamespace(
                stop_reason="end_turn",
                content=[types.SimpleNamespace(type="text", text="<response>done</response>")],
            )

    class Connection:
        calls = []

        async def call_tool(self, name, arguments):
            self.calls.append(name)
            if name == "second" and fail_second:
                raise RuntimeError("tool failed")
            return {"name": name}

    messages = Messages()
    connection = Connection()
    answer, metrics = asyncio.run(
        evaluation.agent_loop(
            types.SimpleNamespace(messages=messages), "test-model", "question", [], connection
        )
    )

    assert answer == "<response>done</response>"
    assert messages.calls == 2
    assert connection.calls == ["first", "second"]
    assert metrics["first"]["count"] == metrics["second"]["count"] == 1
    if fail_second:
        assert "Error executing tool second: tool failed" in messages.result_blocks[1][
            "content"
        ]
