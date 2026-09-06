import importlib.util
from pathlib import Path


MODULE_PATH = Path(__file__).with_name("run_eval.py")
SPEC = importlib.util.spec_from_file_location("run_eval", MODULE_PATH)
assert SPEC and SPEC.loader
run_eval = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(run_eval)


def stream_event(event_type, **kwargs):
    return {"type": "stream_event", "event": {"type": event_type, **kwargs}}


def test_unrelated_tool_before_skill_does_not_end_evaluation():
    clean_name = "candidate-skill-test01"
    state = {"pending_tool_name": None, "accumulated_json": ""}

    assert (
        run_eval._handle_stream_event(
            stream_event(
                "content_block_start",
                content_block={"type": "tool_use", "name": "Bash"},
            ),
            clean_name,
            state,
        )
        is None
    )
    assert (
        run_eval._handle_stream_event(
            stream_event(
                "content_block_start",
                content_block={"type": "tool_use", "name": "Skill"},
            ),
            clean_name,
            state,
        )
        is None
    )
    assert (
        run_eval._handle_stream_event(
            stream_event(
                "content_block_delta",
                delta={
                    "type": "input_json_delta",
                    "partial_json": '{"skill":"candidate-skill-test01"}',
                },
            ),
            clean_name,
            state,
        )
        is True
    )


def test_finished_unrelated_block_does_not_end_evaluation():
    clean_name = "candidate-skill-test01"
    state = {"pending_tool_name": None, "accumulated_json": ""}
    assert (
        run_eval._handle_stream_event(
            stream_event(
                "content_block_start",
                content_block={"type": "tool_use", "name": "Read"},
            ),
            clean_name,
            state,
        )
        is None
    )
    assert (
        run_eval._handle_stream_event(
            stream_event("content_block_stop"), clean_name, state
        )
        is None
    )
    assert (
        run_eval._handle_stream_event(
            stream_event(
                "content_block_start",
                content_block={"type": "tool_use", "name": "Skill"},
            ),
            clean_name,
            state,
        )
        is None
    )
    assert (
        run_eval._handle_stream_event(
            stream_event(
                "content_block_delta",
                delta={
                    "type": "input_json_delta",
                    "partial_json": '{"skill":"candidate-skill-test01"}',
                },
            ),
            clean_name,
            state,
        )
        is True
    )


def test_non_streaming_message_checks_all_tool_uses():
    message = {
        "content": [
            {"type": "tool_use", "name": "Bash", "input": {"command": "pwd"}},
            {
                "type": "tool_use",
                "name": "Skill",
                "input": {"skill": "candidate-skill-test01"},
            },
        ]
    }
    assert (
        run_eval._assistant_message_triggered(message, "candidate-skill-test01") is True
    )
