"""Verdict tests for ``scripts/trigger_stream.py``.

Characterization tests for the stream-json detection that moved out of
``run_eval.run_single_query``: the verdict must be identical to the old inline
loop for early stream events and for the full assistant message fallback.
"""

from scripts.trigger_stream import TriggerDetector

PROBE = "demo-skill-skill-0badcafe"


def stream(se_type: str, **fields) -> dict:
    return {"type": "stream_event", "event": {"type": se_type, **fields}}


def tool_start(name: str) -> dict:
    return stream("content_block_start", content_block={"type": "tool_use", "name": name})


def input_delta(partial_json: str) -> dict:
    return stream("content_block_delta", delta={"type": "input_json_delta", "partial_json": partial_json})


def test_skill_tool_naming_probe_triggers_before_block_stops():
    detector = TriggerDetector(PROBE)

    assert detector.classify(tool_start("Skill")) is None
    assert detector.classify(input_delta('{"skill": "demo-skill-sk')) is None
    assert detector.classify(input_delta('ill-0badcafe"}')) is True


def test_first_tool_other_than_skill_or_read_is_not_a_trigger():
    detector = TriggerDetector(PROBE)

    assert detector.classify(tool_start("Bash")) is False


def test_skill_tool_naming_another_skill_is_not_a_trigger():
    detector = TriggerDetector(PROBE)
    detector.classify(tool_start("Skill"))
    detector.classify(input_delta('{"skill": "other-skill"}'))

    assert detector.classify(stream("content_block_stop")) is False


def test_message_stop_without_tool_use_is_not_a_trigger():
    detector = TriggerDetector(PROBE)

    assert detector.classify(stream("message_stop")) is False


def test_assistant_message_reading_probe_file_is_a_trigger():
    detector = TriggerDetector(PROBE)
    message = {"content": [{"type": "tool_use", "name": "Read", "input": {"file_path": f"/p/.claude/commands/{PROBE}.md"}}]}

    assert detector.classify({"type": "assistant", "message": message}) is True


def test_result_event_without_verdict_is_not_a_trigger():
    detector = TriggerDetector(PROBE)

    assert detector.classify({"type": "result"}) is False
