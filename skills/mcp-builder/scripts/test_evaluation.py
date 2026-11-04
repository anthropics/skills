"""Tests for mcp-builder evaluation helper functions."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from evaluation import extract_xml_content, parse_evaluation_file


def test_extract_xml_content_none_does_not_crash():
    """Regression: extract_xml_content raised TypeError when passed None
    (which agent_loop returns when the final message has no text block)."""
    assert extract_xml_content(None, "response") is None


def test_extract_xml_content_empty_string():
    assert extract_xml_content("", "response") is None


def test_extract_xml_content_single_match():
    text = "before <response>hello world</response> after"
    assert extract_xml_content(text, "response") == "hello world"


def test_extract_xml_content_returns_last_match():
    text = "<response>first</response> mid <response>second</response>"
    assert extract_xml_content(text, "response") == "second"


def test_extract_xml_content_no_match():
    assert extract_xml_content("no tags here", "response") is None


def test_extract_xml_content_multiline():
    text = "<summary>line one\nline two</summary>"
    assert extract_xml_content(text, "summary") == "line one\nline two"


def test_parse_evaluation_file(tmp_path):
    xml = """<?xml version="1.0"?>
<evaluations>
  <qa_pair>
    <question>What is 2+2?</question>
    <answer>4</answer>
  </qa_pair>
  <qa_pair>
    <question>Capital of France?</question>
    <answer>Paris</answer>
  </qa_pair>
</evaluations>"""
    f = tmp_path / "eval.xml"
    f.write_text(xml)
    result = parse_evaluation_file(f)
    assert len(result) == 2
    assert result[0]["question"] == "What is 2+2?"
    assert result[0]["answer"] == "4"
    assert result[1]["answer"] == "Paris"


def test_parse_evaluation_file_missing_elements(tmp_path):
    xml = """<?xml version="1.0"?>
<evaluations>
  <qa_pair><question>only question</question></qa_pair>
</evaluations>"""
    f = tmp_path / "eval.xml"
    f.write_text(xml)
    result = parse_evaluation_file(f)
    assert result == []


def test_parse_evaluation_file_invalid_xml(tmp_path):
    f = tmp_path / "eval.xml"
    f.write_text("not valid xml <<<")
    result = parse_evaluation_file(f)
    assert result == []
