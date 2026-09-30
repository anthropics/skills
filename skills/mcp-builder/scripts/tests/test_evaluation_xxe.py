"""Regression tests for the XXE guard in evaluation.py (CWE-611).

parse_evaluation_file takes a CLI-supplied XML path; xml.etree resolves
external entities. The guard routes through defusedxml when installed,
else refuses DOCTYPE/entity declarations pre-parse.
"""
import sys
from pathlib import Path
from unittest import mock

import pytest

sys.modules.setdefault("anthropic", mock.MagicMock())
sys.modules.setdefault("connections", mock.MagicMock())

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation import parse_evaluation_file

BENIGN = """<?xml version="1.0"?>
<evaluations><qa_pair><question>q?</question><answer>a.</answer></qa_pair></evaluations>
"""
EVIL = """<?xml version="1.0"?>
<!DOCTYPE r [<!ENTITY xxe SYSTEM "file:///etc/passwd">]>
<evaluations><qa_pair><question>&xxe;</question><answer>a.</answer></qa_pair></evaluations>
"""


def test_benign_qa_parses(tmp_path):
    p = tmp_path / "eval.xml"
    p.write_text(BENIGN, encoding="utf-8")
    pairs = parse_evaluation_file(p)
    assert len(pairs) == 1
    assert pairs[0]["question"] == "q?"


def test_entity_payload_blocked(tmp_path):
    # Safe behavior on either code path: defusedxml raises (a ValueError),
    # the stdlib fallback refuses pre-parse. Either way no entity content
    # is ever returned.
    p = tmp_path / "evil.xml"
    p.write_text(EVIL, encoding="utf-8")
    try:
        pairs = parse_evaluation_file(p)
    except ValueError:
        return
    assert pairs == []
    assert "passwd" not in str(pairs)
