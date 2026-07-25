#!/usr/bin/env python3
"""Tests for check_judge_prompt_version (#361 drift guard).

The clean fixture must PASS; a prompt edit that does not re-pin the hash must
FAIL (the core #361 backstop); a correct re-pin must PASS again; a removed
marker must error out (so the guard cannot be silently disabled).
"""
from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

import scripts.check_judge_prompt_version as lint

_PROMPT_BODY = "> CLAIM: {claim_text}\n> Output ONE verdict from {SUPPORTED, UNSUPPORTED}."


def _agent_md(prompt_body: str, *, with_markers: bool = True) -> str:
    if with_markers:
        section = (
            "<!-- JUDGE-PROMPT-CANONICAL-START (#361): note -->\n\n"
            f"{prompt_body}\n\n"
            "<!-- JUDGE-PROMPT-CANONICAL-END (#361) -->"
        )
    else:
        section = prompt_body
    return f"### Step 5 — Judge invocation\n\n{section}\n\n### Step 6 — next\n"


def _constants_src(pinned_hash: str) -> str:
    return (
        'JUDGE_PROMPT_VERSION = "step0-decomp-v1"\n'
        f'JUDGE_PROMPT_SHA256 = "{pinned_hash}"\n'
    )


def _hash_of(prompt_body: str) -> str:
    # Compute the expected hash via the PRODUCTION extraction path, not a shadow
    # copy of the regex — so an extraction bug fails test_clean_fixture_passes
    # instead of hiding behind a matching wrong answer on both sides.
    section = lint._extract_prompt_section(_agent_md(prompt_body))
    assert section is not None
    return hashlib.sha256(section.encode("utf-8")).hexdigest()


class CheckJudgePromptVersionTest(unittest.TestCase):
    def _write_root(self, agent_md: str, constants_src: str) -> Path:
        root = Path(tempfile.mkdtemp())
        agent = root / lint._AGENT_REL
        agent.parent.mkdir(parents=True, exist_ok=True)
        agent.write_text(agent_md, encoding="utf-8")
        constants = root / lint._CONSTANTS_REL
        constants.parent.mkdir(parents=True, exist_ok=True)
        constants.write_text(constants_src, encoding="utf-8")
        return root

    def test_clean_fixture_passes(self) -> None:
        root = self._write_root(_agent_md(_PROMPT_BODY), _constants_src(_hash_of(_PROMPT_BODY)))
        self.assertEqual(lint.check(root), 0)

    def test_prompt_edit_without_repin_fails(self) -> None:
        # Prompt changed; pinned hash still points at the OLD prompt → drift → fail.
        root = self._write_root(
            _agent_md(_PROMPT_BODY + "\n> EXTRA LINE that changes behavior"),
            _constants_src(_hash_of(_PROMPT_BODY)),
        )
        self.assertEqual(lint.check(root), 1)

    def test_prompt_edit_with_correct_repin_passes(self) -> None:
        # The correct bump flow: prompt changed AND hash re-pinned → pass.
        new_body = _PROMPT_BODY + "\n> EXTRA LINE that changes behavior"
        root = self._write_root(_agent_md(new_body), _constants_src(_hash_of(new_body)))
        self.assertEqual(lint.check(root), 0)

    def test_missing_markers_errors(self) -> None:
        root = self._write_root(
            _agent_md(_PROMPT_BODY, with_markers=False),
            _constants_src(_hash_of(_PROMPT_BODY)),
        )
        self.assertEqual(lint.check(root), 2)

    def test_missing_pinned_constant_errors(self) -> None:
        root = self._write_root(_agent_md(_PROMPT_BODY), 'JUDGE_PROMPT_VERSION = "x"\n')
        self.assertEqual(lint.check(root), 2)


if __name__ == "__main__":
    unittest.main()
