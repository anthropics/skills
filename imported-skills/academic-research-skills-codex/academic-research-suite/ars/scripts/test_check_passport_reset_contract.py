"""Unit tests for check_passport_reset_contract.py (ARS v3.6.3 lint).

Enforces the contract: every text file that mentions the env-flag token
`ARS_PASSPORT_RESET` must co-locate a reference to the protocol-doc stem
`passport_as_reset_boundary` so readers can follow the flag to the spec.

The protocol doc itself (`academic-pipeline/references/passport_as_reset_boundary.md`)
is exempt from needing a self-reference.

Also enforces: `pending_decision.options[]` must have unique `value` fields within
each options array.
"""
from __future__ import annotations

import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script
from scripts.check_passport_reset_contract import scan_duplicate_option_values

SCRIPT = Path(__file__).resolve().parent / "check_passport_reset_contract.py"


def _write(root: Path, rel_path: str, content: str) -> Path:
    """Create a text file at root/rel_path with UTF-8 content, parents auto-made."""
    path = root / rel_path
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return path


_DUPLICATE_VALUE_MD = """\
```yaml
reset_boundary:
  - kind: boundary
    hash: a3f2b7c9d0e1
    stage: "3"
    next: "4"
    generated_at: 2026-04-23T14:00:00Z
    session_marker: sess-1
    version_label: v1.0
    pending_decision:
      question: "Which path?"
      options:
        - value: revise
          next_stage: "4"
        - value: revise
          next_stage: "2"
```
"""

_UNIQUE_VALUE_MD = """\
```yaml
reset_boundary:
  - kind: boundary
    hash: b4c2d8e7f0a1
    stage: "3"
    next: "4"
    generated_at: 2026-04-24T10:00:00Z
    session_marker: sess-2
    version_label: v1.0
    pending_decision:
      question: "Stage 3 reviewer decision"
      options:
        - value: revise
          next_stage: "4"
          next_mode: revision
        - value: restructure
          next_stage: "2"
          next_mode: plan
        - value: abort
          next_stage: null
```
"""


class TestPassportResetContractLint(unittest.TestCase):
    def test_empty_repo_passes(self):
        with TemporaryDirectory() as td:
            root = Path(td)
            result = run_script(SCRIPT, "--root", str(root))
            self.assertEqual(result.returncode, 0, msg=result.stderr)

    def test_mention_without_protocol_ref_fails(self):
        with TemporaryDirectory() as td:
            root = Path(td)
            _write(root, "some_doc.md", "Set ARS_PASSPORT_RESET=1 to enable the flag.\n")
            result = run_script(SCRIPT, "--root", str(root))
            self.assertEqual(result.returncode, 1, msg=result.stdout + result.stderr)
            # Diagnostic should name the required protocol-doc stem.
            combined = result.stdout + result.stderr
            self.assertIn("passport_as_reset_boundary", combined)

    def test_mention_with_protocol_ref_passes(self):
        with TemporaryDirectory() as td:
            root = Path(td)
            _write(
                root,
                "some_doc.md",
                "Set ARS_PASSPORT_RESET=1 to enable.\n"
                "See academic-pipeline/references/passport_as_reset_boundary.md for details.\n",
            )
            result = run_script(SCRIPT, "--root", str(root))
            self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)

    def test_protocol_doc_itself_passes_without_self_reference(self):
        with TemporaryDirectory() as td:
            root = Path(td)
            # The protocol doc IS the reference — it does not need to link to itself.
            _write(
                root,
                "academic-pipeline/references/passport_as_reset_boundary.md",
                "# Passport as Reset Boundary\n\n"
                "This protocol is activated by the ARS_PASSPORT_RESET env flag.\n",
            )
            result = run_script(SCRIPT, "--root", str(root))
            self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)

    def test_json_description_satisfies_reference(self):
        with TemporaryDirectory() as td:
            root = Path(td)
            _write(
                root,
                "shared/contracts/passport/reset_ledger_entry.schema.json",
                '{"description": "Set ARS_PASSPORT_RESET=1; see '
                'academic-pipeline/references/passport_as_reset_boundary.md for protocol."}\n',
            )
            result = run_script(SCRIPT, "--root", str(root))
            self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)

    def test_code_comment_still_requires_reference(self):
        with TemporaryDirectory() as td:
            root = Path(td)
            _write(root, "scripts/foo.py", "# ARS_PASSPORT_RESET handling\n")
            result = run_script(SCRIPT, "--root", str(root))
            self.assertEqual(result.returncode, 1, msg=result.stdout + result.stderr)

    def test_binary_file_skipped(self):
        with TemporaryDirectory() as td:
            root = Path(td)
            blob = root / "blob.bin"
            blob.write_bytes(b"\x00\x01\x02ARS_PASSPORT_RESET\x03\x04\xff\xfe")
            result = run_script(SCRIPT, "--root", str(root))
            # Binary bytes (0xff, 0xfe, null) fail UTF-8 decode; the lint must
            # skip silently — returncode 0 — while never crashing.
            self.assertNotIn("Traceback", result.stderr)
            self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)

    def test_detects_duplicate_option_values_in_pending_decision(self):
        """Duplicate value within one options array must produce a violation."""
        with TemporaryDirectory() as td:
            root = Path(td)
            path = _write(root, "shared/handoff_schemas.md", _DUPLICATE_VALUE_MD)
            violations = scan_duplicate_option_values(root)
            self.assertTrue(
                violations,
                msg="Expected a violation for duplicate option value 'revise', got none.",
            )
            combined = " ".join(violations)
            self.assertIn("revise", combined)

    def test_unique_option_values_pass(self):
        """Unique values in options array must produce no violations."""
        with TemporaryDirectory() as td:
            root = Path(td)
            _write(root, "shared/handoff_schemas.md", _UNIQUE_VALUE_MD)
            violations = scan_duplicate_option_values(root)
            self.assertEqual(
                violations,
                [],
                msg=f"Expected no violations for unique option values, got: {violations}",
            )

    def test_triple_duplicate_reports_one_per_value(self):
        """Three options sharing a single value still produce one violation entry."""
        triple_md = (
            "```yaml\n"
            "reset_boundary:\n"
            "  - kind: boundary\n"
            "    hash: c5d3e9f8a1b2\n"
            "    stage: \"3\"\n"
            "    next: \"4\"\n"
            "    generated_at: 2026-04-23T14:00:00Z\n"
            "    session_marker: sess-triple\n"
            "    version_label: v1.0\n"
            "    pending_decision:\n"
            "      question: \"q\"\n"
            "      options:\n"
            "        - value: revise\n"
            "          next_stage: \"4\"\n"
            "        - value: revise\n"
            "          next_stage: \"3\"\n"
            "        - value: revise\n"
            "          next_stage: \"2\"\n"
            "```\n"
        )
        with TemporaryDirectory() as td:
            root = Path(td)
            _write(root, "shared/handoff_schemas.md", triple_md)
            violations = scan_duplicate_option_values(root)
            # One violation per unique duplicate value, not one per extra occurrence.
            self.assertEqual(len(violations), 1, msg=violations)
            self.assertIn("c5d3e9f8a1b2", violations[0])
            self.assertIn("revise", violations[0])

    def test_multiple_pending_decision_blocks_independent(self):
        """Two fenced yaml blocks in one file are evaluated independently."""
        multi_block_md = _UNIQUE_VALUE_MD + "\n\nAnother example:\n\n" + _DUPLICATE_VALUE_MD
        with TemporaryDirectory() as td:
            root = Path(td)
            _write(root, "shared/handoff_schemas.md", multi_block_md)
            violations = scan_duplicate_option_values(root)
            # First block clean, second block dup. Must catch only the second.
            self.assertEqual(len(violations), 1, msg=violations)
            self.assertIn("revise", violations[0])

    def test_yml_extension_and_crlf_fence(self):
        """Fence variants `yml` and CRLF line endings must still be parsed."""
        yml_crlf_md = (
            "Intro prose.\r\n\r\n"
            "```yml  \r\n"
            "reset_boundary:\r\n"
            "  - kind: boundary\r\n"
            "    hash: d6f4a0c1b2e3\r\n"
            "    stage: \"3\"\r\n"
            "    next: \"4\"\r\n"
            "    generated_at: 2026-04-23T14:00:00Z\r\n"
            "    session_marker: sess-crlf\r\n"
            "    version_label: v1.0\r\n"
            "    pending_decision:\r\n"
            "      question: \"q\"\r\n"
            "      options:\r\n"
            "        - value: dup\r\n"
            "          next_stage: \"4\"\r\n"
            "        - value: dup\r\n"
            "          next_stage: \"2\"\r\n"
            "```\r\n"
        )
        with TemporaryDirectory() as td:
            root = Path(td)
            _write(root, "shared/handoff_schemas.md", yml_crlf_md)
            violations = scan_duplicate_option_values(root)
            self.assertEqual(len(violations), 1, msg=violations)
            self.assertIn("dup", violations[0])


if __name__ == "__main__":
    unittest.main()
