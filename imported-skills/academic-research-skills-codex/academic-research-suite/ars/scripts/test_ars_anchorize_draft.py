"""Tests for ars_anchorize_draft.py (#89 Item 7 Slice A, spec §8.1).

Pins the three §8.1 anchorize properties — idempotent (second run
byte-identical), content-neutral (output minus marker lines == input),
manifest agreement (per-block hashes AND base_draft_hash equal an
independent apply-side recomputation) — plus fresh-ID assignment,
CRLF handling, schema validity of the emitted manifest, and the CLI
rejection path.

Run standalone:
    python -m unittest scripts/test_ars_anchorize_draft.py -v
"""
from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import jsonschema

from scripts._block_parser import MARKER_RE, base_draft_hash, parse_document
from scripts.ars_anchorize_draft import anchorize_file, anchorize_text, main

REPO_ROOT = Path(__file__).resolve().parent.parent
MANIFEST_SCHEMA = json.loads(
    (REPO_ROOT / "shared" / "contracts" / "patch" / "block_manifest.schema.json").read_text()
)

FIXTURE = """---
title: fixture
---

# Heading

First paragraph with a citation.<!--ref:smith2024-->

- item one
- item two

```python
code, untouched
```

> quoted line

Final paragraph.
"""


def _strip_marker_lines(text: str) -> str:
    kept = [
        line
        for line in text.split("\n")
        if not MARKER_RE.match(line.rstrip("\r"))
    ]
    return "\n".join(kept)


class TestAnchorizeText(unittest.TestCase):
    def test_all_blocks_labeled(self):
        anchored = anchorize_text(FIXTURE)
        parsed = parse_document(anchored)
        self.assertTrue(all(b.block_id is not None for b in parsed.blocks))
        self.assertEqual(len(parsed.blocks), 6)

    def test_ids_zero_padded_sequential_document_order(self):
        anchored = anchorize_text(FIXTURE)
        ids = [b.block_id for b in parse_document(anchored).blocks]
        self.assertEqual(ids, ["B0001", "B0002", "B0003", "B0004", "B0005", "B0006"])

    def test_idempotent(self):
        once = anchorize_text(FIXTURE)
        self.assertEqual(anchorize_text(once), once)

    def test_content_neutral(self):
        anchored = anchorize_text(FIXTURE)
        self.assertEqual(_strip_marker_lines(anchored), FIXTURE)

    def test_existing_ids_kept_fresh_is_max_plus_one(self):
        text = "<!--block:B0007-->\nLabeled.\n\nUnlabeled.\n"
        anchored = anchorize_text(text)
        ids = [b.block_id for b in parse_document(anchored).blocks]
        self.assertEqual(ids, ["B0007", "B0008"])

    def test_marker_directly_above_block_no_blank_line(self):
        anchored = anchorize_text("Para.\n")
        self.assertEqual(anchored, "<!--block:B0001-->\nPara.\n")

    def test_crlf_draft_gets_crlf_marker_lines(self):
        anchored = anchorize_text("Para one.\r\n\r\nPara two.\r\n")
        self.assertEqual(
            anchored,
            "<!--block:B0001-->\r\nPara one.\r\n\r\n<!--block:B0002-->\r\nPara two.\r\n",
        )

    def test_frontmatter_never_labeled(self):
        anchored = anchorize_text(FIXTURE)
        before_first_block = anchored.split("# Heading")[0]
        self.assertEqual(before_first_block.count("<!--block:"), 1)
        self.assertTrue(anchored.startswith("---\ntitle: fixture\n---\n"))


class TestAnchorizeFile(unittest.TestCase):
    def _run(self, content: str) -> tuple[Path, Path, dict]:
        tmp = Path(tempfile.mkdtemp())
        draft = tmp / "draft.md"
        draft.write_bytes(content.encode("utf-8"))
        manifest_path = Path(str(draft) + ".block-manifest.json")
        summary = anchorize_file(draft, manifest_path)
        return draft, manifest_path, summary

    def test_second_run_byte_identical_and_unchanged(self):
        draft, manifest_path, first = self._run(FIXTURE)
        self.assertTrue(first["changed"])
        after_first = draft.read_bytes()
        second = anchorize_file(draft, manifest_path)
        self.assertFalse(second["changed"])
        self.assertEqual(draft.read_bytes(), after_first)

    def test_manifest_validates_against_schema(self):
        _, manifest_path, _ = self._run(FIXTURE)
        manifest = json.loads(manifest_path.read_text())
        jsonschema.validate(manifest, MANIFEST_SCHEMA)

    def test_manifest_agreement_with_independent_recomputation(self):
        draft, manifest_path, _ = self._run(FIXTURE)
        manifest = json.loads(manifest_path.read_text())
        raw = draft.read_bytes()
        parsed = parse_document(raw.decode("utf-8"))
        self.assertEqual(manifest["base_draft_hash"], base_draft_hash(raw))
        self.assertEqual(
            [(b.block_id, b.norm_hash) for b in parsed.blocks],
            [(e["block_id"], e["old_hash"]) for e in manifest["blocks"]],
        )

    def test_excerpt_truncated_to_80(self):
        long_line = "x" * 200
        _, manifest_path, _ = self._run(long_line + "\n")
        manifest = json.loads(manifest_path.read_text())
        excerpt = manifest["blocks"][0]["first_line_excerpt"]
        self.assertLessEqual(len(excerpt), 80)
        self.assertTrue(excerpt.endswith("…"))

    def test_summary_counts(self):
        _, _, summary = self._run(FIXTURE)
        self.assertEqual(summary["blocks_total"], 6)
        self.assertEqual(summary["blocks_newly_labeled"], 6)


class TestCli(unittest.TestCase):
    def test_rejection_exits_2(self):
        tmp = Path(tempfile.mkdtemp())
        draft = tmp / "bad.md"
        draft.write_text("Heading\n===\n")
        self.assertEqual(main([str(draft)]), 2)
        self.assertFalse(Path(str(draft) + ".block-manifest.json").exists())
        self.assertEqual(draft.read_text(), "Heading\n===\n")

    def test_ok_exits_0_writes_manifest(self):
        tmp = Path(tempfile.mkdtemp())
        draft = tmp / "ok.md"
        draft.write_text("Para.\n")
        self.assertEqual(main([str(draft)]), 0)
        manifest = json.loads(Path(str(draft) + ".block-manifest.json").read_text())
        self.assertEqual(len(manifest["blocks"]), 1)

    def test_manifest_out_override(self):
        tmp = Path(tempfile.mkdtemp())
        draft = tmp / "ok.md"
        out = tmp / "custom-manifest.json"
        draft.write_text("Para.\n")
        self.assertEqual(main([str(draft), "--manifest-out", str(out)]), 0)
        self.assertTrue(out.exists())


if __name__ == "__main__":
    unittest.main()
