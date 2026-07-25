"""Tests for the shared block parser (#89 Item 7 Slice A, spec §8.1).

Covers: segmentation per supported block class, marker attachment, the
§3.1 malformed-state rejections (duplicate IDs, orphan marker, marker
stack, marker-in-fence-as-content), the unsupported-construct rejections
by name (setext underline, raw-HTML opener, footnote definition), and
the §3.2 hash normalization rules.

Run standalone:
    python -m unittest scripts/test_block_parser.py -v
"""
from __future__ import annotations

import unittest

from scripts._block_parser import (
    BlockParseError,
    base_draft_hash,
    block_hash,
    normalize_block_text,
    parse_document,
    segment_fragment,
    split_lines_keepends,
)


def _kinds(text: str) -> list[str]:
    return [b.kind for b in parse_document(text).blocks]


class TestSegmentation(unittest.TestCase):
    def test_blank_separated_paragraphs(self):
        doc = parse_document("Para one.\n\nPara two.\n")
        self.assertEqual([b.kind for b in doc.blocks], ["text", "text"])
        self.assertEqual(doc.blocks[0].first_line, "Para one.")

    def test_multiline_paragraph_is_one_block(self):
        doc = parse_document("Line one\nline two\nline three.\n\nNext.\n")
        self.assertEqual(len(doc.blocks), 2)

    def test_atx_heading_is_single_line_block(self):
        doc = parse_document("# Title\nBody right under heading.\n")
        self.assertEqual([b.kind for b in doc.blocks], ["heading", "text"])

    def test_heading_interrupts_text_run(self):
        doc = parse_document("Intro text.\n## Section\n")
        self.assertEqual([b.kind for b in doc.blocks], ["text", "heading"])

    def test_fenced_code_never_split(self):
        text = "```python\n\ncode line\n\n# not a heading\n```\n"
        doc = parse_document(text)
        self.assertEqual([b.kind for b in doc.blocks], ["fence"])

    def test_tilde_fence(self):
        doc = parse_document("~~~\nx\n~~~\n")
        self.assertEqual([b.kind for b in doc.blocks], ["fence"])

    def test_unterminated_fence_rejected(self):
        with self.assertRaises(BlockParseError) as ctx:
            parse_document("```\ncode\n")
        self.assertEqual(ctx.exception.kind, "unterminated_fence")

    def test_table_run_is_one_block(self):
        text = "| a | b |\n|---|---|\n| 1 | 2 |\n"
        doc = parse_document(text)
        self.assertEqual([b.kind for b in doc.blocks], ["table"])

    def test_list_run_with_indented_continuation(self):
        text = "- item one\n  continued\n- item two\n"
        doc = parse_document(text)
        self.assertEqual([b.kind for b in doc.blocks], ["list"])

    def test_loose_list_blank_inside_run(self):
        text = "- item one\n\n- item two\n\nNot a list.\n"
        doc = parse_document(text)
        self.assertEqual([b.kind for b in doc.blocks], ["list", "text"])

    def test_ordered_list(self):
        doc = parse_document("1. one\n2. two\n")
        self.assertEqual([b.kind for b in doc.blocks], ["list"])

    def test_blockquote_run(self):
        doc = parse_document("> quoted\n> more\n\ntext\n")
        self.assertEqual([b.kind for b in doc.blocks], ["blockquote", "text"])

    def test_frontmatter_skipped_never_labeled(self):
        text = "---\ntitle: x\n---\n\nBody.\n"
        doc = parse_document(text)
        self.assertIsNotNone(doc.frontmatter_span)
        self.assertEqual(len(doc.blocks), 1)
        self.assertEqual(doc.text[doc.frontmatter_span[0] : doc.frontmatter_span[1]], "---\ntitle: x\n---\n")

    def test_unterminated_frontmatter_rejected(self):
        with self.assertRaises(BlockParseError) as ctx:
            parse_document("---\ntitle: x\n")
        self.assertEqual(ctx.exception.kind, "unterminated_frontmatter")

    def test_spans_reconstruct_document(self):
        text = "---\nfm: 1\n---\n\n# H\n\nPara.\n\n- l1\n- l2\n"
        doc = parse_document(text)
        rebuilt = doc.text[doc.frontmatter_span[0] : doc.frontmatter_span[1]]
        pos = doc.frontmatter_span[1]
        for b in doc.blocks:
            start = b.full_start
            rebuilt += doc.text[pos:start] + doc.text[start : b.span[1]]
            pos = b.span[1]
        rebuilt += doc.text[pos:]
        self.assertEqual(rebuilt, text)

    def test_no_trailing_newline_final_block(self):
        doc = parse_document("Para one.\n\nPara two no EOL")
        self.assertEqual(len(doc.blocks), 2)
        self.assertEqual(doc.text[doc.blocks[1].span[0] : doc.blocks[1].span[1]], "Para two no EOL")


class TestMarkers(unittest.TestCase):
    def test_marker_attaches_to_following_block(self):
        doc = parse_document("<!--block:B0001-->\nPara.\n")
        self.assertEqual(doc.blocks[0].block_id, "B0001")
        self.assertIsNotNone(doc.blocks[0].marker_span)

    def test_unlabeled_block_has_no_id(self):
        doc = parse_document("Para.\n")
        self.assertIsNone(doc.blocks[0].block_id)

    def test_orphan_marker_before_blank_rejected(self):
        with self.assertRaises(BlockParseError) as ctx:
            parse_document("<!--block:B0001-->\n\nPara.\n")
        self.assertEqual(ctx.exception.kind, "orphan_marker")
        self.assertTrue(ctx.exception.hint)

    def test_orphan_marker_at_eof_rejected(self):
        with self.assertRaises(BlockParseError) as ctx:
            parse_document("Para.\n\n<!--block:B0002-->\n")
        self.assertEqual(ctx.exception.kind, "orphan_marker")

    def test_marker_stack_rejected(self):
        with self.assertRaises(BlockParseError) as ctx:
            parse_document("<!--block:B0001-->\n<!--block:B0002-->\nPara.\n")
        self.assertEqual(ctx.exception.kind, "marker_stack")

    def test_duplicate_block_ids_rejected(self):
        text = "<!--block:B0001-->\nOne.\n\n<!--block:B0001-->\nTwo.\n"
        with self.assertRaises(BlockParseError) as ctx:
            parse_document(text)
        self.assertEqual(ctx.exception.kind, "duplicate_block_id")

    def test_marker_inside_fence_is_content(self):
        text = "```\n<!--block:B0009-->\n```\n\n<!--block:B0001-->\nPara.\n"
        doc = parse_document(text)
        self.assertEqual([b.block_id for b in doc.blocks], [None, "B0001"])
        self.assertIn("<!--block:B0009-->", doc.blocks[0].normalized_text)

    def test_next_fresh_id_is_max_plus_one(self):
        text = "<!--block:B0007-->\nOne.\n\n<!--block:B0003-->\nTwo.\n"
        doc = parse_document(text)
        self.assertEqual(doc.next_fresh_id_num(), 8)

    def test_marker_grammar_requires_exact_shape(self):
        # A near-miss marker line (missing the B prefix) is not a marker;
        # it is text content and merges with the adjacent text run.
        doc = parse_document("<!--block:0001-->\nPara.\n")
        self.assertEqual(len(doc.blocks), 1)
        self.assertIsNone(doc.blocks[0].block_id)
        self.assertIn("<!--block:0001-->", doc.blocks[0].normalized_text)


class TestUnsupportedConstructs(unittest.TestCase):
    def test_setext_underline_rejected_by_name(self):
        with self.assertRaises(BlockParseError) as ctx:
            parse_document("Heading text\n===\n")
        self.assertEqual(ctx.exception.kind, "unsupported_construct:setext_underline")

    def test_setext_dashes_rejected(self):
        with self.assertRaises(BlockParseError) as ctx:
            parse_document("Heading text\n---\n")
        self.assertEqual(ctx.exception.kind, "unsupported_construct:setext_underline")

    def test_thematic_break_after_blank_is_plain_text(self):
        doc = parse_document("Para.\n\n---\n\nMore.\n")
        self.assertEqual(len(doc.blocks), 3)

    def test_raw_html_opener_rejected_by_name(self):
        with self.assertRaises(BlockParseError) as ctx:
            parse_document("<div>\ncontent\n</div>\n")
        self.assertEqual(ctx.exception.kind, "unsupported_construct:raw_html_block")

    def test_footnote_definition_rejected_by_name(self):
        with self.assertRaises(BlockParseError) as ctx:
            parse_document("[^1]: a footnote definition\n")
        self.assertEqual(ctx.exception.kind, "unsupported_construct:footnote_definition")

    def test_inline_ref_marker_is_not_html_opener(self):
        # v3.7.1 citation markers start with <!-- which the raw-HTML
        # detector (^</?[A-Za-z]) must not catch.
        doc = parse_document("Claim text.<!--ref:smith2024-->\n")
        self.assertEqual([b.kind for b in doc.blocks], ["text"])


class TestFragmentMode(unittest.TestCase):
    def test_fragment_segments_multi_paragraph(self):
        spans = segment_fragment("Para one.\n\nPara two.")
        self.assertEqual(len(spans), 2)

    def test_fragment_rejects_embedded_marker(self):
        with self.assertRaises(BlockParseError) as ctx:
            segment_fragment("<!--block:B0001-->\nPara.\n")
        self.assertEqual(ctx.exception.kind, "marker_in_fragment")

    def test_fragment_rejects_empty(self):
        with self.assertRaises(BlockParseError) as ctx:
            segment_fragment("   \n\n")
        self.assertEqual(ctx.exception.kind, "empty_fragment")

    def test_fragment_has_no_frontmatter_detection(self):
        # A leading --- in a fragment is not frontmatter; --- after
        # nothing is a one-line text block (thematic-break shape).
        spans = segment_fragment("---\n\nPara.\n")
        self.assertEqual(len(spans), 2)

    def test_fragment_rejects_unsupported_constructs(self):
        with self.assertRaises(BlockParseError):
            segment_fragment("text\n===\n")


class TestNormalizationAndHashes(unittest.TestCase):
    def test_crlf_normalized_for_hash_only(self):
        self.assertEqual(
            normalize_block_text(["line one\r\n", "line two\r\n"]),
            "line one\nline two",
        )

    def test_blank_edges_stripped_intraline_whitespace_kept(self):
        self.assertEqual(
            normalize_block_text(["\n", "a  b  \n", "\n"]),
            "a  b  ",
        )

    def test_hash_is_12_hex(self):
        h = block_hash("some text")
        self.assertRegex(h, r"^[0-9a-f]{12}$")

    def test_base_draft_hash_is_12_hex_over_bytes(self):
        h = base_draft_hash(b"raw bytes")
        self.assertRegex(h, r"^[0-9a-f]{12}$")

    def test_crlf_and_lf_blocks_hash_equal(self):
        a = parse_document("Para text.\r\n").blocks[0]
        b = parse_document("Para text.\n").blocks[0]
        self.assertEqual(a.norm_hash, b.norm_hash)

    def test_split_lines_keepends_no_unicode_linebreak_split(self):
        # U+2028 must NOT split lines (str.splitlines would).
        lines = split_lines_keepends("a b\nc\n")
        self.assertEqual(lines, ["a b\n", "c\n"])


if __name__ == "__main__":
    unittest.main()
