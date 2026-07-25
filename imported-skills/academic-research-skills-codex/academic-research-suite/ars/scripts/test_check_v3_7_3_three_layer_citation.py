"""Tests for v3.7.3 Three-Layer Citation lint.

Spec: docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md §3.1
External motivation: Zhao et al. arXiv:2605.07723 (2026-05).
"""
from __future__ import annotations

from pathlib import Path

import pytest

import importlib.util
import sys

SCRIPT_PATH = Path(__file__).resolve().parent / "check_v3_7_3_three_layer_citation.py"
spec = importlib.util.spec_from_file_location("lint_module", SCRIPT_PATH)
lint_module = importlib.util.module_from_spec(spec)
sys.modules["lint_module"] = lint_module
spec.loader.exec_module(lint_module)
lint_file = lint_module.lint_file


def write(tmp_path: Path, content: str) -> Path:
    p = tmp_path / "draft.md"
    p.write_text(content, encoding="utf-8")
    return p


# --- Positive cases ----------------------------------------------------

def test_quote_anchor_passes(tmp_path: Path):
    p = write(tmp_path, "Smith (2024) <!--ref:smith2024--><!--anchor:quote:An%20excerpt-->")
    assert lint_file(p) == []


def test_page_anchor_passes(tmp_path: Path):
    p = write(tmp_path, "Smith (2024) <!--ref:smith2024--><!--anchor:page:12-14-->")
    assert lint_file(p) == []


def test_section_anchor_passes(tmp_path: Path):
    p = write(tmp_path, "Smith (2024) <!--ref:smith2024--><!--anchor:section:3.2-->")
    assert lint_file(p) == []


def test_paragraph_anchor_passes(tmp_path: Path):
    p = write(tmp_path, "Smith (2024) <!--ref:smith2024--><!--anchor:paragraph:3-->")
    assert lint_file(p) == []


def test_resolved_low_warn_marker_with_anchor_passes(tmp_path: Path):
    """v3.7.1 finalizer-resolved LOW-WARN ref + anchor still passes."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024 LOW-WARN--><!--anchor:page:14-->",
    )
    assert lint_file(p) == []


def test_resolved_ok_with_contamination_marker_passes(tmp_path: Path):
    """v3.7.3 contamination annotation suffix in ref marker still passes."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024 ok CONTAMINATED-PREPRINT--><!--anchor:page:14-->",
    )
    assert lint_file(p) == []


def test_multiple_citations_all_anchored_pass(tmp_path: Path):
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:page:1--> and "
        "Jones (2025) <!--ref:jones2025--><!--anchor:quote:short-->.",
    )
    assert lint_file(p) == []


def test_quote_exactly_25_words_passes(tmp_path: Path):
    twenty_five = "%20".join(["word"] * 25)
    p = write(
        tmp_path,
        f"Smith (2024) <!--ref:smith2024--><!--anchor:quote:{twenty_five}-->",
    )
    assert lint_file(p) == []


# --- Negative cases ----------------------------------------------------

def test_bare_ref_without_anchor_fails(tmp_path: Path):
    """v3.7.1 Two-Layer-only citation now violates v3.7.3."""
    p = write(tmp_path, "Smith (2024) <!--ref:smith2024-->.")
    violations = lint_file(p)
    assert len(violations) == 1
    assert "without trailing anchor" in violations[0]
    assert "R-L3-1-A" in violations[0]


def test_orphan_anchor_without_ref_fails(tmp_path: Path):
    """Anchor marker without preceding ref is a violation."""
    p = write(tmp_path, "Some prose <!--anchor:page:14--> and more.")
    violations = lint_file(p)
    assert len(violations) == 1
    assert "orphan anchor" in violations[0]


def test_invalid_anchor_kind_fails(tmp_path: Path):
    """Anchor kind outside the closed enum is rejected."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:url:https://example.com-->",
    )
    violations = lint_file(p)
    # urlencoded scheme doesn't match the kind enum: lint should report
    # orphan-anchor (because the regex doesn't match) — either way it's
    # a violation. Assert at least one violation reported.
    assert len(violations) >= 1


def test_quote_exceeding_25_words_fails(tmp_path: Path):
    twenty_six = "%20".join(["word"] * 26)
    p = write(
        tmp_path,
        f"Smith (2024) <!--ref:smith2024--><!--anchor:quote:{twenty_six}-->",
    )
    violations = lint_file(p)
    assert len(violations) == 1
    assert "exceeds 25 words" in violations[0]
    assert "R-L3-1-B" in violations[0]


def test_none_kind_anchor_passes_lint_but_gate_refuses(tmp_path: Path):
    """v3.7.3 R-L3-1-A: emitting `none` is contract-legal (it triggers the
    gate at finalizer time, not at lint time). The lint only checks anchor
    presence and shape; finalizer applies the precedence-zero MED-WARN
    refusal. So `<!--anchor:none:-->` PASSES the lint."""
    p = write(tmp_path, "Smith (2024) <!--ref:smith2024--><!--anchor:none:-->")
    assert lint_file(p) == []


def test_missing_file_reports_violation(tmp_path: Path):
    p = tmp_path / "does-not-exist.md"
    violations = lint_file(p)
    assert len(violations) == 1
    assert "does not exist" in violations[0]


# --- v3.7.3 gemini review F1 closure: hyphen encoding ------------------

def test_quote_with_raw_double_hyphen_fails(tmp_path: Path):
    """v3.7.3 F1: `--` in URL-encoded quote value can prematurely close
    the HTML comment. Must percent-encode `-` as `%2D`."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:quote:foo--bar-->",
    )
    violations = lint_file(p)
    assert len(violations) >= 1
    # Find the F1 violation specifically.
    assert any("raw `--`" in v and "F1" in v for v in violations)


def test_quote_with_encoded_hyphen_passes(tmp_path: Path):
    """v3.7.3 F1: properly encoded `%2D` is acceptable."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:quote:foo%2D%2Dbar-->",
    )
    assert lint_file(p) == []


def test_quote_with_single_raw_hyphen_passes(tmp_path: Path):
    """v3.7.3 F1: single `-` is harmless; only `--` breaks HTML comments.
    Linting consecutive `--` only avoids false-positive on legitimate
    single hyphens that survive encoding."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:quote:foo-bar-->",
    )
    assert lint_file(p) == []


# --- v3.7.3 gemini review F2 closure: whitespace between ref + anchor ---

def test_ref_anchor_separated_by_single_space_passes(tmp_path: Path):
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--> <!--anchor:page:12-->",
    )
    assert lint_file(p) == []


def test_ref_anchor_separated_by_multiple_spaces_passes(tmp_path: Path):
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024-->    <!--anchor:page:12-->",
    )
    assert lint_file(p) == []


def test_ref_anchor_separated_by_newline_passes(tmp_path: Path):
    """v3.7.3 F2: LLM may emit ref + anchor on separate lines."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024-->\n<!--anchor:page:12-->",
    )
    assert lint_file(p) == []


def test_ref_anchor_separated_by_newline_and_tab_passes(tmp_path: Path):
    """v3.7.3 F2: mixed whitespace (newline + indent) between markers."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024-->\n\t<!--anchor:page:12-->",
    )
    assert lint_file(p) == []


# --- v3.7.3 gemini review F7 closure: fenced code block isolation ------

def test_ref_inside_fenced_code_block_is_ignored(tmp_path: Path):
    """v3.7.3 F7: ref/anchor markers inside ``` fenced code blocks are
    documentation examples (in spec docs, README, agent prompts) and
    must NOT trigger violations."""
    p = write(
        tmp_path,
        "Some prose.\n\n"
        "```\n"
        "Example: Smith (2024) <!--ref:smith2024-->\n"
        "```\n\n"
        "After fence.",
    )
    assert lint_file(p) == []


def test_ref_outside_fence_still_lints(tmp_path: Path):
    """v3.7.3 F7: lint still catches violations outside fences when a
    fence is present in the same file."""
    p = write(
        tmp_path,
        "```\n"
        "Example inside fence: <!--ref:example-->\n"
        "```\n\n"
        "Bad outside: Smith (2024) <!--ref:smith2024-->.",
    )
    violations = lint_file(p)
    assert len(violations) == 1
    assert "smith2024" in violations[0]


def test_tilde_fenced_code_block_also_ignored(tmp_path: Path):
    """v3.7.3 F7: ~~~ fences (CommonMark alternative) also skip linting."""
    p = write(
        tmp_path,
        "Prose.\n\n"
        "~~~\n"
        "Example: <!--ref:smith2024-->\n"
        "~~~\n",
    )
    assert lint_file(p) == []


def test_nested_html_comment_marker_in_quote_value_handled(tmp_path: Path):
    """v3.7.3 F7: a quote value containing an HTML-comment-like substring
    (after proper percent-encoding incl. hyphen-encode per F1) should
    still parse cleanly. This documents the encoding-handles-everything
    invariant — if F1 hyphen rule holds, the value can never contain
    a literal `<!--` or `-->`."""
    # `<!--` URL-encoded is `%3C%21%2D%2D`. Lint should accept this.
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:quote:%3C%21%2D%2Dtag%2D%2D%3E-->",
    )
    assert lint_file(p) == []


# --- v3.7.3 codex round-2 F8 closure: 2-token ref suffix (contamination) ---

def test_contamination_2_token_suffix_with_valid_anchor_passes(tmp_path: Path):
    """v3.7.3 F8: ref carrying `ok CONTAMINATED-PREPRINT` is the
    v3.7.3 finalizer-resolved shape for `ok` + preprint contamination.
    Must still pair correctly with the trailing anchor marker."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024 ok CONTAMINATED-PREPRINT--><!--anchor:page:14-->",
    )
    assert lint_file(p) == []


def test_contamination_2_token_low_warn_combined_with_anchor_passes(tmp_path: Path):
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024 LOW-WARN CONTAMINATED-PREPRINT+UNMATCHED--><!--anchor:page:14-->",
    )
    assert lint_file(p) == []


def test_contamination_2_token_ref_without_anchor_caught(tmp_path: Path):
    """v3.7.3 F8: previously the 2-token regex skipped these refs
    entirely, so missing-anchor violations went undetected. Lint must
    now catch them."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024 ok CONTAMINATED-PREPRINT-->.",
    )
    violations = lint_file(p)
    assert len(violations) == 1
    assert "without trailing anchor" in violations[0]


# --- v3.7.3 codex round-2 F9 closure: empty non-none anchor values -----

def test_empty_page_anchor_fails(tmp_path: Path):
    """v3.7.3 F9: `<!--anchor:page:-->` carries no locator payload but
    is non-`none`. Must trigger violation, not bypass the gate."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:page:-->",
    )
    violations = lint_file(p)
    assert len(violations) == 1
    assert "empty anchor value" in violations[0]
    assert "F9" in violations[0]


def test_empty_quote_anchor_fails(tmp_path: Path):
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:quote:-->",
    )
    violations = lint_file(p)
    assert len(violations) == 1
    assert "empty anchor value" in violations[0]


def test_empty_section_anchor_fails(tmp_path: Path):
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:section:-->",
    )
    violations = lint_file(p)
    assert len(violations) == 1
    assert "empty anchor value" in violations[0]


def test_whitespace_only_value_fails(tmp_path: Path):
    """v3.7.3 F9: a value of just whitespace is functionally empty."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:page:   -->",
    )
    violations = lint_file(p)
    assert len(violations) == 1
    assert "empty anchor value" in violations[0]


def test_empty_none_anchor_still_passes_lint(tmp_path: Path):
    """v3.7.3 F9: `none` is the one kind that legitimately has an
    empty value (it's the explicit no-anchor declaration). Lint must
    not flag it — finalizer's precedence-zero rule catches it later."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:none:-->",
    )
    assert lint_file(p) == []


# --- v3.7.3 codex round-3 F10 closure: premature comment terminator ----

def test_quote_with_raw_arrow_close_caught(tmp_path: Path):
    """v3.7.3 F10: `<!--anchor:quote:foo-->bar-->` looks like a valid
    anchor to the main regex (which stops at the first `-->`), but the
    HTML parser sees the comment close at byte 24 and treats `bar-->`
    as visible trailing prose. The main F1 check on `--` in value
    never sees the second `-->` because the regex stopped early.
    Sentinel scan must catch this."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:quote:foo-->bar-->",
    )
    violations = lint_file(p)
    assert any("F10" in v for v in violations), f"violations={violations}"


def test_quote_followed_by_normal_ref_still_passes(tmp_path: Path):
    """v3.7.3 F10: trailing whitespace + next `<!--ref:` is legitimate,
    not a leak. Sentinel scan must not false-positive here."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:quote:short--> "
        "and Jones (2025) <!--ref:jones2025--><!--anchor:page:1-->",
    )
    assert lint_file(p) == []


def test_quote_with_single_arrow_ambiguous_passes(tmp_path: Path):
    """v3.7.3 F10 boundary: a single `-->` followed by prose like
    `bar.` is statically indistinguishable from a legitimate
    anchor-close + normal trailing prose. The sentinel scan only
    catches DEFINITE leaks (trailing `-->` proves a second
    comment-terminator was emitted inside what should have been one
    encoded payload). Single-terminator + ambiguous prose passes."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:quote:foo-->bar.",
    )
    # Lint cannot statically decide leak vs legit; passes here. The
    # actual remediation is the encoded form `<!--anchor:quote:foo%2D%2Dbar-->`
    # which would unambiguously include both intent + safety.
    assert lint_file(p) == []


# --- v3.7.3 codex round-4 F12 closure: orphan after non-ref comment ----

def test_anchor_after_arbitrary_html_comment_caught(tmp_path: Path):
    """v3.7.3 F12: an anchor preceded by a non-ref HTML comment is an
    orphan — the `<!--note-->` is not a ref marker. The earlier
    `(?<!-->)` lookbehind incorrectly skipped this case."""
    p = write(
        tmp_path,
        "<!--note--><!--anchor:page:1-->",
    )
    violations = lint_file(p)
    assert any("orphan anchor" in v for v in violations), f"violations={violations}"


def test_anchor_after_3_token_malformed_ref_caught(tmp_path: Path):
    """v3.7.3 F12: a ref with 3 status tokens exceeds the {0,2} cap on
    the main ref_anchor_pattern. The malformed ref is not matched by
    the main loop AND was previously skipped by orphan scan because
    its `-->` close fooled the lookbehind. Now the orphan scan walks
    every anchor and checks for a well-formed preceding ref."""
    p = write(
        tmp_path,
        "<!--ref:slug ok CONTAMINATED-PREPRINT EXTRA--><!--anchor:page:1-->",
    )
    violations = lint_file(p)
    assert any("orphan anchor" in v for v in violations), f"violations={violations}"


def test_anchor_after_well_formed_ref_still_passes(tmp_path: Path):
    """v3.7.3 F12 boundary: legitimate ref+anchor pairs (1 or 2 status
    tokens, valid slug pattern) must still pass — removing the
    lookbehind cannot regress the happy path."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024 ok CONTAMINATED-PREPRINT--><!--anchor:page:1-->",
    )
    assert lint_file(p) == []


# --- v3.7.3 codex round-5 F14 closure: malformed ref without anchor ----

def test_malformed_ref_3_tokens_no_anchor_caught(tmp_path: Path):
    """v3.7.3 F14: ref with 3 status tokens exceeds the {0,2} cap.
    Without trailing anchor, both the main ref_anchor_pattern AND the
    orphan scan miss it. Broad scan must catch the malformed ref."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024 ok CONTAMINATED-PREPRINT EXTRA-->.",
    )
    violations = lint_file(p)
    assert any("malformed ref" in v and "F14" in v for v in violations), \
        f"violations={violations}"


def test_malformed_ref_with_invalid_slug_caught(tmp_path: Path):
    """v3.7.3 F14: slug starting with a digit fails the strict pattern;
    must still be flagged as malformed."""
    p = write(
        tmp_path,
        "(2024) <!--ref:2024smith ok-->.",
    )
    violations = lint_file(p)
    assert any("malformed ref" in v for v in violations), \
        f"violations={violations}"


def test_malformed_ref_4_tokens_with_anchor_caught(tmp_path: Path):
    """v3.7.3 F14: even when an anchor follows the malformed ref,
    the malformed ref itself is reported (separate violation from
    F12 orphan-anchor)."""
    p = write(
        tmp_path,
        "<!--ref:smith2024 ok CONTAMINATED-PREPRINT EXTRA TOKEN--><!--anchor:page:1-->",
    )
    violations = lint_file(p)
    # Both F14 (malformed ref) and F12 (orphan anchor — because the
    # malformed ref is not a well-formed preceding ref) fire here.
    assert any("malformed ref" in v for v in violations), \
        f"violations={violations}"


def test_well_formed_ref_with_2_tokens_does_not_trigger_malformed(tmp_path: Path):
    """v3.7.3 F14 boundary: 2-token ref (slug + ok + contamination)
    is the legitimate v3.7.3 contamination-annotation shape; must
    NOT trigger malformed-ref violation."""
    p = write(
        tmp_path,
        "<!--ref:smith2024 ok CONTAMINATED-PREPRINT--><!--anchor:page:1-->",
    )
    assert lint_file(p) == []


# --- v3.7.3 codex round-6 F15 closure: prompt-vs-lint alignment --------

def test_quote_with_single_hyphen_explicitly_allowed(tmp_path: Path):
    """v3.7.3 F15: prompts and lint align on "encode consecutive `--`,
    raw single `-` is fine". `AI-generated` survives raw. This is
    the post-round-6 weak rule (lint was always weak; prompts had
    been written as strong "encode every `-`" and were the
    inconsistent party — adjusted in F15 commit)."""
    p = write(
        tmp_path,
        "Chen (2024) <!--ref:chen2024--><!--anchor:quote:AI-generated%20text-->",
    )
    assert lint_file(p) == []


def test_quote_with_triple_hyphen_must_encode_first_double(tmp_path: Path):
    """v3.7.3 F15 boundary: `---` contains `--`. The lint rejects
    any consecutive `--` regardless of length. Three hyphens
    (`---`) MUST encode at least the first two."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:quote:foo---bar-->",
    )
    violations = lint_file(p)
    assert any("raw `--`" in v for v in violations), f"violations={violations}"


# --- v3.7.3 codex round-8 F19 closure: decode before empty check -------

def test_url_encoded_whitespace_page_anchor_caught(tmp_path: Path):
    """v3.7.3 F19: `<!--anchor:page:%20%20-->` looks non-empty as raw
    bytes but decodes to two spaces — functionally no locator. F9
    pre-decode check missed this; F19 closure adds unquote() before
    the strip() emptiness check."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:page:%20%20-->",
    )
    violations = lint_file(p)
    assert any("empty anchor value" in v for v in violations), \
        f"violations={violations}"


def test_url_encoded_single_space_quote_anchor_caught(tmp_path: Path):
    """v3.7.3 F19: same logic for quote kind — decoded `%20` is one
    space, no actual quoted content."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:quote:%20-->",
    )
    violations = lint_file(p)
    assert any("empty anchor value" in v for v in violations), \
        f"violations={violations}"


def test_url_encoded_real_content_passes(tmp_path: Path):
    """v3.7.3 F19 boundary: encoded value with real content (e.g.
    `An%20excerpt` = `An excerpt`) decodes to non-empty and passes."""
    p = write(
        tmp_path,
        "Smith (2024) <!--ref:smith2024--><!--anchor:quote:An%20excerpt-->",
    )
    assert lint_file(p) == []
