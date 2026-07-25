#!/usr/bin/env python3
"""Mutation tests for scripts/check_policy_anchor_protocol.py."""
from __future__ import annotations

import sys
import textwrap
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))

import check_policy_anchor_protocol as cpap  # noqa: E402


# Each named invariant from impl spec §4.3 must be referenced verbatim. The
# protocol doc must also resolve each §4.4 #1–#11 concern by name and carry
# the §3 G10 7-row precedence table verbatim from Decision Doc.
_GOOD_PROTOCOL = textwrap.dedent(
    """\
    # Policy-Anchor Disclosure Protocol (#108)

    **Anchor inventory**: `prisma-trAIce, icmje, nature, ieee`

    ## Frozen invariants from Decision Doc §4.3

    - G1 invariant — no ai_disclosure field added to corpus entry schema
    - G2 invariant — SLR mode dispatches via slr_lineage to PRISMA-trAIce track
    - G3 / G10 invariant — seven-row precedence table holds; auto-promotion forbiddance
    - G4 invariant — 4 policy-anchor renderers; Nature dedup
    - G5 invariant — PRISMA M6 fires only when all three gates hold
    - G7 invariant — copyediting carve-out anchor-specific
    - G8 invariant — IEEE #5 + #6 paired mandate
    - G9 invariant — image-rights regimes anchor-specific

    ## §4.4 open concerns resolved

    - concern #1 — explicit slr_lineage input
    - concern #2 — auto-detect tool identity per v3.2 Phase 4
    - concern #3 — per-(tool × task) prompt scope tuple
    - concern #4 — IEEE locator free-form list with IMRaD exemplars
    - concern #5 — Nature image hybrid annotation + suggested patches
    - concern #6 — UNCERTAIN per-facet annotation alongside USED render
    - concern #7 — venue+anchor conflict reject with error
    - concern #8 — three-state completeness flag full spec
    - concern #9 — test set scope covers all invariants + concerns
    - concern #10 — ai_used:true force v3.2 categorization flow
    - concern #11 — G1 invariant scope narrowing per §2.1 authoritative

    ## G10 7-row precedence table (whole-disclosure)

    | # | Precondition | Output |
    |---|---|---|
    | 1 | ai_used:false AND ≥1 category USED | Honest conflict annotation |
    | 2 | ai_used:false AND no USED AND no UNCERTAIN | No-AI statement (G10 opt-in) |
    | 3 | ai_used:false AND ≥1 UNCERTAIN AND no USED | Honest tension annotation |
    | 4 | ai_used:true OR ≥1 USED, row 1 not match | Full anchor disclosure render |
    | 5 | ≥1 UNCERTAIN AND no USED AND no ai_used | Honest not-supplied annotation |
    | 6 | All NOT USED AND no UNCERTAIN AND no ai_used | Silence (G10 default-OK) |
    | 7 | Empty input across every dimension | Honest cold-start annotation |

    ## Auto-promotion forbiddance

    A still-UNCERTAIN category MUST NOT be rendered as though USED in any of
    the four anchor outputs. This is the §4.3 G3/G10 invariant the
    implementation enforces.

    ## Anchor lookup mechanism

    Renderer reads `policy_anchor_table.md` keyed by `--policy-anchor=<a>`
    where a ∈ {prisma-trAIce, icmje, nature, ieee}.

    ## v3.2 Nature venue dedup

    Both the v3.2 Nature venue renderer and the Nature anchor renderer cite
    the canonical source pointer `shared/policy_data/nature_policy.md`.
    """
)


class CheckPolicyAnchorProtocolGoldenPathTest(unittest.TestCase):
    def test_good_protocol_passes(self) -> None:
        violations = cpap.lint_text(_GOOD_PROTOCOL)
        self.assertEqual(violations, [], msg=f"unexpected violations: {violations}")


class CheckPolicyAnchorProtocolMutationTests(unittest.TestCase):
    def test_missing_invariant_reference_fails(self) -> None:
        bad = _GOOD_PROTOCOL.replace("G1 invariant", "")
        violations = cpap.lint_text(bad)
        self.assertTrue(
            any("G1" in v for v in violations),
            msg=f"expected G1 invariant violation; got {violations}",
        )

    def test_missing_concern_resolution_fails(self) -> None:
        bad = _GOOD_PROTOCOL.replace("concern #6", "")
        violations = cpap.lint_text(bad)
        self.assertTrue(
            any("#6" in v or "concern 6" in v.lower() for v in violations),
            msg=f"expected concern #6 violation; got {violations}",
        )

    def test_missing_g10_table_row_fails(self) -> None:
        # Drop row 4 — the load-bearing full-anchor-disclosure row
        bad = _GOOD_PROTOCOL.replace(
            "| 4 | ai_used:true OR ≥1 USED, row 1 not match | Full anchor disclosure render |",
            "",
        )
        violations = cpap.lint_text(bad)
        self.assertTrue(
            any("row 4" in v.lower() or "7-row" in v.lower() for v in violations),
            msg=f"expected G10 row 4 violation; got {violations}",
        )

    def test_missing_auto_promotion_forbiddance_fails(self) -> None:
        # Strip every mention of both forbiddance keywords so the validator
        # has nothing to anchor on; replace with neutral filler text.
        bad = _GOOD_PROTOCOL
        bad = bad.replace("auto-promotion forbiddance", "(removed clause)")
        bad = bad.replace("Auto-promotion forbiddance", "Removed clause")
        bad = bad.replace(
            "A still-UNCERTAIN category MUST NOT be rendered as though USED in any of\n"
            "the four anchor outputs.",
            "",
        )
        violations = cpap.lint_text(bad)
        self.assertTrue(
            any("auto-promot" in v.lower() or "UNCERTAIN" in v for v in violations),
            msg=f"expected auto-promotion forbiddance violation; got {violations}",
        )

    def test_partial_auto_promotion_token_loss_still_fails(self) -> None:
        # Codex round-2 P2 #3: dropping the load-bearing MUST NOT sentence
        # while keeping the "auto-promotion" heading should still fail. The
        # protocol's invariant is the prohibition itself; the heading word
        # alone is insufficient.
        bad = _GOOD_PROTOCOL.replace(
            "A still-UNCERTAIN category MUST NOT be rendered as though USED in any of\n"
            "the four anchor outputs.",
            "",
        )
        violations = cpap.lint_text(bad)
        self.assertTrue(
            any("MUST NOT" in v for v in violations),
            msg=f"expected forbiddance-token violation; got {violations}",
        )

    def test_partial_keyword_loss_still_fails(self) -> None:
        # Inverse mutation: keep the prohibition sentence but drop the
        # "auto-promotion" anchor heading. The lint should still fail
        # because both tokens are load-bearing.
        bad = _GOOD_PROTOCOL.replace("auto-promotion forbiddance", "(removed clause)")
        bad = bad.replace("Auto-promotion forbiddance", "Removed clause")
        violations = cpap.lint_text(bad)
        self.assertTrue(
            any("auto-promotion" in v for v in violations),
            msg=f"expected auto-promotion-token violation; got {violations}",
        )

    def test_concern_number_boundary_matching(self) -> None:
        # Codex round-5 P2 #3 closure: removing `concern #1` from a doc that
        # still mentions `concern #10` and `concern #11` should still fail.
        # Previous substring-membership check would let the document pass.
        bad = _GOOD_PROTOCOL.replace("concern #1 —", "deleted-clause —", 1)
        # Confirm the bad text still contains concern #10 / #11
        self.assertIn("concern #10", bad)
        self.assertIn("concern #11", bad)
        violations = cpap.lint_text(bad)
        self.assertTrue(
            any("concern #1 " in v or "concern #1\b" in v.lower() for v in violations),
            msg=f"expected concern #1 violation; got {violations}",
        )

    def test_missing_dedup_pointer_fails(self) -> None:
        bad = _GOOD_PROTOCOL.replace("shared/policy_data/nature_policy.md", "elsewhere.md")
        violations = cpap.lint_text(bad)
        self.assertTrue(
            any("nature_policy.md" in v or "dedup" in v.lower() for v in violations),
            msg=f"expected dedup pointer violation; got {violations}",
        )

    def test_missing_anchor_slug_fails(self) -> None:
        # Codex round-6 P2 #2 closure: dropping slug from the
        # **Anchor inventory** line must fail even if the slug name
        # appears elsewhere (e.g., in a per-anchor render section).
        bad = _GOOD_PROTOCOL.replace(
            "**Anchor inventory**: `prisma-trAIce, icmje, nature, ieee`",
            "**Anchor inventory**: `icmje, nature, ieee`",
        )
        # Add a stray prisma-trAIce mention to confirm the inventory check
        # is strict (the global substring would catch this and pass).
        bad += "\n\nNote: prisma-trAIce renders are mentioned in §3.1.\n"
        violations = cpap.lint_text(bad)
        self.assertTrue(
            any("prisma-trAIce" in v or "anchor slug" in v.lower() for v in violations),
            msg=f"expected anchor slug violation; got {violations}",
        )

    def test_missing_anchor_inventory_line_fails(self) -> None:
        bad = _GOOD_PROTOCOL.replace(
            "**Anchor inventory**: `prisma-trAIce, icmje, nature, ieee`",
            "(inventory line removed)",
        )
        violations = cpap.lint_text(bad)
        self.assertTrue(
            any("Anchor inventory" in v for v in violations),
            msg=f"expected Anchor inventory violation; got {violations}",
        )

    def test_extra_anchor_in_inventory_fails(self) -> None:
        # Codex round-7 P3 #2 closure: inventory advertising a slug
        # outside the canonical closed enum (e.g., `cope`) must fail.
        # Previously the lint only checked presence, not extras.
        bad = _GOOD_PROTOCOL.replace(
            "**Anchor inventory**: `prisma-trAIce, icmje, nature, ieee`",
            "**Anchor inventory**: `prisma-trAIce, icmje, nature, ieee, cope`",
        )
        violations = cpap.lint_text(bad)
        self.assertTrue(
            any("cope" in v and "unexpected" in v for v in violations),
            msg=f"expected unexpected-anchor violation; got {violations}",
        )


class CheckPolicyAnchorProtocolInvariantTest(unittest.TestCase):
    def test_invariant_names_count(self) -> None:
        self.assertEqual(len(cpap.REQUIRED_INVARIANTS), 8)

    def test_concern_count(self) -> None:
        self.assertEqual(len(cpap.REQUIRED_CONCERNS), 11)


if __name__ == "__main__":
    unittest.main()
