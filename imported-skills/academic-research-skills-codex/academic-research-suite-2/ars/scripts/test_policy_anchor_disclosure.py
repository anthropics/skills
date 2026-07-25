#!/usr/bin/env python3
"""#108 policy-anchor disclosure renderer conformance tests.

Reference impl: scripts/policy_anchor_disclosure_referee.py

The referee is an executable specification of the disclosure decision
logic encoded in policy_anchor_disclosure_protocol.md §2 (G10 7-row
table) and §4 (auto-promotion forbiddance). It is not the production
runtime — production is LLM-prose at execution time — but it provides
deterministic conformance testing that fails when the protocol doc and
the reference impl drift.

Each test asserts (input → expected G10 row decision + acceptable per-
facet annotation). Negative tests assert forbidden behaviors (auto-
promote UNCERTAIN, silent venue+anchor precedence, etc.) raise the
expected error.

Cross-reference: impl spec §3 (resolved-paths table), §4 (TDD discipline),
§6 (test count expectation).
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))

import policy_anchor_disclosure_referee as referee  # noqa: E402


# Convenience constructors mirroring referee.RendererInput shape.
# Default policy_anchor='icmje' so existing tests still pass without
# extra wiring; tests that exercise the unset-selector path supply
# policy_anchor=None explicitly.
def _inp(
    *,
    ai_used=None,
    categories=None,
    policy_anchor="icmje",
    venue=None,
    slr_lineage=False,
    mode_param=None,
    tool_type="LLM",
    methodological_in_slr=True,
    level_of_involvement=None,
    affected_sections=None,
):
    return referee.RendererInput(
        ai_used=ai_used,
        categories=categories or {},
        policy_anchor=policy_anchor,
        venue=venue,
        slr_lineage=slr_lineage,
        mode_param=mode_param,
        tool_type=tool_type,
        methodological_in_slr=methodological_in_slr,
        level_of_involvement=level_of_involvement,
        affected_sections=affected_sections,
    )


# ============================================================================
# §3 G10 7-row precedence table — positive fixtures per row
# ============================================================================
class G10PrecedenceTableTest(unittest.TestCase):
    def test_row_1_ai_used_false_with_used_category_emits_conflict_annotation(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(ai_used=False, categories={"drafting": "USED"})
        )
        self.assertEqual(result.row, 1)
        self.assertEqual(result.kind, "conflict_annotation")

    def test_row_2_ai_used_false_clean_no_used_no_uncertain_emits_no_ai_statement(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(ai_used=False, categories={"drafting": "NOT USED", "revision": "NOT USED"})
        )
        self.assertEqual(result.row, 2)
        self.assertEqual(result.kind, "no_ai_statement")

    def test_row_3_ai_used_false_with_uncertain_no_used_emits_tension_annotation(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(ai_used=False, categories={"drafting": "UNCERTAIN"})
        )
        self.assertEqual(result.row, 3)
        self.assertEqual(result.kind, "tension_annotation")

    def test_row_4_ai_used_true_with_used_full_anchor_render(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(ai_used=True, categories={"drafting": "USED"})
        )
        self.assertEqual(result.row, 4)
        self.assertEqual(result.kind, "anchor_render")

    def test_row_4_used_category_without_ai_used_flag_full_anchor_render(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(ai_used=None, categories={"drafting": "USED"})
        )
        self.assertEqual(result.row, 4)
        self.assertEqual(result.kind, "anchor_render")

    def test_row_5_uncertain_no_used_no_flag_emits_not_supplied_annotation(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(ai_used=None, categories={"drafting": "UNCERTAIN"})
        )
        self.assertEqual(result.row, 5)
        self.assertEqual(result.kind, "not_supplied_annotation")

    def test_row_6_all_not_used_no_uncertain_no_flag_silent(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(ai_used=None, categories={"drafting": "NOT USED", "revision": "NOT USED"})
        )
        self.assertEqual(result.row, 6)
        self.assertEqual(result.kind, "silence")

    def test_row_7_empty_input_emits_cold_start_annotation(self) -> None:
        result = referee.decide_disclosure_output(_inp(ai_used=None, categories={}))
        self.assertEqual(result.row, 7)
        self.assertEqual(result.kind, "not_supplied_annotation")


# ============================================================================
# §4 Auto-promotion forbiddance — load-bearing negative tests
# ============================================================================
class AutoPromotionForbiddanceTest(unittest.TestCase):
    def test_uncertain_never_rendered_as_used_in_row_4(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "USED", "revision": "UNCERTAIN"},
            )
        )
        self.assertEqual(result.row, 4)
        # USED facet at full strength
        self.assertIn("drafting", result.used_facets)
        # UNCERTAIN facet annotated, never promoted
        self.assertIn("revision", result.uncertain_facets)
        self.assertNotIn("revision", result.used_facets)

    def test_explicit_promote_raises(self) -> None:
        with self.assertRaises(referee.AutoPromotionForbidden):
            referee.render_facet_as_used(category_state="UNCERTAIN")


# ============================================================================
# §4.3 G1 invariant — no entry-level field touched
# ============================================================================
class G1InvariantTest(unittest.TestCase):
    def test_referee_does_not_read_corpus_entry_field(self) -> None:
        # The referee receives flat input; assert the dataclass has no
        # 'corpus_entry_ai_disclosure' (the would-be entry-level field).
        fields = {f.name for f in referee.RendererInput.__dataclass_fields__.values()}
        self.assertNotIn("corpus_entry_ai_disclosure", fields)
        self.assertNotIn("ai_disclosure", fields)


# ============================================================================
# §4.3 G2 invariant — track gate by slr_lineage
# ============================================================================
class G2InvariantTest(unittest.TestCase):
    def test_prisma_track_requires_slr_lineage(self) -> None:
        # slr_lineage=False with --policy-anchor=prisma-trAIce → rejected
        with self.assertRaises(referee.TrackGateError):
            referee.decide_disclosure_output(
                _inp(
                    ai_used=True,
                    categories={"drafting": "USED"},
                    policy_anchor="prisma-trAIce",
                    slr_lineage=False,
                )
            )

    def test_prisma_track_with_lineage_passes(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "USED"},
                policy_anchor="prisma-trAIce",
                slr_lineage=True,
            )
        )
        self.assertEqual(result.row, 4)

    def test_cold_start_mode_param_substitutes_lineage(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "USED"},
                policy_anchor="prisma-trAIce",
                slr_lineage=False,
                mode_param="systematic-review",
            )
        )
        self.assertEqual(result.row, 4)


# ============================================================================
# §4.3 G5 invariant — three-gate composition for M6 prompt disclosure
# ============================================================================
class G5InvariantTest(unittest.TestCase):
    def test_prompt_disclosure_fires_when_all_three_gates_hold(self) -> None:
        self.assertTrue(
            referee.prompt_disclosure_required(
                track="prisma-trAIce",
                tool_type="LLM",
                methodological_in_slr=True,
            )
        )

    def test_prompt_disclosure_skipped_when_not_prisma_track(self) -> None:
        self.assertFalse(
            referee.prompt_disclosure_required(
                track="icmje",
                tool_type="LLM",
                methodological_in_slr=True,
            )
        )

    def test_prompt_disclosure_skipped_when_non_llm_tool(self) -> None:
        self.assertFalse(
            referee.prompt_disclosure_required(
                track="prisma-trAIce",
                tool_type="symbolic-solver",
                methodological_in_slr=True,
            )
        )

    def test_prompt_disclosure_skipped_when_copyediting_only(self) -> None:
        self.assertFalse(
            referee.prompt_disclosure_required(
                track="prisma-trAIce",
                tool_type="LLM",
                methodological_in_slr=False,
            )
        )


# ============================================================================
# §4.3 G7 invariant — anchor-specific carve-out semantics
# ============================================================================
class G7InvariantTest(unittest.TestCase):
    def test_nature_carveout_eliminates(self) -> None:
        sem = referee.copyediting_carveout_semantics("nature")
        self.assertEqual(sem, "eliminate")

    def test_ieee_carveout_downgrades(self) -> None:
        sem = referee.copyediting_carveout_semantics("ieee")
        self.assertEqual(sem, "downgrade")

    def test_prisma_carveout_out_of_scope(self) -> None:
        sem = referee.copyediting_carveout_semantics("prisma-trAIce")
        self.assertEqual(sem, "out_of_scope")

    def test_icmje_carveout_not_addressed(self) -> None:
        sem = referee.copyediting_carveout_semantics("icmje")
        self.assertEqual(sem, "not_addressed")


# ============================================================================
# §4.3 G8 invariant — IEEE #5 + #6 paired mandate
# ============================================================================
class G8InvariantTest(unittest.TestCase):
    def test_ieee_render_requires_both_level_and_sections(self) -> None:
        with self.assertRaises(referee.PairedMandateViolation):
            referee.assert_ieee_pairing_conformant(
                level_of_involvement="full drafting",
                affected_sections=None,
            )

    def test_ieee_render_requires_level_when_sections_present(self) -> None:
        with self.assertRaises(referee.PairedMandateViolation):
            referee.assert_ieee_pairing_conformant(
                level_of_involvement=None,
                affected_sections=["Methods"],
            )

    def test_ieee_render_passes_when_both_present(self) -> None:
        # Should not raise
        referee.assert_ieee_pairing_conformant(
            level_of_involvement="full drafting",
            affected_sections=["Methods"],
        )

    def test_ieee_row_4_render_enforces_pairing(self) -> None:
        # Codex round-3 P2 #1 closure: previously row 4 returned
        # anchor_render for IEEE even when only level_of_involvement was
        # supplied (no affected_sections). The decision function must
        # raise PairedMandateViolation in that case.
        with self.assertRaises(referee.PairedMandateViolation):
            referee.decide_disclosure_output(
                _inp(
                    ai_used=True,
                    categories={"drafting": "USED"},
                    policy_anchor="ieee",
                    level_of_involvement="full drafting",
                    # affected_sections=None
                )
            )

    def test_ieee_row_4_render_passes_when_both_inputs_present(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "USED"},
                policy_anchor="ieee",
                level_of_involvement="full drafting",
                affected_sections=["Methods"],
            )
        )
        self.assertEqual(result.row, 4)
        self.assertEqual(result.kind, "anchor_render")

    def test_ieee_row_4_render_passes_when_neither_pairing_input_present(self) -> None:
        # When neither IEEE-pairing input is supplied, the renderer still
        # proceeds — the missing pairing surfaces as a per-facet "not
        # supplied" annotation downstream (per protocol §3.4); it is not
        # a hard violation at the decision-table level.
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "USED"},
                policy_anchor="ieee",
                level_of_involvement=None,
                affected_sections=None,
            )
        )
        self.assertEqual(result.row, 4)
        self.assertEqual(result.kind, "anchor_render")


# ============================================================================
# §4.3 G9 invariant — anchor-specific image-rights regimes
# ============================================================================
class G9InvariantTest(unittest.TestCase):
    def test_anchor_image_regimes_are_distinct(self) -> None:
        nature = referee.image_rights_regime("nature")
        ieee = referee.image_rights_regime("ieee")
        icmje = referee.image_rights_regime("icmje")
        prisma = referee.image_rights_regime("prisma-trAIce")
        # All four distinct (not unified)
        self.assertEqual(len({nature, ieee, icmje, prisma}), 4)

    def test_nature_regime_is_default_deny(self) -> None:
        self.assertEqual(referee.image_rights_regime("nature"), "default_deny_with_carveouts")

    def test_ieee_regime_folds_into_acknowledgments(self) -> None:
        self.assertEqual(referee.image_rights_regime("ieee"), "acknowledgments_only")


# ============================================================================
# §4.4 #1 — slr_lineage signal, no upstream chasing
# ============================================================================
class Concern1Test(unittest.TestCase):
    def test_slr_lineage_input_directly_drives_track(self) -> None:
        # Even with origin_mode=full, slr_lineage=true routes to prisma-trAIce
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "USED"},
                policy_anchor="prisma-trAIce",
                slr_lineage=True,
            )
        )
        self.assertEqual(result.row, 4)
        self.assertEqual(result.track, "prisma-trAIce")


# ============================================================================
# §4.4 #5 — Nature hybrid image output channel
# ============================================================================
class Concern5Test(unittest.TestCase):
    def test_nature_image_render_emits_two_channels(self) -> None:
        outputs = referee.nature_image_outputs(
            images=[{"id": "fig1", "ai_generated": True}],
        )
        self.assertIn("annotation_block", outputs)
        self.assertIn("suggested_patch", outputs)
        # ARS does not modify manuscript source autonomously
        self.assertNotIn("inline_modification", outputs)


# ============================================================================
# §4.4 #6 — UNCERTAIN per-facet annotation
# ============================================================================
class Concern6Test(unittest.TestCase):
    def test_used_and_uncertain_mix_renders_used_with_uncertain_annotation(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=None,
                categories={
                    "drafting": "USED",
                    "revision": "UNCERTAIN",
                    "citation_check": "USED",
                },
            )
        )
        self.assertEqual(result.row, 4)
        self.assertSetEqual(set(result.used_facets), {"drafting", "citation_check"})
        self.assertSetEqual(set(result.uncertain_facets), {"revision"})


# ============================================================================
# §4.4 #7 — venue+anchor conflict resolution
# ============================================================================
class Concern7Test(unittest.TestCase):
    def test_consistent_nature_pair_passes(self) -> None:
        # --venue=Nature + --policy-anchor=nature is consistent
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "USED"},
                policy_anchor="nature",
                venue="Nature",
            )
        )
        self.assertEqual(result.row, 4)

    def test_conflicting_pair_rejected(self) -> None:
        with self.assertRaises(referee.VenueAnchorConflict):
            referee.decide_disclosure_output(
                _inp(
                    ai_used=True,
                    categories={"drafting": "USED"},
                    policy_anchor="ieee",
                    venue="Nature",
                )
            )

    def test_unmapped_venue_with_anchor_rejected(self) -> None:
        # Codex round-1 P2 #2 closure: unmapped venue (ICLR) with anchor
        # must reject, not silently fall through.
        with self.assertRaises(referee.VenueAnchorConflict):
            referee.decide_disclosure_output(
                _inp(
                    ai_used=True,
                    categories={"drafting": "USED"},
                    policy_anchor="ieee",
                    venue="ICLR",
                )
            )

    def test_nature_spelling_variant_with_non_nature_anchor_rejected(self) -> None:
        # Codex round-1 P2 #2 secondary case: even a Nature-shaped venue
        # string outside the canonical set must reject when paired with a
        # non-nature anchor.
        with self.assertRaises(referee.VenueAnchorConflict):
            referee.decide_disclosure_output(
                _inp(
                    ai_used=True,
                    categories={"drafting": "USED"},
                    policy_anchor="ieee",
                    venue="Nature (Nature Publishing Group)",
                )
            )

    def test_nature_db_label_with_nature_anchor_passes(self) -> None:
        # Codex round-2 P2 #1 closure: the v3.2 venue_disclosure_policies
        # entry uses "Nature (Nature Publishing Group)" as its label.
        # That exact string + policy_anchor='nature' must be treated as a
        # consistent pair (not raised). Without this, every author using
        # the existing policy database name would be blocked.
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "USED"},
                policy_anchor="nature",
                venue="Nature (Nature Publishing Group)",
            )
        )
        self.assertEqual(result.row, 4)


# ============================================================================
# Category state enum validation (codex round-2 P2 #2)
# ============================================================================
class CategoryStateEnumValidationTest(unittest.TestCase):
    def test_lowercase_used_raises(self) -> None:
        with self.assertRaises(referee.InvalidCategoryState):
            referee.decide_disclosure_output(
                _inp(ai_used=None, categories={"drafting": "used"})
            )

    def test_typo_category_state_raises(self) -> None:
        with self.assertRaises(referee.InvalidCategoryState):
            referee.decide_disclosure_output(
                _inp(ai_used=None, categories={"drafting": "USE D"})
            )

    def test_valid_states_pass(self) -> None:
        # All three canonical states pass without raising; smoke check.
        for state in ("USED", "NOT USED", "UNCERTAIN"):
            referee.decide_disclosure_output(
                _inp(ai_used=None, categories={"drafting": state})
            )


# ============================================================================
# Selector-unsupplied + venue-only paths (codex round-4 P2 #2)
# ============================================================================
class SelectorUnsuppliedTest(unittest.TestCase):
    def test_no_selector_at_all_raises(self) -> None:
        with self.assertRaises(referee.SelectorUnsupplied):
            referee.decide_disclosure_output(
                _inp(ai_used=None, categories={}, policy_anchor=None, venue=None)
            )

    def test_venue_only_delegates_to_venue_path(self) -> None:
        # Codex round-4 P2 #2: RendererInput(venue="ICLR", policy_anchor=None)
        # used to default policy_anchor to "icmje" and produce a conflict
        # error. Now the referee delegates the venue-only case to v3.2.
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "USED"},
                policy_anchor=None,
                venue="ICLR",
            )
        )
        self.assertEqual(result.row, 0)
        self.assertEqual(result.kind, "delegated_to_venue_path")
        self.assertEqual(result.track, "ICLR")


# ============================================================================
# Nature Portfolio venue variants (codex round-4 P2 #3)
# ============================================================================
class NaturePortfolioVariantTest(unittest.TestCase):
    def test_nature_medicine_with_nature_anchor_passes(self) -> None:
        # Codex round-4 P2 #3: Nature Portfolio journals (Nature Medicine,
        # Nature Climate Change, Nature Communications, …) all inherit
        # the parent Nature AI policy. Pairing any of them with
        # policy_anchor='nature' is a consistent pair, not a conflict.
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "USED"},
                policy_anchor="nature",
                venue="Nature Medicine",
            )
        )
        self.assertEqual(result.row, 4)

    def test_nature_communications_with_nature_anchor_passes(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "USED"},
                policy_anchor="nature",
                venue="Nature Communications",
            )
        )
        self.assertEqual(result.row, 4)

    def test_unrelated_journal_with_nature_anchor_still_rejects(self) -> None:
        # Non-Nature-prefixed venue + nature anchor remains a conflict.
        with self.assertRaises(referee.VenueAnchorConflict):
            referee.decide_disclosure_output(
                _inp(
                    ai_used=True,
                    categories={"drafting": "USED"},
                    policy_anchor="nature",
                    venue="Cell",
                )
            )

    def test_helper_returns_true_for_canonical_names(self) -> None:
        for v in referee.NATURE_VENUE_NAMES:
            self.assertTrue(referee.is_nature_portfolio_venue(v))

    def test_helper_returns_true_for_prefix_journals(self) -> None:
        for v in ("Nature Medicine", "Nature Climate Change", "Nature Energy"):
            self.assertTrue(referee.is_nature_portfolio_venue(v))

    def test_helper_returns_false_for_unrelated_journals(self) -> None:
        for v in ("Science", "Cell", "PLOS ONE", "Nature"):
            self.assertEqual(
                referee.is_nature_portfolio_venue(v),
                v in referee.NATURE_VENUE_NAMES,
                msg=f"{v} miscategorized",
            )


# ============================================================================
# Policy anchor enum validation (codex round-1 P2 #3)
# ============================================================================
class PolicyAnchorEnumValidationTest(unittest.TestCase):
    def test_typo_anchor_value_raises(self) -> None:
        with self.assertRaises(referee.InvalidPolicyAnchor):
            referee.decide_disclosure_output(
                _inp(
                    ai_used=True,
                    categories={"drafting": "USED"},
                    policy_anchor="ICMJE",  # uppercase typo
                )
            )

    def test_unknown_anchor_value_raises(self) -> None:
        with self.assertRaises(referee.InvalidPolicyAnchor):
            referee.decide_disclosure_output(
                _inp(
                    ai_used=True,
                    categories={"drafting": "USED"},
                    policy_anchor="cope",  # not in canonical 4
                )
            )


# ============================================================================
# §4.4 #10 — ai_used:true substantive-content gate
# ============================================================================
class Concern10Test(unittest.TestCase):
    def test_bare_ai_used_true_no_categories_triggers_categorization_flow(self) -> None:
        result = referee.decide_disclosure_output(
            _inp(ai_used=True, categories={})
        )
        # Should trigger v3.2 categorization flow, not full anchor render
        self.assertEqual(result.kind, "prompt_for_categorization")

    def test_bare_ai_used_true_all_not_used_triggers_categorization_flow(self) -> None:
        # ai_used=true contradicts everything-NOT-USED; row 1 doesn't apply
        # (row 1 needs USED) → caught by concern #10 gate. Codex round-5
        # P2 #2: protocol §3 G10 row 4 sub-gate spec extended to cover
        # this case (was bare-flag only previously). Referee already
        # handled it correctly; protocol doc now aligned.
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "NOT USED", "revision": "NOT USED"},
            )
        )
        self.assertEqual(result.kind, "prompt_for_categorization")

    def test_ai_used_true_with_uncertain_only_triggers_categorization(self) -> None:
        # Edge case from round-5 P2 #2: ai_used=true + only UNCERTAIN
        # categories should also trigger categorization flow rather than
        # a row-4 render (no USED facets means no substantive content).
        result = referee.decide_disclosure_output(
            _inp(
                ai_used=True,
                categories={"drafting": "UNCERTAIN"},
            )
        )
        self.assertEqual(result.kind, "prompt_for_categorization")


# ============================================================================
# §4.4 #11 — G1 invariant scope narrowing (data layer untouched, plumbing OK)
# ============================================================================
class Concern11Test(unittest.TestCase):
    def test_renderer_input_excludes_corpus_entry_fields(self) -> None:
        fields = {f.name for f in referee.RendererInput.__dataclass_fields__.values()}
        # No field that would be a "corpus-entry" addition
        for forbidden in ("corpus_entry_id", "corpus_entry_ai_disclosure", "literature_corpus"):
            self.assertNotIn(forbidden, fields)

    def test_plumbing_inputs_are_runtime_signals(self) -> None:
        # slr_lineage + mode_param are runtime renderer inputs, not entry-level
        fields = {f.name for f in referee.RendererInput.__dataclass_fields__.values()}
        self.assertIn("slr_lineage", fields)
        self.assertIn("mode_param", fields)


if __name__ == "__main__":
    unittest.main()
