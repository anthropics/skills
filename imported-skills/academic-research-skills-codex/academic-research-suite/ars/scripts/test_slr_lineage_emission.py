#!/usr/bin/env python3
"""#111 slr_lineage emission conformance tests.

Tests the pipeline plumbing that lets `disclosure --policy-anchor=prisma-trAIce`
dispatch automatically after `deep-research systematic-review → academic-paper
full` runs, per the documented handoff path in
`policy_anchor_disclosure_protocol.md` §3.1.

Two layers under test:

1. Resolution helper (`scripts/slr_lineage.py`) — pure function over a
   `state_tracker.stages` snapshot. Returns `True` iff any stage was
   produced by deep-research in systematic-review mode.

2. Renderer integration — a passport carrying `slr_lineage=True` passes
   the §4.3 G2 invariant gate without a manual `mode_param='systematic-
   review'` supplied at cold-start.

Design doc: `docs/design/2026-05-15-issue-111-slr-lineage-emission-design.md`.
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))

import policy_anchor_disclosure_referee as referee  # noqa: E402
import slr_lineage  # noqa: E402


# ============================================================================
# §1 Resolution helper — `slr_lineage.resolve_from_stages`
# ============================================================================
class ResolveFromStagesTest(unittest.TestCase):
    """Helper computes `slr_lineage` from a `state_tracker.stages` dict.

    Contract (per design §4.2): `slr_lineage` is True iff any stage in
    the run history has `skill == 'deep-research'` AND
    `mode == 'systematic-review'`. Run-level provenance, not per-artifact.
    """

    def test_systematic_review_stage_present_returns_true(self) -> None:
        stages = {
            "1": {"skill": "deep-research", "mode": "systematic-review"},
            "2": {"skill": "academic-paper", "mode": "full"},
        }
        self.assertTrue(slr_lineage.resolve_from_stages(stages))

    def test_no_systematic_review_returns_false(self) -> None:
        stages = {
            "1": {"skill": "deep-research", "mode": "full"},
            "2": {"skill": "academic-paper", "mode": "full"},
        }
        self.assertFalse(slr_lineage.resolve_from_stages(stages))

    def test_mid_entry_no_stage_1_returns_false(self) -> None:
        """Mid-entry from Stage 2 (user brings their own paper) has no
        Stage 1 evidence — SLR cannot be inferred."""
        stages = {
            "2": {"skill": "academic-paper", "mode": "full"},
            "2.5": {"agent": "integrity_verification_agent", "mode": "pre-review"},
        }
        self.assertFalse(slr_lineage.resolve_from_stages(stages))

    def test_empty_stages_returns_false(self) -> None:
        self.assertFalse(slr_lineage.resolve_from_stages({}))

    def test_slr_mode_alias_accepted(self) -> None:
        """The `SLR_MODES` enum at the renderer side accepts both
        'systematic-review' and 'slr'. The resolver must match the same
        set so symmetric values don't silently fall through."""
        stages = {"1": {"skill": "deep-research", "mode": "slr"}}
        self.assertTrue(slr_lineage.resolve_from_stages(stages))

    def test_non_deep_research_systematic_review_ignored(self) -> None:
        """A non-deep-research stage carrying mode='systematic-review'
        (hypothetically a future skill) must not trigger SLR lineage —
        the contract is bound to deep-research lineage specifically."""
        stages = {
            "1": {"skill": "academic-paper", "mode": "systematic-review"},
        }
        self.assertFalse(slr_lineage.resolve_from_stages(stages))

    def test_stage_without_mode_skipped(self) -> None:
        """A stage entry missing `mode` (e.g., skipped Stage 4') must
        not raise — the resolver treats missing/None as not-SLR."""
        stages = {
            "1": {"skill": "deep-research"},
            "4p": {"skill": "academic-paper", "mode": None, "status": "skipped"},
        }
        self.assertFalse(slr_lineage.resolve_from_stages(stages))


# ============================================================================
# §2 Renderer integration — passport with slr_lineage=True dispatches
# ============================================================================
class RendererIntegrationTest(unittest.TestCase):
    """Passport carrying `slr_lineage=True` passes G2 track gate without
    cold-start `mode_param` supplied. Mirror of the documented
    `deep-research systematic-review → academic-paper full → disclosure`
    auto-dispatch path."""

    def _inp(self, *, slr_lineage=False, mode_param=None):
        return referee.RendererInput(
            ai_used=True,
            categories={"drafting": "USED"},
            policy_anchor="prisma-trAIce",
            venue=None,
            slr_lineage=slr_lineage,
            mode_param=mode_param,
        )

    def test_pipeline_emitted_slr_lineage_dispatches_without_mode_param(self) -> None:
        """Acceptance criterion #3 (positive): SLR pipeline passport
        carries `slr_lineage=True`, disclosure renderer fires without
        G2 TrackGateError and without the user supplying mode_param."""
        result = referee.decide_disclosure_output(
            self._inp(slr_lineage=True, mode_param=None)
        )
        self.assertEqual(result.row, 4)
        self.assertEqual(result.kind, "anchor_render")
        self.assertEqual(result.track, "prisma-trAIce")

    def test_non_slr_pipeline_passport_still_blocks_prisma_track(self) -> None:
        """Negative: non-SLR pipeline (e.g., deep-research full mode)
        produces `slr_lineage=False`. The renderer still refuses
        --policy-anchor=prisma-trAIce per G2 invariant — no behavior
        change for non-SLR paths."""
        with self.assertRaises(referee.TrackGateError):
            referee.decide_disclosure_output(
                self._inp(slr_lineage=False, mode_param=None)
            )

    def test_pre_111_passport_with_mode_param_dispatches_cold_start(self) -> None:
        """Pre-#111 passports lack the `slr_lineage` field (absence = False).
        Cold-start path requires explicit `mode_param='systematic-review'`,
        which dispatches anchor_render as before. The block-on-missing-signal
        side of this contract is covered by
        `test_non_slr_pipeline_passport_still_blocks_prisma_track`."""
        result = referee.decide_disclosure_output(
            self._inp(slr_lineage=False, mode_param="systematic-review")
        )
        self.assertEqual(result.row, 4)
        self.assertEqual(result.kind, "anchor_render")


# ============================================================================
# §3 End-to-end: stages → resolver → passport-shape → renderer
# ============================================================================
class EndToEndPipelineHandoffTest(unittest.TestCase):
    """Exercises the full handoff: state_tracker.stages snapshot →
    resolver → outgoing passport → renderer accepts prisma-trAIce."""

    def test_slr_pipeline_full_handoff_dispatches(self) -> None:
        stages = {
            "1": {"skill": "deep-research", "mode": "systematic-review"},
            "2": {"skill": "academic-paper", "mode": "full"},
        }
        outgoing_passport_slr = slr_lineage.resolve_from_stages(stages)
        self.assertTrue(outgoing_passport_slr)

        ri = referee.RendererInput(
            ai_used=True,
            categories={"drafting": "USED"},
            policy_anchor="prisma-trAIce",
            slr_lineage=outgoing_passport_slr,
        )
        result = referee.decide_disclosure_output(ri)
        self.assertEqual(result.kind, "anchor_render")
        self.assertEqual(result.track, "prisma-trAIce")

    def test_non_slr_pipeline_handoff_blocks(self) -> None:
        stages = {
            "1": {"skill": "deep-research", "mode": "full"},
            "2": {"skill": "academic-paper", "mode": "full"},
        }
        outgoing_passport_slr = slr_lineage.resolve_from_stages(stages)
        self.assertFalse(outgoing_passport_slr)

        ri = referee.RendererInput(
            ai_used=True,
            categories={"drafting": "USED"},
            policy_anchor="prisma-trAIce",
            slr_lineage=outgoing_passport_slr,
        )
        with self.assertRaises(referee.TrackGateError):
            referee.decide_disclosure_output(ri)


# ============================================================================
# §4 Monotonic OR — preserve already-persisted slr_lineage across resume
# ============================================================================
class EmitMonotonicOrTest(unittest.TestCase):
    """Codex round-1 [P2]: a `resume_from_passport=<hash>` session has an
    empty `state_tracker.stages` (reconstructed from ledger only); recomputing
    `slr_lineage` from stages alone would overwrite a persisted `true` and
    defeat #111's auto-dispatch goal. The OR wrapper preserves any already-
    persisted lineage signal."""

    def test_resume_preserves_true_when_stages_empty(self) -> None:
        # Empty stages (fresh resume), but passport already carries the SLR signal
        self.assertTrue(slr_lineage.emit({}, incoming_slr_lineage=True))

    def test_in_session_new_slr_flips_false_to_true(self) -> None:
        stages = {"1": {"skill": "deep-research", "mode": "systematic-review"}}
        self.assertTrue(slr_lineage.emit(stages, incoming_slr_lineage=False))

    def test_no_evidence_anywhere_returns_false(self) -> None:
        # Empty stages + no incoming signal = honest false
        self.assertFalse(slr_lineage.emit({}, incoming_slr_lineage=False))

    def test_none_incoming_treated_as_false(self) -> None:
        """Pre-#111 passport (incoming field absent / None) + non-SLR stages
        = false, identical to pre-#111 behavior."""
        stages = {"1": {"skill": "deep-research", "mode": "full"}}
        self.assertFalse(slr_lineage.emit(stages, incoming_slr_lineage=None))

    def test_default_incoming_is_none_safe(self) -> None:
        """Default arg ergonomics: omitting incoming_slr_lineage should not
        crash and should treat it as no-prior-signal."""
        stages = {"1": {"skill": "deep-research", "mode": "systematic-review"}}
        self.assertTrue(slr_lineage.emit(stages))


if __name__ == "__main__":
    unittest.main()
