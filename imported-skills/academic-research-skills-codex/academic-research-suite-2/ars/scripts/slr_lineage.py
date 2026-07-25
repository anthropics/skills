#!/usr/bin/env python3
"""#111 slr_lineage resolver — pure function over state_tracker.stages.

Pipeline plumbing helper for the `deep-research systematic-review →
academic-paper full → disclosure --policy-anchor=prisma-trAIce` auto-
dispatch path. The orchestrator persists the resolved value on the
Schema 9 Material Passport at the Stage 1 → Stage 2 handoff; the
disclosure renderer reads it back as `RendererInput.slr_lineage`.

Design: docs/design/2026-05-15-issue-111-slr-lineage-emission-design.md
Contract: policy_anchor_disclosure_protocol.md §3.1 (G2 invariant)
"""
from __future__ import annotations

from typing import Mapping

# Dual-path import: when this module is loaded via `from scripts.slr_lineage
# import emit` from the repo root (the namespace-package style used by
# test_check_sprint_contract.py, tests/test_helpers.py, etc.), the sibling import
# needs the `scripts.` prefix. When loaded via `import slr_lineage` after a
# sys.path.insert (the style used by scripts/test_slr_lineage_emission.py),
# the bare name works. Try the package form first; fall back to the sibling
# form. Either path resolves to the same module — single source of truth for
# SLR_MODES preserved.
try:
    from scripts.policy_anchor_disclosure_referee import SLR_MODES
except ImportError:
    from policy_anchor_disclosure_referee import SLR_MODES


def resolve_from_stages(stages: Mapping[str, Mapping]) -> bool:
    """Return True iff any stage was produced by deep-research in SLR mode.

    Run-level provenance: the contract is bound to deep-research lineage
    specifically, mirroring the §4.3 G2 invariant track gate. A
    non-deep-research stage with mode='systematic-review' does NOT
    trigger SLR lineage — only the documented producer counts.
    """
    return any(
        (stage.get("skill") == "deep-research")
        and (stage.get("mode") in SLR_MODES)
        for stage in stages.values()
    )


def emit(
    stages: Mapping[str, Mapping],
    incoming_slr_lineage: bool | None = None,
) -> bool:
    """Compute the outgoing passport's `slr_lineage` via monotonic OR.

    Resume-from-passport / mid-entry passports may already carry
    `slr_lineage: true` even when the live `state_tracker.stages` is
    empty (reconstructed from ledger only). Recomputing from stages
    alone would overwrite that signal and defeat the auto-dispatch
    goal. The OR preserves any prior signal; a true never flips back
    to false.
    """
    return bool(incoming_slr_lineage) or resolve_from_stages(stages)
