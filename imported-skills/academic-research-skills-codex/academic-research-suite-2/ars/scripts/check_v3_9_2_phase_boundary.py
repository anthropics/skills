#!/usr/bin/env python3
"""Static lint for ARS v3.9.2 phase boundary coverage (#133 hot-fix).

Spec: docs/design/2026-05-18-ars-v3.9.2-phase-boundary-spec.md Phase 5
Classification: docs/design/2026-05-18-ars-v3.9.2-agent-phase-classification.md

Enforces three invariants:

1. **Bucket A coverage** — all 23 single-phase agents MUST carry a
   `## Phase Boundary (v3.9.2)` or `## Phase Boundary (v3.9.4)` H2 block.

2. **Bucket B/C/D exclusion** — all 16 multi-phase / phase-orthogonal /
   cross-phase-meta agents MUST NOT carry the block. Adding a fence to
   these agents would either falsely block legitimate cross-phase work
   (Bucket B/C) or defeat orchestration (Bucket D).

3. **Block content shape** — each Bucket A block must contain the four
   load-bearing keywords/phrases that make the boundary detectable in
   prompt processing:
     - `Phase Boundary (v3.9.2)` or `Phase Boundary (v3.9.4)` (the H2 marker)
     - `MUST NOT` (the prohibition section)
     - `MAY READ` (the explicit upstream-read permission)
     - `Enforcement (v3.9.2)` or `Enforcement (v3.9.4)` (the trailing enforcement-paragraph marker)

   These are scoped to the Phase Boundary block itself (via H2 → next H2
   boundary), so the same keyword appearing elsewhere in the agent file
   does not count toward passing.

4. **Canonical enforcement sentence (#491 defrift lock)** — every Bucket A
   block's enforcement paragraph must carry the canonical sentence verbatim
   (version-matched to the block's v3.9.2/v3.9.4 marker; per-file tails
   AFTER the sentence stay free — formatter's v3.7.1 hard-gate note, the
   reviewers' Sprint Contract notes are legitimately file-specific). The
   previous copy ("hook deferred to v3.10 #134") went factually stale
   repo-wide with no lint noticing (audits/harness-retirement-2026-07-04.md
   B4-F01). Scope: the constant governs the Bucket A blocks only — the
   `agents/` mirrors follow mechanically via check_agents_mirror_sync.py,
   and the SKILL.md copies carry a different, shorter wording (separate
   surface). Update procedure: see the error message in check_bucket_a.

Falsifiability discipline (per feedback_lint_passes_but_prompt_silent.md):
keywords are scoped to the v3.9.2 block; bare keyword presence anywhere
in the agent file does NOT count. The block must include all four phrases
inside its own H2 span.

Exit codes: 0 on pass, 1 on any failure.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Bucket A — 23 single-phase agents that MUST have Phase Boundary block.
# Source: docs/design/2026-05-18-ars-v3.9.2-agent-phase-classification.md
BUCKET_A_AGENTS = [
    # deep-research/agents/ (10)
    "deep-research/agents/research_question_agent.md",
    "deep-research/agents/research_architect_agent.md",
    "deep-research/agents/bibliography_agent.md",
    "deep-research/agents/source_verification_agent.md",
    "deep-research/agents/synthesis_agent.md",
    "deep-research/agents/timeline_extraction_agent.md",  # v3.9.4 Phase 2 sibling
    "deep-research/agents/editor_in_chief_agent.md",
    "deep-research/agents/ethics_review_agent.md",
    "deep-research/agents/risk_of_bias_agent.md",
    "deep-research/agents/meta_analysis_agent.md",
    # academic-paper/agents/ (7)
    "academic-paper/agents/literature_strategist_agent.md",
    "academic-paper/agents/structure_architect_agent.md",
    "academic-paper/agents/draft_writer_agent.md",
    "academic-paper/agents/citation_compliance_agent.md",
    "academic-paper/agents/abstract_bilingual_agent.md",
    "academic-paper/agents/peer_reviewer_agent.md",
    "academic-paper/agents/formatter_agent.md",
    # academic-paper-reviewer/agents/ (6)
    "academic-paper-reviewer/agents/eic_agent.md",
    "academic-paper-reviewer/agents/methodology_reviewer_agent.md",
    "academic-paper-reviewer/agents/domain_reviewer_agent.md",
    "academic-paper-reviewer/agents/perspective_reviewer_agent.md",
    "academic-paper-reviewer/agents/devils_advocate_reviewer_agent.md",
    "academic-paper-reviewer/agents/editorial_synthesizer_agent.md",
]

# Buckets B/C/D — 16 agents that MUST NOT have the block.
# B (4): multi-phase; C (8): phase-orthogonal; D (4): cross-phase-meta.
BUCKET_BCD_AGENTS = [
    # Bucket B — multi-phase (4)
    "deep-research/agents/devils_advocate_agent.md",          # P1, 3, 5 + Socratic L2, 4
    "deep-research/agents/report_compiler_agent.md",          # P4, 6
    "academic-paper/agents/argument_builder_agent.md",        # P3 + Plan Step 3
    "academic-paper/agents/visualization_agent.md",           # P4 + P7
    # Bucket C — phase-orthogonal (8)
    "deep-research/agents/socratic_mentor_agent.md",          # Socratic Layer 1-5
    "academic-paper/agents/socratic_mentor_agent.md",         # Plan Step 0-3
    "deep-research/agents/monitoring_agent.md",               # post-pipeline
    "academic-paper/agents/revision_coach_agent.md",          # Revision-Coach standalone
    "academic-pipeline/agents/integrity_verification_agent.md",  # Stage 2.5 / 4.5 gates
    "academic-pipeline/agents/collaboration_depth_agent.md",  # FULL/SLIM advisory
    "academic-pipeline/agents/claim_ref_alignment_audit_agent.md",  # opt-in audit
    "shared/agents/compliance_agent.md",                      # cross-skill stage gates
    # Bucket D — cross-phase / meta (4)
    "academic-paper/agents/intake_agent.md",                  # Phase 0 cross-phase config
    "academic-pipeline/agents/pipeline_orchestrator_agent.md",  # orchestrator
    "academic-pipeline/agents/state_tracker_agent.md",        # meta state
    "academic-paper-reviewer/agents/field_analyst_agent.md",  # Phase 0 configures panel
]

# v3.9.4: widened to accept either v3.9.2 or v3.9.4 phase boundary markers.
# timeline_extraction_agent.md (added in v3.9.4) uses v3.9.4 in both markers.
PHASE_BOUNDARY_RE = re.compile(r"## Phase Boundary \(v3\.9\.(2|4)\)")
ENFORCEMENT_RE = re.compile(r"Enforcement \(v3\.9\.(?:2|4)\)")

# #491 defrift lock — the canonical enforcement sentence, keyed by the block's
# version marker ("2" = v3.9.2, "4" = v3.9.4). Any Bucket A copy that drifts
# fails the lint; update procedure lives in check_bucket_a's error message.
# Deliberately lint-local rather than a shared/references/firm_rules.md
# canonical block: this is factual enforcement-STATUS prose, not a behavioral
# firm rule, and co-locating it with its only consumer avoids cross-lint
# coupling (cross-referenced in firm_rules.md "Related mechanisms").
CANONICAL_ENFORCEMENT = {
    "2": (
        "**Enforcement (v3.9.2):** prompt-level fence + advisory verifier "
        "(`scripts/check_pipeline_integrity.py`). Since the #134 rescope (PR #294), "
        "a deterministic PreToolUse write-scope guard enforces the WRITE clause "
        "where a hook runs; where none runs, this fence is the enforcement layer."
    ),
    "4": (
        "**Enforcement (v3.9.4):** prompt-level fence + advisory verifier "
        "(`scripts/check_pipeline_integrity.py` v3.9.4 extension). Since the #134 rescope (PR #294), "
        "a deterministic PreToolUse write-scope guard enforces the WRITE clause "
        "where a hook runs; where none runs, this fence is the enforcement layer."
    ),
}

# H2 marker that ends the Phase Boundary block scope.
# Used to scope keyword checks: keywords appearing elsewhere in the file
# (e.g., in v3.6.7 PATTERN PROTECTION further down) do NOT count.
H2_RE = re.compile(r"^## ", re.MULTILINE)

# Required keywords/phrases inside each Bucket A block.
# Note: Phase Boundary and Enforcement markers are version-widened (v3.9.2|v3.9.4);
# MUST NOT and MAY READ are version-neutral.
REQUIRED_PHRASES = [
    "MUST NOT",
    "MAY READ",
]


def extract_block(text: str) -> str | None:
    """Extract the Phase Boundary (v3.9.2|v3.9.4) block from H2 start to next H2."""
    m = PHASE_BOUNDARY_RE.search(text)
    if m is None:
        return None
    start = m.start()
    # Find next H2 after the block marker
    after_block_start = m.end()
    next_h2 = H2_RE.search(text, after_block_start)
    end = next_h2.start() if next_h2 else len(text)
    return text[start:end]


def check_bucket_a(path: Path) -> list[str]:
    """Bucket A: must have block AND all required phrases inside block."""
    errors: list[str] = []
    if not path.is_file():
        errors.append(f"{path.relative_to(REPO_ROOT)}: file not found")
        return errors

    text = path.read_text(encoding="utf-8")
    block = extract_block(text)
    if block is None:
        errors.append(
            f"{path.relative_to(REPO_ROOT)}: missing '## Phase Boundary (v3.9.2|v3.9.4)' "
            f"block (Bucket A agents MUST carry this block per "
            f"docs/design/2026-05-18-ars-v3.9.2-agent-phase-classification.md)"
        )
        return errors

    for phrase in REQUIRED_PHRASES:
        if phrase not in block:
            errors.append(
                f"{path.relative_to(REPO_ROOT)}: Phase Boundary block missing "
                f"required phrase: {phrase!r} (falsifiability discipline: phrase "
                f"must appear inside the H2 block, not elsewhere in the file)"
            )
    # Enforcement marker check (version-widened: v3.9.2 or v3.9.4)
    if not ENFORCEMENT_RE.search(block):
        errors.append(
            f"{path.relative_to(REPO_ROOT)}: Phase Boundary block missing "
            f"required phrase: 'Enforcement (v3.9.2|v3.9.4)' (falsifiability "
            f"discipline: phrase must appear inside the H2 block)"
        )
    # Canonical enforcement sentence check (#491 defrift lock).
    # Version-matched to the block's own marker; per-file tail after the
    # sentence is free, so containment of the full sentence is the assertion.
    version = PHASE_BOUNDARY_RE.search(block).group(1)
    canonical = CANONICAL_ENFORCEMENT[version]
    if canonical not in block:
        errors.append(
            f"{path.relative_to(REPO_ROOT)}: enforcement paragraph has drifted "
            f"from the canonical sentence (#491 defrift lock, v3.9.{version} "
            f"variant). It must contain CANONICAL_ENFORCEMENT from "
            f"{Path(__file__).name} verbatim (per-file tail after the sentence "
            f"stays free). If the enforcement reality legitimately changed, "
            f"update the constant and sweep all {len(BUCKET_A_AGENTS)} Bucket A "
            f"files in the same PR; the `agents/` mirrors follow via "
            f"check_agents_mirror_sync.py."
        )
    return errors


def check_bucket_bcd(path: Path) -> list[str]:
    """Bucket B/C/D: must NOT have the block (adding fence breaks multi-phase
    or cross-phase legitimate behavior)."""
    errors: list[str] = []
    if not path.is_file():
        errors.append(f"{path.relative_to(REPO_ROOT)}: file not found")
        return errors

    text = path.read_text(encoding="utf-8")
    if PHASE_BOUNDARY_RE.search(text):
        errors.append(
            f"{path.relative_to(REPO_ROOT)}: unexpected '## Phase Boundary "
            f"(v3.9.2|v3.9.4)' block on Bucket B/C/D agent. These agents are "
            f"multi-phase (B), phase-orthogonal (C), or cross-phase meta (D) by "
            f"design — adding a single-phase fence would either falsely block "
            f"legitimate cross-phase work or defeat orchestration. See "
            f"docs/design/2026-05-18-ars-v3.9.2-agent-phase-classification.md."
        )
    return errors


def main() -> int:
    errors: list[str] = []

    for rel_path in BUCKET_A_AGENTS:
        errors.extend(check_bucket_a(REPO_ROOT / rel_path))

    for rel_path in BUCKET_BCD_AGENTS:
        errors.extend(check_bucket_bcd(REPO_ROOT / rel_path))

    # Coverage sanity
    if len(BUCKET_A_AGENTS) != 23:
        errors.append(
            f"BUCKET_A_AGENTS has {len(BUCKET_A_AGENTS)} entries but "
            f"classification doc requires 23 (v3.9.4 added timeline_extraction_agent)"
        )
    if len(BUCKET_BCD_AGENTS) != 16:
        errors.append(
            f"BUCKET_BCD_AGENTS has {len(BUCKET_BCD_AGENTS)} entries but "
            f"classification doc requires 16"
        )

    if errors:
        print("v3.9.2 Phase Boundary lint FAILED:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    print(f"v3.9.2/v3.9.4 Phase Boundary lint PASSED: "
          f"{len(BUCKET_A_AGENTS)} Bucket A agents have block, "
          f"{len(BUCKET_BCD_AGENTS)} Bucket B/C/D agents excluded.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
