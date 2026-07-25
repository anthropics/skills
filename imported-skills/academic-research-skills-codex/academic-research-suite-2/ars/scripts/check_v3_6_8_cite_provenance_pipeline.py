#!/usr/bin/env python3
"""ARS v3.7.1 Step 3b — Cite-Time Provenance Finalizer (academic-pipeline mode).

Spec: docs/design/2026-04-30-ars-v3.6.8-trust-provenance-and-drift-transparency-spec.md
      § Step 3b — Pipeline finalizer (academic-pipeline mode)
      § 3.3   — Cite-time trust-chain non-check (4-cell matrix)
      § 3.6   — Human-Read Signal Protocol (peer-file join semantics)

Lint enforces that `academic-pipeline/agents/pipeline_orchestrator_agent.md`
carries a `## Cite-Time Provenance Finalizer (v3.7.1)` subsection containing:

  1. All 4 matrix rows (HIGH WARN / MED WARN / LOW WARN / OK), each
     keyed by its canonical phrase from spec § 3.3 lines 174-179
  2. The peer-file join reference (`<session>_human_read_log.yaml` or
     the §3.6 computed form `<passport-stem>_human_read_log.yaml`)
  3. The idempotency clause (spec line 181)
  4. The revision-loop preservation clause: resolved markers do not
     invalidate on subsequent passes (spec line 181)

Block scope: starts at the H2 heading line, ends at the next H1/H2/H3
heading line or EOF. Per-clause greps are scoped to the block's bytes.

Boundary rule: this lint does NOT touch the v3.6.7 frozen manifest
(scripts/v3_6_7_inversion_manifest.json); it operates on a different
file (pipeline_orchestrator_agent.md) which is NOT in any v3.6.7
manifest.

Exit codes: 0 on pass, 1 on any failure.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
ORCHESTRATOR = (
    REPO_ROOT / "academic-pipeline" / "agents" / "pipeline_orchestrator_agent.md"
)

FINALIZER_HEADING = "## Cite-Time Provenance Finalizer (v3.7.1)"


def _extract_finalizer_block(text: str) -> str | None:
    """Return the bytes of the finalizer subsection, or None if absent.

    Block start: the canonical H2 heading line (line-anchored).
    Block end: next H1/H2/H3 heading line, or EOF.

    Boundary discipline (R1 P3 acknowledged): nested H3 / H4 inside the
    canonical H2 block would terminate the scan prematurely. This is
    INTENTIONAL — the canonical Step 3b prose is flat (no nested
    headings); a nested heading that gets clauses left UN-scanned will
    fail the lint, surfacing the structural drift to the contributor.
    A future Step 3b expansion that legitimately needs nested headings
    must update this extractor's terminator regex (or remove the H3
    terminator if appropriate). See R1 codex review for context.
    """
    # Anchor on a Markdown heading line (line-start, optional indent,
    # 1-3 hashes, the canonical title, optional trailing whitespace, EOL).
    anchor = re.compile(
        r"(?m)^[ \t]*##[ \t]+Cite-Time Provenance Finalizer \(v3\.7\.1\)[ \t]*$"
    )
    m = anchor.search(text)
    if m is None:
        return None
    start = m.start()
    next_h = re.compile(r"(?m)^[ \t]*#{1,3}[ \t]+")
    head_eol = text.find("\n", m.end())
    search_start = (head_eol + 1) if head_eol >= 0 else len(text)
    next_match = next_h.search(text, pos=search_start)
    end = next_match.start() if next_match else len(text)
    return text[start:end]


# Each (label, marker, diagnostic) describes one canonical clause that
# must appear in the block. Markers are taken verbatim from spec § 3.3
# lines 174-179 + line 181, so any drift between this lint and the spec
# trips a CI failure.
_REQUIRED_CLAUSES: list[tuple[str, str, str]] = [
    (
        "matrix row 1 (HIGH WARN)",
        "UNVERIFIED CITATION — NO ORIGINAL",
        "Row 1 maps source_acquired=false → "
        "[UNVERIFIED CITATION — NO ORIGINAL]<!--ref:slug--> "
        "(spec §3.3 line 176)",
    ),
    (
        "matrix row 2 (MED WARN)",
        "UNVERIFIED CITATION — AI HAS NOT CROSS-CHECKED",
        "Row 2 maps (acquired=true, verified=false, human=false) → "
        "[UNVERIFIED CITATION — AI HAS NOT CROSS-CHECKED]<!--ref:slug--> "
        "(spec §3.3 line 177)",
    ),
    # R1 P2-1 closure: anchor on the matrix-row's two distinguishing
    # tokens — the resolved marker form `<!--ref:slug LOW-WARN-->` AND
    # the `per-section` checklist phrase. The bare `LOW-WARN` substring
    # also appears in the LOW-WARN-promotion paragraph, so a matrix-row
    # drift to e.g. `LOW-WARNING` while the paragraph still mentions
    # `LOW-WARN` could pre-R1 false-pass. The two anchors must BOTH
    # appear; the per-section phrase only ever appears in the matrix row.
    (
        "matrix row 3 (LOW WARN) — resolved marker form",
        "<!--ref:slug LOW-WARN-->",
        "Row 3 maps (acquired=true, verified=true, human=false) → "
        "<!--ref:slug LOW-WARN--> (spec §3.3 line 178)",
    ),
    # R2 P2 closure: `per-section` alone appears in BOTH the matrix row
    # and the LOW-WARN-promotion paragraph (twice in the canonical block),
    # so anchoring on the bare token doesn't actually catch matrix-row
    # drift. Anchor on the FULL canonical phrase that is unique to the
    # matrix row's checklist-append clause.
    (
        "matrix row 3 (LOW WARN) — checklist append clause",
        "per-section pre-finalization checklist",
        "Row 3 must also append the slug to a per-section "
        "pre-finalization checklist artifact (spec §3.3 line 178)",
    ),
    # R3 P2-1 closure: bare `<!--ref:slug ok-->` appears in BOTH the
    # matrix row and the LOW-WARN-promotion paragraph (and idempotency
    # discussion). Anchor on the unique matrix-row phrase
    # `**OK**: replace with` to disambiguate matrix-row drift.
    (
        "matrix row 4 (OK) — resolved marker form",
        "<!--ref:slug ok-->",
        "Row 4 maps all-true triple → <!--ref:slug ok--> "
        "(spec §3.3 line 179)",
    ),
    (
        "matrix row 4 (OK) — canonical row clause",
        "**OK**: replace with",
        "Row 4's canonical row clause is `**OK**: replace with "
        "<!--ref:slug ok-->` (spec §3.3 line 179)",
    ),
    (
        "peer-file join reference",
        "human_read_log.yaml",
        "Finalizer joins on `<passport-stem>_human_read_log.yaml` per "
        "spec §3.3 line 172 + §3.6 round-5 R5-003 amend",
    ),
    (
        "idempotency clause",
        "idempotent",
        "Each finalizer pass must be idempotent on its own resolved "
        "markers; re-running on `<!--ref:slug ok-->` is a no-op "
        "(spec §3.3 line 181)",
    ),
    (
        "revision-loop preservation clause",
        "do not invalidate",
        "On revision loops the finalizer re-resolves any newly-emitted "
        "bare `<!--ref:slug-->` comments; resolved markers do not "
        "invalidate (spec §3.3 line 181 + Step 3b acceptance line 457)",
    ),
    # R3 P2-2 closure: R2 closed a P1 specifically about /ars-unmark-read
    # rescind semantics (`ok` is NOT a fixed point; can be demoted). The
    # bidirectional contract MUST stay in the prose; lint must enforce
    # both the rescind affordance and demotion-language so future edits
    # cannot silently drop them.
    (
        "rescind affordance clause",
        "/ars-unmark-read",
        "Spec §3.6 line 302 defines /ars-unmark-read as the rescind "
        "affordance; the canonical block must mention it so demotion "
        "semantics survive prose edits (R2 P1 closure)",
    ),
    # R3 P2-2: anchor on `demot` stem so both `demote` (verb) and
    # `demotion` (noun) satisfy the clause.
    (
        "bidirectional matrix re-evaluation clause",
        "demot",
        "R2 P1 closure: the canonical block must explicitly describe "
        "demotion (e.g. `ok` → `LOW-WARN` after /ars-unmark-read) so "
        "the bidirectional contract survives prose edits",
    ),
]


def check_finalizer_subsection(verbose: bool = True) -> int:
    """Enforce that the orchestrator carries the finalizer subsection
    with all required clauses. Returns 0 PASS / 1 FAIL.
    """
    if not ORCHESTRATOR.exists():
        print(
            "[ARS-V3.7.1 STEP-3B LINT ERROR: orchestrator agent file missing "
            f"at {ORCHESTRATOR.relative_to(REPO_ROOT)}]"
        )
        return 1
    text = ORCHESTRATOR.read_text(encoding="utf-8")
    block = _extract_finalizer_block(text)
    if block is None:
        print(
            "[ARS-V3.7.1 STEP-3B LINT ERROR: "
            "academic-pipeline/agents/pipeline_orchestrator_agent.md is "
            f"missing the canonical H2 heading '{FINALIZER_HEADING}'. "
            "Step 3b spec line 449 requires this subsection.]"
        )
        return 1

    failures: list[str] = []
    for label, marker, diagnostic in _REQUIRED_CLAUSES:
        if marker not in block:
            failures.append(
                f"  [{label}] missing canonical phrase {marker!r}. "
                f"{diagnostic}"
            )

    if failures:
        print(
            "[ARS-V3.7.1 STEP-3B LINT ERROR: Cite-Time Provenance Finalizer "
            "subsection missing required clauses]"
        )
        for line in failures:
            print(line)
        return 1

    if verbose:
        rel = ORCHESTRATOR.relative_to(REPO_ROOT)
        print(f"  [{rel}] Step 3b finalizer subsection PASS "
              f"({len(_REQUIRED_CLAUSES)} canonical clauses present)")
        print("[v3.7.1 Step 3b finalizer] PASSED")
    return 0


def main() -> int:
    return check_finalizer_subsection()


if __name__ == "__main__":
    sys.exit(main())
