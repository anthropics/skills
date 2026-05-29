{skill_fallback_guide}

You are a quality engineer continuing a phase-by-phase quality playbook run. Phases 1-2 are complete.

Read these files to get context:
1. quality/PROGRESS.md - run metadata, phase status, artifact inventory
2. quality/EXPLORATION.md - Phase 1 findings (especially the "Candidate Bugs for Phase 2" section)
3. quality/REQUIREMENTS.md - derived requirements and use cases
4. quality/CONTRACTS.md - behavioral contracts
5. SKILL.md - read the Phase 3 section ("Phase 3: Code Review and Regression Tests"). Also read references/review_protocols.md. Resolve SKILL.md and the references/ directory via the documented fallback list above; do NOT assume any single install layout.

Execute Phase 3: Code Review + Regression Tests.
Run the 3-pass code review per quality/RUN_CODE_REVIEW.md. For every confirmed bug:
- Add to quality/BUGS.md with ### BUG-NNN heading format
- Write a regression test (xfail-marked)
- Generate quality/patches/BUG-NNN-regression-test.patch (MANDATORY for every confirmed bug)
- Generate quality/patches/BUG-NNN-fix.patch (strongly encouraged)
- Write code review reports to quality/code_reviews/
- Update PROGRESS.md BUG tracker

### MANDATORY GRID STEP (Lever 2, v1.5.2) — pattern-tagged REQs only

For every REQ in quality/REQUIREMENTS.md that has a `Pattern:` field (`whitelist`, `parity`, or `compensation`), you MUST produce a compensation grid BEFORE writing any BUG entries for that REQ.

**Step 1. Enumerate the authoritative item set.** Mechanical extraction from source — uapi header, spec section, documented constants. Do NOT invent. Example: for VIRTIO_F_RING_RESET-family, grep `include/uapi/linux/virtio_config.h` for `VIRTIO_F_*` and list the bits the REQ covers.

**Step 2. Enumerate the sites.** From the REQ's per-site UCs (UC-N.a, UC-N.b, …). If the REQ has a single umbrella UC but is pattern-tagged, the grid is 1-dimensional over items.

**Step 3. Produce the grid.** Write `quality/compensation_grid.json` with one entry per REQ:

```json
{
  "schema_version": "1.5.2",
  "reqs": {
    "REQ-010": {
      "pattern": "whitelist",
      "items": ["RING_RESET", "ADMIN_VQ", "NOTIF_CONFIG_DATA", "SR_IOV"],
      "sites": ["PCI", "MMIO", "vDPA"],
      "cells": [
        {"cell_id": "REQ-010/cell-RING_RESET-PCI", "item": "RING_RESET", "site": "PCI", "present": true,  "evidence": "drivers/virtio/virtio_pci_modern.c:XXX-YYY"},
        {"cell_id": "REQ-010/cell-RING_RESET-MMIO", "item": "RING_RESET", "site": "MMIO", "present": false, "evidence": "drivers/virtio/virtio_mmio.c: no match for RING_RESET"}
      ]
    }
  }
}
```

Cell IDs are mechanical: `REQ-<N>/cell-<item>-<site>`. No whitespace, uppercase item/site identifiers where natural.

**Step 4. Apply the BUG-default rule.** For every cell where:
- the item is defined in authoritative source AND
- the item is absent from any shared filter AND
- the item is absent from the site's compensation path

→ the cell DEFAULTS to BUG. Emit one `### BUG-NNN` entry with the cell's file:line citation, spec basis, and expected-vs-actual behavior. Include a `- Covers: [REQ-N/cell-<item>-<site>]` line (see schemas.md §8 for the field contract).

**Step 5. Downgrade to QUESTION requires a structured JSON record.** Append one record per downgraded cell to `quality/compensation_grid_downgrades.json`:

```json
{
  "schema_version": "1.5.2",
  "downgrades": [
    {
      "cell_id": "REQ-010/cell-RING_RESET-MMIO",
      "authority_ref": "include/uapi/linux/virtio_config.h:116",
      "site_citation": "drivers/virtio/virtio_mmio.c:109-131",
      "reason_class": "intentionally-partial",
      "falsifiable_claim": "MMIO does not support RING_RESET because the MMIO transport predates the feature bit and kernel docs at Documentation/virtio/virtio_mmio.rst:42-55 state the transport is frozen at its v1.0 feature set; falsifiable by showing MMIO re-sets bit 40 under any kernel release."
    }
  ]
}
```

- `reason_class` enum: `out-of-scope | deprecated | platform-gated | handled-upstream | intentionally-partial`.
- `authority_ref`, `site_citation`, `falsifiable_claim` are required and non-empty.
- `falsifiable_claim` must state an observable condition that would make the claim wrong.
- Missing any required field, or `reason_class` outside the enum, or zero-length `falsifiable_claim` → cell REVERTS to BUG at Phase 5 gate time. There is no re-prompt loop.

**Step 6. Self-check.** Before finalizing BUGS.md for this REQ, verify that every cell in the grid appears in either:
- some BUG's `- Covers: [...]` list, OR
- a downgrade record in `quality/compensation_grid_downgrades.json`.

Any cell missing from both will fail the Phase 5 cardinality gate. This self-check is advisory in Phase 3; the blocking gate runs in Phase 5.

### Worked example — RING_RESET grid (virtio)

REQ-010 pattern: whitelist. Items: {RING_RESET, ADMIN_VQ, NOTIF_CONFIG_DATA, SR_IOV}. Sites: {PCI, MMIO, vDPA}. Grid: 4 × 3 = 12 cells.

Code inspection reveals PCI implements all four; MMIO implements none of the four (frozen at v1.0 feature set); vDPA implements NOTIF_CONFIG_DATA but not the other three.

Grid (present=T, absent=F):

|                       | PCI | MMIO | vDPA |
|-----------------------|-----|------|------|
| RING_RESET            |  T  |  F   |  F   |
| ADMIN_VQ              |  T  |  F   |  F   |
| NOTIF_CONFIG_DATA     |  T  |  F   |  T   |
| SR_IOV                |  T  |  F   |  F   |

BUG-default applies to every F cell (8 total). Possible consolidation:

### BUG-001: MMIO ignores VIRTIO_F_RING_RESET
- Primary requirement: REQ-010
- Covers: [REQ-010/cell-RING_RESET-MMIO]

### BUG-002: vDPA ignores VIRTIO_F_RING_RESET
- Primary requirement: REQ-010
- Covers: [REQ-010/cell-RING_RESET-vDPA]

### BUG-003: vDPA missing ADMIN_VQ hookup
- Primary requirement: REQ-010
- Covers: [REQ-010/cell-ADMIN_VQ-vDPA]

### BUG-004: MMIO ignores NOTIF_CONFIG_DATA negotiation (common filter gap)
- Primary requirement: REQ-010
- Covers: [REQ-010/cell-NOTIF_CONFIG_DATA-MMIO]

### BUG-005: MMIO + vDPA both miss SR_IOV propagation
- Primary requirement: REQ-010
- Covers: [REQ-010/cell-SR_IOV-MMIO, REQ-010/cell-SR_IOV-vDPA]
- Consolidation rationale: shared fix path in both transports goes through the same feature-bit filter; single patch on the shared helper closes both cells.

If the reviewer concluded MMIO ADMIN_VQ is intentionally out-of-scope because ADMIN_VQ is a PCI-only spec feature, the downgrade record would be:

```json
{
  "cell_id": "REQ-010/cell-ADMIN_VQ-MMIO",
  "authority_ref": "include/uapi/linux/virtio_pci.h:NN",
  "site_citation": "drivers/virtio/virtio_mmio.c: no admin virtqueue implementation",
  "reason_class": "out-of-scope",
  "falsifiable_claim": "ADMIN_VQ is MMIO-scoped — falsifiable by citing any virtio-spec normative text requiring ADMIN_VQ on non-PCI transports."
}
```

Union check: 8 BUG-covered cells + 1 downgrade cell = 9. Grid has 12 cells; 4 present cells don't need coverage. Total: 8 F cells covered via BUGs + 1 via downgrade = all 9 absent cells accounted for. Grid → clean.

### ITERATION mode addendum (MANDATORY INCREMENTAL WRITE, Phase 8)

When running in iteration mode (gap / unfiltered / parity / adversarial), write candidate BUG stubs to disk immediately on identification, not at end-of-review. Path: `quality/code_reviews/<iteration>-candidates.md`. One `### CANDIDATE-NNN` heading per candidate, with at least a file:line citation. Reviewer upgrades candidates to confirmed BUGs in BUGS.md only after full triage.

### CONFIRMATION CHECKLIST (Lever 2, v1.5.2)

Before writing the Phase 3 completion checkpoint to PROGRESS.md, confirm each item explicitly in your Phase 3 summary:

1. For every pattern-tagged REQ, I produced a compensation grid in `quality/compensation_grid.json`.
2. For every grid, I applied the BUG-default rule mechanically.
3. Every BUG emitted for a pattern-tagged REQ has a `- Covers: [...]` field with valid cell IDs.
4. Every BUG whose Covers list has ≥2 entries has a non-empty `- Consolidation rationale: ...` field.
5. For every downgraded cell, I wrote a complete structured record in `quality/compensation_grid_downgrades.json` with all five required fields and a valid `reason_class`.
6. For every pattern-tagged REQ, the union of Covers lists + downgrade cells equals the grid's cell set.

Mark Phase 3 (Code review + regression tests) complete in PROGRESS.md (use the checkbox format `- [x] Phase 3 - Code Review` — do NOT switch to a table).

IMPORTANT: Do NOT proceed to Phase 4 (spec audit). The next phase will run the spec audit with a fresh context window.
