# Design — #105 v3.7.3 contamination_signals backfill migration tool

**Date**: 2026-05-15
**Issue**: #105 (v3.7.3 release completeness follow-up)
**Status**: design — ready for TDD implementation
**Scope**: minimal — single tool, directory-scan, scalar provenance, ruamel round-trip. No batch mode, no resumable checkpoint, no structured backfill provenance.

---

## 1. Problem

v3.7.3 spec §3.2 R-L3-2-B says: "bibliography_agent computes contamination_signals at ingest time, not at audit time. Re-running the check post-hoc on existing entries is **a separate batch operation (deferred to user invocation; not part of v3.7.3 finalizer)**."

Pre-v3.7.3 passport entries lack `contamination_signals`. Without a backfill tool:

- Users with existing corpora cannot get CONTAMINATED-PREPRINT / CONTAMINATED-UNMATCHED advisories on pre-v3.7.3 entries
- The v3.7.3 finalizer treats absence as "signals not computed → no advisory fires", which is technically correct but operationally degrades the v3.7.3 protection layer for legacy corpora
- This issue (#105) is v3.7.3 release completeness: the spec already promised the backfill path exists; this tool delivers it

## 2. Spec anchors (frozen, do not re-litigate)

- §3.2 Signal 1: `year >= 2024 AND venue ∈ {arXiv, bioRxiv, medRxiv, SSRN, Research Square, Preprints.org, ChemRxiv, EarthArXiv, OSF Preprints, TechRxiv}` (10-server closed list)
- §3.2 Signal 2: SS API lookup per `deep-research/references/semantic_scholar_api_protocol.md`; OMIT field on `obtained_via=manual` (exemption); OMIT field on API degradation (absence ≠ negative confirmation)
- §3.2 emission rules: emit object with both fields `false` when computed-and-clean; emit partial object when only one signal computable; never set `semantic_scholar_unmatched: false` on API degradation
- Schema cross-field rules: 4 `allOf` branches already cover (a) manual + semantic_scholar_unmatched present = INVALID; (b) preprint_post_llm_inflection=true + year<2024 = INVALID

## 3. Open-question resolutions (user-chosen 2026-05-15)

| # | Question | Resolution | Rationale |
|---|---|---|---|
| Q1 | API rate-limit handling | backoff-only (existing SS protocol: 429→2s×3); **no resumable checkpoint** | YAGNI for minimal scope; large-corpus users add checkpoint in follow-up if needed |
| Q2 | Schema field naming | scalar `contamination_signals_backfilled_at: ISO-8601 timestamp string` | issue body itself suggested "start with scalar"; strictly additive upgrade path to structured if v3.7.4 needs it |
| Q3 | Multi-passport batch mode | directory-scan only (no `--input-list`) | YAGNI for minimal scope; user passport is typically 1 active session |
| Q4 | YAML library | ruamel.yaml | passport is user-owned file; preserve comments + key order (memory `feedback_toml_duplicate_table_corruption` discipline spirit) |

## 4. Design — three pieces

### 4.1 Resolver module

`scripts/contamination_signals.py` — pure functions:

```python
PREPRINT_VENUES = frozenset({
    "arXiv", "bioRxiv", "medRxiv", "SSRN", "Research Square",
    "Preprints.org", "ChemRxiv", "EarthArXiv", "OSF Preprints", "TechRxiv",
})

def compute_preprint_signal(entry: Mapping) -> bool:
    """Signal 1 per spec §3.2 Vector 1."""

def compute_ss_unmatched_signal(entry, ss_client) -> bool | None:
    """Signal 2 per spec §3.2 Vector 2. Returns None on (a) manual exemption,
    (b) API degradation; returns True/False otherwise."""
```

The two signals are independently testable. SS API call is dependency-injected so tests use a mock; production uses a real client.

### 4.2 Migration script

`scripts/migrate_literature_corpus_to_v3_7_3.py` — CLI tool:

```
usage: migrate_literature_corpus_to_v3_7_3.py [--dry-run] [--verbose] <passport_or_dir>

Arguments:
  passport_or_dir   Path to a single passport YAML or a directory containing passports.
                    Directory scan finds *.yaml files non-recursively.

Options:
  --dry-run         Print proposed changes; write no files.
  --verbose         Per-entry logging.
```

**Behavior:**

1. Load passport via `ruamel.yaml` (round-trip — preserve comments + key order)
2. For each entry in `literature_corpus[]`:
   - If `contamination_signals` already present → SKIP (idempotency)
   - If entry's schema state is "insufficient-data" (no year, or no venue + no source_pointer hint) → SKIP, log reason
   - Compute Signal 1
   - Compute Signal 2 (skip on manual; omit on API degradation)
   - Construct `contamination_signals` object per emission rules
   - Set `contamination_signals_backfilled_at` to current UTC ISO-8601 timestamp
3. If `--dry-run`, print diff and exit. Else, write back via `ruamel.yaml` round-trip.
4. Emit migration report at stdout: `processed=N patched=M skipped=K errored=E`, plus per-skip-category counts.

**SS API client:** reuse existing `references/semantic_scholar_api_protocol.md` logic. Implementation: thin wrapper around `requests` with 429 backoff per protocol. Single shared client across the migration run (HTTP keepalive).

### 4.3 Schema extension

`shared/contracts/passport/literature_corpus_entry.schema.json` — add one optional field:

```json
"contamination_signals_backfilled_at": {
  "type": "string",
  "format": "date-time",
  "description": "v3.7.3 backfill provenance. ISO-8601 UTC timestamp set by scripts/migrate_literature_corpus_to_v3_7_3.py when contamination_signals was computed post-hoc rather than at ingest. Absence means signals were either computed at ingest (bibliography_agent v3.7.3+) or not computed at all. Backward compat: pre-v3.7.3 entries lack both contamination_signals and this field; ingest-time entries lack only this field."
}
```

Pure additive — existing v3.7.3 ingest-time entries (which don't carry this field) remain valid.

### 4.4 Migration guide doc

`docs/migration/v3.7.3-contamination-signals-backfill.md` — user-facing:

- When to run (after upgrading to v3.7.3+)
- Dry-run-first workflow
- Idempotency guarantee
- Semantic Scholar API rate-limit considerations (1 req/s unauthenticated; large corpora take time)
- What to do on API degradation (re-run later)

## 5. Files touched

| File | Change kind |
|---|---|
| `scripts/contamination_signals.py` | new — Signal 1 + Signal 2 resolvers |
| `scripts/migrate_literature_corpus_to_v3_7_3.py` | new — CLI migration tool |
| `scripts/test_contamination_signals.py` | new — unit tests for resolvers |
| `scripts/test_migrate_literature_corpus_to_v3_7_3.py` | new — pytest for migration tool (mocks SS API) |
| `shared/contracts/passport/literature_corpus_entry.schema.json` | additive — new optional `contamination_signals_backfilled_at` field |
| `scripts/adapters/tests/test_literature_corpus_entry_schema.py` | extend — 2-3 tests for the new field (valid present / valid absent / invalid type) |
| `docs/migration/v3.7.3-contamination-signals-backfill.md` | new — user-facing migration guide |
| `requirements-dev.txt` | add `ruamel.yaml>=0.18` |
| `CHANGELOG.md` | Unreleased entry under #105 |

### Files explicitly NOT touched

| File | Reason |
|---|---|
| `deep-research/agents/bibliography_agent.md` | v3.7.3 spec frozen; ingest-time computation unchanged |
| `academic-pipeline/agents/pipeline_orchestrator_agent.md` | Finalizer behavior unchanged; migration is offline |
| Existing `scripts/adapters/*` | Adapters produce ingest-time entries; migration is downstream |

## 6. Test discipline

Per `superpowers:test-driven-development`:

**Resolver tests (`test_contamination_signals.py`):**

- Signal 1: 11 cases (one per preprint venue × year boundary; non-preprint venue; year < 2024)
- Signal 2: 6 cases (manual exemption → None; API match → False; API no-match → True; API 429×3 backoff → None; API 5xx → None; API network failure → None)

**Migration tests (`test_migrate_literature_corpus_to_v3_7_3.py`):**

- Dry-run mode: no file writes, stdout shows proposed changes
- Idempotency: re-run on migrated passport produces zero changes (byte-equivalent)
- Manual entry skipped: `obtained_via=manual` → signals computed but `semantic_scholar_unmatched` omitted
- Insufficient-data entry: missing year → skipped, logged
- Already-migrated entry (has `contamination_signals`): skipped, no re-computation
- Directory scan: 2 passports in a dir, both migrated independently
- Report counts: processed/patched/skipped accurate

**Schema tests (extend `test_literature_corpus_entry_schema.py`):**

- `contamination_signals_backfilled_at` present + valid ISO-8601 → valid
- field absent → valid (backward compat)
- field as non-string → rejected
- field as malformed timestamp → rejected by format validator

## 7. Regression budget

- 1053 + 17 (#111) baseline must stay green
- All new tests must pass
- 4 schema cross-field rules (allOf branches) must continue to fire correctly on edge inputs
- No frontmatter change to existing skills
- No new lint (schema lint already covers the new field via `additionalProperties: false` permission)

## 8. Out of scope (defer)

- Resumable checkpoint (deferred until a user reports a 10k-entry corpus)
- `--input-list` batch mode (deferred until multi-corpus user emerges)
- v3.7.4 OpenAlex / Crossref signals (covered by #102)
- Structured `_backfill_provenance: {at, version, by}` object (upgrade path: scalar `_backfilled_at` → structured object remains backward-compatible if needed)

---

## Related

- Parent v3.7.3 spec: `docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md` §3.2 (Vector 1 + Vector 2 + R-L3-2-B)
- Schema: `shared/contracts/passport/literature_corpus_entry.schema.json` (existing contamination_signals + 4 allOf invariants)
- v3.7.3 PR #98: ship commit `4cc880f` — added contamination_signals to schema + bibliography_agent computation
- Migration discipline precedent: memory `feedback_toml_duplicate_table_corruption` — round-trip parser principle (applied here via ruamel.yaml for YAML)
- External motivation: Zhao et al. arXiv:2605.07723 (2026-05) — corpus-scale evidence anchor (README #104 propagation)
