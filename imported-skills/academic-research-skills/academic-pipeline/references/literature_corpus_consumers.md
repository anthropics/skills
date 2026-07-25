# Consumer Protocol — `literature_corpus[]` Reading

**Status**: Released in v3.6.5 (both Phase 1 consumers wired)
**Applies to**: any agent in this repo that reads `literature_corpus[]` from a Material Passport
**Authoritative spec**: [`docs/design/2026-04-26-ars-v3.6.5-consumer-integration-design.md`](../../docs/design/2026-04-26-ars-v3.6.5-consumer-integration-design.md)

## What this document covers

This is the contract every literature-reading consumer agent must follow. The v3.6.4 input port (`shared/contracts/passport/literature_corpus_entry.schema.json`) defines what enters a Material Passport; this document defines how Phase 1 agents read it.

The `corpus-first, search-fills-gap` flow has five steps; the four Iron Rules are non-negotiable; the PRE-SCREENED block is the reproducibility surface; failures are surfaced honestly via the `[CORPUS PARSE FAILURE: <cause>]` graceful fallback.

## Reading flow (shared by every consumer)

```
Step 0: Detect literature_corpus[] presence and minimal shape
Step 1: Pre-screen corpus against current RQ
Step 2: Search-fills-gap — case A / B / B' / C
Step 3: Merge included + external_included for downstream
Step 4: Emit Search Strategy Report with PRE-SCREENED block
```

The full flow specification lives in spec §3.1. Each consumer agent's `agent.md` must include the full Step 0–4 description and all four Step 2 case markers (case A / case B / case B' / case C). The lint enforces presence (L6).

## PRE-SCREENED block template

Every consumer emits the block in this exact shape (alphabetical ordering for citation_keys; truncate at 50 entries with appendix file). Spec §3.2 has the complete template plus truncation rules.

```markdown
PRE-SCREENED FROM USER CORPUS:
- Adapter: <obtained_via enum value | "<unspecified>" | "mixed (...)">
                                          # e.g., zotero-bbt-export, or "<unspecified>" per F4a,
                                          # or "<value> (N of M entries declared)" per F4b,
                                          # or "mixed (zotero-bbt-export: K, ..., undeclared: U)" per F4c
- Snapshot date: <max(obtained_at)>        # ISO 8601, or "<unspecified>" per F4d,
                                          # or "<date> (M of N entries declared)" per F4e,
                                          # or append "(spans <N> days; corpus may not be a single snapshot)" per F4f
- Total entries scanned: <N>
- Pre-screening result:
  - Included: <K> entries
    citation_keys:
      - <k1>
      - <k2>
  - Excluded by inclusion / exclusion criteria: <E> entries
    citation_keys:
      - <e1>
    (omit this sub-block if 0)
  - Skipped (criteria cannot be applied): <S> entries
    citation_keys with reasons:
      - <key>: <reason>
    (omit this sub-block if 0)
- Zero-hit note (emit per F3 only when Included: 0):
  Zero-hit note (corpus non-empty, 0 included after screening): possible
  causes are (a) corpus is stale relative to current RQ, (b) RQ has
  shifted away from what the user originally curated, (c) adapter
  exported entries unrelated to this RQ.
- Note: presence in corpus does not imply inclusion;
  same criteria applied to corpus and external sources.
```

## The four Iron Rules

### Iron Rule 1 — Same criteria

Apply the same Inclusion / Exclusion criteria to corpus entries and external database results. No exceptions. A corpus entry is not "pre-approved"; it must clear the same screening as a fresh database hit.

### Iron Rule 2 — No silent skip

Any skipped corpus entry must be recorded in the PRE-SCREENED block's skipped sub-section with a reason. Silently dropping an entry is a prompt-layer violation. The lint enforces structural markers; behaviour is enforced by the BAD / GOOD example pair below and observed in real runs.

<!-- BAD -->
```
[corpus has 5 entries]
agent includes 3, excludes 1 (off-topic), and silently drops 1 with empty
abstract because "I cannot evaluate it".

PRE-SCREENED block reports:
- Total entries scanned: 5
- Included: 3 entries
- Excluded: 1 entry
(no Skipped sub-block)

(1 entry silently disappeared from the pipeline: 3 + 1 ≠ 5 — Iron Rule 2 violation.)
```

<!-- GOOD -->
```
[corpus has 5 entries]
agent excludes 1 (off-topic), keeps 3 in pre_screened_included[].
agent records 1 with empty abstract as Skipped: "abstract empty after privacy clearing; criteria reference research method but only title is present, criteria cannot be applied".

PRE-SCREENED block reports:
- Included: 3 entries
- Excluded by inclusion / exclusion criteria: 1 entry
- Skipped (criteria cannot be applied): 1 entry
  - smith2024foo: abstract empty after privacy clearing; criteria reference research method but only title is present
- Note: presence in corpus does not imply inclusion;
  same criteria applied to corpus and external sources.
```

### Iron Rule 3 — No corpus mutation

Consumer agents never modify, backfill, or derive new content into `literature_corpus[]`. Read only. The Material Passport's corpus is the user's curated list; any rewriting belongs to the user's adapter (v3.6.4 input port), not Phase 1 prompt-layer agents.

### Iron Rule 4 — Graceful fallback on parse failure

Consumer agents do NOT re-validate schema, do NOT parse JSON Schema at runtime, and do NOT dereference `source_pointer` URIs. The v3.6.4 input-port lint validates adapter output, but a passport may reach a Phase 1 agent through other paths (hand-edits, `resume_from_passport`, assembled passports). When a consumer cannot parse `literature_corpus[]`, emit `[CORPUS PARSE FAILURE: <cause>]` in the Search Strategy Report and fall back to external-DB-only flow. Do not abort Phase 1, do not attempt schema repair, do not invent contents.

## Zero-hit and provenance reporting (F3 / F4)

Two reproducibility surfaces sit inside the PRE-SCREENED block. Every consumer agent must emit each one when the corresponding trigger fires; both are non-blocking and independent of which Step 2 case dispatches next.

**Zero-hit note (F3).** When `pre_screened_included[]` is empty after Step 1 — corpus is non-empty but no entry survived screening — the consumer emits a zero-hit note inside the PRE-SCREENED block listing the three plausible causes:

```
- Zero-hit note (corpus non-empty, 0 included after screening): possible causes
  are (a) corpus is stale relative to current RQ, (b) RQ has shifted away from
  what the user originally curated, (c) adapter exported entries unrelated to
  this RQ.
```

The note appears regardless of which Step 2 case fires next. Step 2 dispatch follows F3 in spec §4.1.

**Provenance reporting (F4a–F4f).** `obtained_via` and `obtained_at` are optional in v3.6.4 schema. The PRE-SCREENED block's `Adapter:` and `Snapshot date:` lines reflect actual coverage; consumers never invent enum values or guess timestamps.

| Sub-case | Trigger | `Adapter:` line content |
|---|---|---|
| F4a | Zero entries declare `obtained_via` | `Adapter: <unspecified>` + trailing note `Adapter origin not declared; user-written adapter should populate obtained_via per v3.6.4 schema recommendation.` |
| F4b | At least one entry declares; all declared share single value | `Adapter: <enum value> (N of M entries declared)` |
| F4c | Two or more distinct enum values among declared entries | `Adapter: mixed (zotero-bbt-export: K, obsidian-vault: L, ..., undeclared: U)` |

| Sub-case | Trigger | `Snapshot date:` line content |
|---|---|---|
| F4d | Zero entries declare `obtained_at` | `Snapshot date: <unspecified>` + trailing note `Snapshot date not declared; reproducibility is reduced. Adapter should populate obtained_at per v3.6.4 schema recommendation.` |
| F4e | Partial coverage | `Snapshot date: <max(obtained_at)> (M of N entries declared)` |
| F4f | Wide spread (>90 days between min and max) | append `(spans <N> days; corpus may not be a single snapshot)`. Composes with F4e. |

F4a/b/c are mutually exclusive by trigger. F4d applies only when zero entries declare `obtained_at`; F4e and F4f compose. See spec §4.2 for the full precedence reasoning.

## Consumer: bibliography_agent

**Status**: Wired in v3.6.5
**Skill**: deep-research
**Phase**: 1 (literature search and curation)
**Agent file**: [`deep-research/agents/bibliography_agent.md`](../../deep-research/agents/bibliography_agent.md)

The deep-research bibliography agent applies the corpus-first flow during its systematic literature search. The PRE-SCREENED block sits inside the Search Strategy section of its Annotated Bibliography output (per the agent's existing Output Format), preceding the existing DATABASES / Inclusion-Exclusion / RESULTS structure.

When `literature_corpus[]` is non-empty and parses cleanly, the agent enters Step 1 pre-screening. When the corpus is absent, empty, or fails the minimal shape check, the agent runs its existing external-DB-only flow (Iron Rule 4 graceful fallback for the failure cases).

## Consumer: literature_strategist_agent

**Status**: Wired in v3.6.5
**Skill**: academic-paper
**Phase**: 1 (literature search and curation)
**Agent file**: [`academic-paper/agents/literature_strategist_agent.md`](../../academic-paper/agents/literature_strategist_agent.md)

The academic-paper literature strategist agent applies the corpus-first flow during its literature search strategy phase. The PRE-SCREENED block sits inside the Search Strategy section of the Literature Search Report (per the agent's existing Output Format), immediately before the `Databases` line. The merged `final_included` set feeds the agent's downstream Annotated Bibliography, Literature Matrix, Research Gap Identification, and Recommended Sources by Paper Section outputs without altering their formats.

When `literature_corpus[]` is non-empty and parses cleanly, the agent enters Step 1 pre-screening, and Step 2 search-fills-gap dispatches the external 4-Layer Progressive Strategy. When the corpus is absent, empty, or fails the minimal shape check, the agent runs its existing 4-Layer external-DB-only flow unchanged (Iron Rule 4 graceful fallback for the failure cases).
