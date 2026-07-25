# ARS #390 — Diff/Patch Revision Mode (block-anchored deterministic patch apply for revision rounds)

**Issue:** #390 (scoped from #89 Item 7 — DELEGATE-52 follow-up, rank 1 in the re-ranked priority table)
**Date:** 2026-06-10
**Type:** Architecture design spec (design-phase only — no implementation in this round)
**Decision authority:** owner-confirmed scope (#89 progress comment 2026-06-09; this spec is the Item 7 design anchor)
**Prerequisites shipped:** v3.7.1 two-layer / v3.7.3 three-layer citation markers (the HTML-comment marker convention this design extends), #134 Slice 1 scoped-write guard (the Bucket A Bash-deny that fixes the emitter/applier role split), #388 Items 4+5 (interaction-count budget + Context Hygiene at dispatch).

## §0 Slice B amendment (2026-06-11, #424)

Implementation-round decisions recorded against this spec (amendment mode — the body below is the design-round record and stands unedited; where it conflicts with this block, this block wins). All four were taken with an independent cross-model consult concurring:

1. **`touched_ratio` threshold = 0.6** (§3.3 required ship decision). Comparator is strict `>` per the body's "above a threshold"; `ars_apply_revision_patch.py` now defaults to 0.6 (`DEFAULT_TOUCHED_RATIO_THRESHOLD`); 1.0 disables (the ratio never exceeds 1.0). Rationale: high enough not to checkpoint honest major-but-local revisions, low enough to catch a re-emission wearing a patch costume.
2. **`insert_after` heading-anchor exemption** (carried from Slice A cross-model review; supersedes the §3.3 literal rule for this one case). An `insert_after` whose ANCHOR is a heading raises no heading flag when its segmented `new_text` contains no heading blocks — the heading's bytes are untouched, and "insert body text after a section heading" is the most common legitimate insertion; flagging it every round is alarm fatigue that erodes the checkpoint. Heading-bearing `new_text` still flags via its segments; replace/delete of a heading flags unchanged.
3. **Patch emission format = sidecar file** (§10 open item; supersedes §3.2's "emitted in a fenced code block"). The writer writes `phase6_*/revision_patch_round<N>.json` inside its #134 write fence (file writes are allowed there; only Bash is denied) — a schema-validatable artifact with no fragile fenced-chat extraction step, and the same file convention Mode B users get.
4. **Marker interaction defaults verified and fixed in prose** (§10 open items). First-party check found `formatter_agent.md` had NO marker-strip rule for ANY marker kind and `word_count_conventions.md` had no comment-exclusion rule — the body's "expectation: formatter strips like other markers" had nothing to point at. Slice B adds both explicitly: Phase 7 strips all ARS markers (`ref`/`anchor`/`block`) from converted final outputs after the marker-dependent gates run (working drafts + `phase6_*/` artifacts keep theirs), and word counts strip `<!--...-->` before splitting — one rule for all marker kinds. Max single-op `new_text` size: folded into the existing triggers, no separate cap — a whole-paper `new_text` necessarily carries headings (heading flag) and a true re-emission must delete the displaced blocks (ratio flag). `preserved_ratio` surfaces as one advisory line next to the #389 round-trip count at stage checkpoints.

## 0. TL;DR

Every ARS revision round today asks `draft_writer_agent` to re-emit the complete paper. DELEGATE-52 (arXiv:2604.15597) measures exactly this round-trip shape and finds that frontier models corrupt documents by **subtle modification, not deletion** — and that 80–98% of total degradation comes from rare single-step critical failures. Full re-emission exposes every character of the paper to that failure mode on every round.

This spec replaces full re-emission in **`academic-paper` revision mode** with a three-layer mechanism:

1. **Block anchor layer** — a deterministic script stamps every markdown block with a stable `<!--block:BNNNN-->` ID (same HTML-comment grammar as the shipped v3.7.1/v3.7.3 citation markers) and emits a **block manifest** (`block_id → hash`) that becomes part of the writer's revision context. IDs are content-independent and never renumbered.
2. **Patch document** — the writer's revision deliverable becomes a JSON list of block operations (`replace_block` / `insert_after` / `delete_block`), each carrying the target block ID, an `old_hash` precondition **copied from the block manifest** (the writer never computes hashes — §3.2), and the `roadmap_item_ids` it addresses. No full draft is emitted.
3. **Deterministic apply** — a script validates a whole-document base hash plus **all** per-op preconditions before touching anything (fail-closed, two-phase), applies the operations by **byte-span splicing** (untouched spans are copied from the original bytes, never re-serialized), assigns fresh IDs to inserted blocks, and emits an apply report. Blocks not named by an operation are preserved **byte-identical by construction** at the apply step (§3.4 bounds this claim against the finalizer's own legitimate marker mutations).

The honest claim — stated here once and repeated in §4 because it is the load-bearing boundary of the whole design: this mechanism **shrinks the silent-distortion surface from "the whole paper, every round" to "the blocks an operation explicitly touches."** It does NOT improve the quality of the edits themselves, and it is NOT a paper-recommended technique (§1.2).

## 1. Motivation and honest premises

### 1.1 The round-trip mechanism ARS currently runs

Re-emission sites in the current suite (first-party verified 2026-06-10):

| Site | Shape | Evidence |
|---|---|---|
| `academic-paper` revision mode (standalone; also what pipeline revision stages dispatch — "Resolved next stage: 4 (mode: revision)", `pipeline_orchestrator_agent.md:87`) | reviewer feedback → `draft_writer_agent` re-emits complete draft | `academic-paper/SKILL.md` mode table ("Revised draft with tracked changes"); `draft_writer_agent.md` § Output Format requires "[Complete paper text with all sections...]" |
| `academic-paper full` in-pair Phase 6 → Phase 4 revision loop (max 2 rounds) | evaluator block → writer Phase 4b re-emits `## Draft Body` | `academic-paper/SKILL.md` § v3.6.6 protocol — Phase 4b lint **requires** a full `## Draft Body` section, so this site cannot adopt patches without touching the contract structure; deferred to the Item 9 boundary (§7) |
| Four further internal loops (integrity FAIL correction, post-review Socratic coaching, deep-research internal, `academic-paper full` writer/evaluator attempts) | various | #89 Item 8 — explicitly NOT this spec's scope (§5.2) |

The current revision-round preservation story is entirely behavioral: the v3.7.1 finalizer idempotency clause promises "When evidence is unchanged across a revision pass, every marker is preserved byte-identical" (`pipeline_orchestrator_agent.md:718`) — but under full re-emission that promise rests on the LLM choosing to reproduce every untouched character faithfully. DELEGATE-52's frontier-distortion finding says precisely that this is the assumption that fails, and fails subtly. Under patch apply, the same promise becomes a property of the apply script: untouched blocks are not re-generated at all.

### 1.2 Honest premise 1 — this is an engineering inference, NOT a paper recommendation

Recorded in #89 ("Acknowledged limitations") and the Codex cross-model review on #83, and preserved here because it bounds what this spec may claim:

> DELEGATE-52 does **not** recommend diff/patch outputs. The paper says targeted programmatic modifications *could in principle* reduce corruption, but its **tested basic tool harness did not improve outcomes.**

That negative result is a counter-signal this design must face, not bury. We cannot determine from the paper *why* the tested harness failed (whether the models still rewrote large spans through the tools, whether there was no precondition/fail-closed layer, or something else). Therefore:

- The design difference this spec bets on — declarative patch + hash precondition + fail-closed deterministic apply + an escalation gate that excludes structural rewrites — is an **unvalidated hypothesis** about *why* a patch shape can succeed where a tool harness did not. §8.4 defines the measurement hook so the hypothesis is checkable instead of assumed.
- The one claim that does NOT depend on LLM behavior improving: under patch apply, a block no operation names **cannot** be silently distorted, because no generation pass runs over it. That is a property of the apply script, not of the model. Blast-radius containment is the honest core claim; edit-quality improvement is explicitly not claimed.

### 1.3 Honest premise 2 — Fable 5 system card re-baseline modestly strengthens the case

Per #385 (decision note) and the #89 progress comment (2026-06-09): the Fable 5 system card §6.3.3.4 shows a **missing-context hallucination regression — 87% vs Opus 4.8's 95%** on the unavailable-tool probe. Full re-emission asks the model to reconstruct the entire document, including spans whose grounding may have degraded or scrolled out of context by that round; a regression on behavior-under-missing-context enlarges exactly that risk surface. A patch shape shrinks what must be regenerated per round to the spans actually under revision. "Modestly strengthens" is the calibrated phrasing — this is corroborating context for an already rank-1 item, not the load-bearing justification.

### 1.4 Finding-to-decision traceability

| DELEGATE-52 finding (#89) | Design response |
|---|---|
| Full re-emission is the measured round-trip mechanism | Revision deliverable becomes a patch document; no full draft emitted (§3.2) |
| Frontier models corrupt by subtle modification, not deletion | Untouched blocks preserved byte-identical by construction (§3.3) |
| Sparse-severe: rare single-step critical failures dominate degradation | Two-phase fail-closed apply: one bad precondition rejects the whole patch with the file untouched — a stale-base apply cannot half-land (§3.3) |
| Global restructure corrupts more than local ops | No first-class structural ops, plus deterministic structural-shape triggers at apply time that route to explicit, user-confirmed escalation (§3.3, §3.6) |
| Interaction-length compounding | Items 4+5 shipped (#389) surface the count; patches additionally shrink per-interaction exposure |
| Generic LLM judges explain <25% of variance on hard semantic diffs | Preservation verification here is **not** LLM-judged: hash preconditions and byte comparison are deterministic (§3.3, §8) |

## 2. Existing skeleton this design builds on

- **Schema 7 Revision Roadmap** (`shared/handoff_schemas.md`): `RoadmapItem.id` (`REV-001`), `target_section`, `suggested_action`, `verification_criteria` — patch ops trace to these IDs.
- **Schema 8 Response to Reviewers**: `ResponseItem.change_location` ("section + paragraph" free text) — gains an optional machine-checkable sibling (§6).
- **HTML-comment marker convention** (v3.7.1 `<!--ref:slug-->`, v3.7.3 `<!--anchor:kind:value-->`): prose-embedded, render-invisible, mechanically extractable markers are an established, lint-guarded pattern in this repo. The block marker reuses the grammar. Naming note: `<!--anchor:...-->` locates a position in a **cited source**; `<!--block:...-->` locates a block in **the draft itself**. The token `block` is chosen (not `anchor`) so the two cannot be conflated by prompt or lint.
- **`content_hash` precedent** (Schema 9, SHA-256) for change detection.
- **#134 Slice 1 write guard**: `draft_writer_agent` is Bucket A — all Bash denied, writes fenced to `phase4_*/**` + `phase6_*/**` (`scripts/ars_phase_scope_manifest.json`). This *forces* the correct role split: the writer can only emit the patch document; only the orchestrator / main session can run the apply script (§3.5).
- **Revision tracking template** (#268 nested commitment ledger) — `commitment_type: restructure` is the existing enum value the escalation gate keys on (§3.6).

## 3. Mechanism design

### 3.1 Block anchor layer

**Marker grammar.** `<!--block:BNNNN-->` on its own line, immediately above the block it labels (no blank line between marker and block). `NNNN` = zero-padded decimal, monotonically increasing. IDs are **content-independent and never renumbered**; the next fresh ID is `max(existing) + 1` (computed by scan — no counter state file). A block's ID survives every edit to its text; identity is positional-historical, not content-derived. (A content-derived ID would change on every edit and defeat anchoring; content integrity is the *hash precondition's* job, carried in the patch, never stored in the document.)

**Who stamps IDs: a script, never the LLM.** `scripts/ars_anchorize_draft.py` (name final at implementation) stamps an un-anchored or partially-anchored draft. Idempotent: already-labeled blocks keep their IDs. The writer never invents, copies, or renumbers a block ID; the apply script rejects any `new_text` containing a `<!--block:` marker (§3.3). This closes the obvious failure of asking the LLM to maintain its own anchor discipline (skip/duplicate/drift), and is the same division of labor as v3.7.1: narrative side emits prose, deterministic side owns the bookkeeping.

**Block manifest — the hash source the writer copies from.** Anchorize additionally emits a machine-generated block manifest (JSON, written beside the anchored draft: top-level `base_draft_hash` + one `{block_id, old_hash, first_line_excerpt}` entry per block) that is included in the writer's revision-invocation context. This exists because the writer **cannot compute hashes**: `draft_writer_agent` is a Bucket A agent with all Bash denied (#134), and an LLM asked to "emit the SHA-256 of the block" would hallucinate one. The same goes for the document-level hash — the manifest carries `base_draft_hash` precisely so that **every** hash in the patch document, per-op and document-level alike, is a mechanical copy from a script-computed source. A mis-copied or invented hash is caught at apply time exactly like a stale one (fail-closed) — the manifest makes the honest path cheap; the apply check makes the dishonest path fail.

**Block segmentation (normative for the shared parser module used by both anchorize and apply).** Line-based scan:

- fenced code block (``` / ~~~ to matching fence) → one block, never split;
- ATX heading line → one block;
- contiguous table lines → one block;
- contiguous list run (including indented continuations) → one block (markers never interleave list items);
- contiguous blockquote run → one block;
- otherwise: a blank-line-separated text run that contains **no unsupported-construct pattern** (next rule) → one block;
- YAML frontmatter (leading `---` fence) → skipped entirely, never labeled, never patchable;
- an existing `<!--block:...-->` line attaches to the block that follows it.

**Unsupported-construct rejection (normative — what keeps the catch-all honest).** A bare "otherwise → text run" rule would silently swallow dialect it does not understand, which is mis-anchoring, not fail-closed. So the catch-all is explicitly guarded: a would-be text run is **rejected as unsupported** if it contains a setext-underline shape (a `===`/`---` line directly under a non-blank line), a raw-HTML block opener (line-initial `<tag`), or a footnote-definition opener (line-initial `[^...]:`)— detection of these shapes is deterministic even though parsing them is unsupported. The MVP supported surface is exactly the block classes listed above; everything else stops the pipeline loudly with the construct named.

**Malformed-state rules (normative — the parser fails closed, it never guesses):**

- a `<!--block:` line inside a code fence is fence **content**, not a marker (and is hashed as content);
- duplicate block IDs anywhere → reject the document (anchorize refuses to proceed; apply refuses the patch) — duplicates can only arise from hand-editing, and guessing which one is "real" would silently misroute patches;
- an orphan marker (marker line followed by a blank line or EOF, i.e. attached to nothing) → reject with a repair hint;
- net effect with the rejection rule above: dialect coverage (setext headings, raw HTML blocks, footnote definitions) is an **availability** gap to close at implementation (§10) — such documents cannot use patch mode yet — not a correctness risk.

**Anchorize trigger points.** (a) After Phase 4 initial-draft assembly, before the draft enters Phase 5/6 — so reviewers and the writer's revision invocation both see anchored text. (b) On revision-mode intake of a legacy (pre-anchor) draft: anchorize first, then proceed. (c) After an escalated full re-emission (§3.6): re-anchorize from scratch — a new ID generation; old patches never apply across a re-emission boundary (each patch is generated per-round against the current base, so no cross-generation application exists in the protocol).

### 3.2 Patch document

The writer's revision deliverable. JSON (schema at `shared/contracts/patch/revision_patch.schema.json`, final shape at implementation), emitted in a fenced code block alongside the human-facing revision log. JSON over YAML: the apply script schema-validates as step zero, malformed output is rejected wholesale and retried once (§3.6), and JSON avoids the YAML scalar/flow-sequence traps already documented in the #268 template work.

```json
{
  "patch_format_version": "1.0",
  "revision_round": 1,
  "base_draft_hash": "3c4d5e6f7a8b",
  "ops": [
    { "op": "replace_block", "block_id": "B0042", "old_hash": "a1b2c3d4e5f6",
      "new_text": "Revised paragraph text... (Smith, 2024)<!--ref:smith2024--><!--anchor:page:14-->",
      "roadmap_item_ids": ["REV-001"] },
    { "op": "insert_after", "block_id": "B0042", "old_hash": "a1b2c3d4e5f6",
      "new_text": "A new paragraph...\n\nAnd a second new paragraph...",
      "roadmap_item_ids": ["REV-001"] },
    { "op": "delete_block", "block_id": "B0050", "old_hash": "0f9e8d7c6b5a",
      "roadmap_item_ids": ["REV-003"] }
  ],
  "emitted_by": "draft_writer_agent"
}
```

**Operation vocabulary (closed, deliberately minimal):**

| op | fields | semantics |
|---|---|---|
| `replace_block` | `block_id`, `old_hash`, `new_text`, `roadmap_item_ids` | Replace the block's text. If `new_text` segments into multiple blocks, the **first** retains the target's ID and the rest receive fresh IDs in order (one paragraph legitimately becomes two; the anchor stays on the head) |
| `insert_after` | `block_id` + `old_hash` of the anchor block (or sentinel `"DOC-BODY-START"` with `old_hash` omitted), `new_text`, `roadmap_item_ids` | Insert new block(s) after the named block; the parser segments `new_text` and assigns fresh IDs in order. The anchor's hash is required because insertion *position* is meaningful only relative to the anchor's *content* ("after the paragraph that says X") |
| `delete_block` | `block_id`, `old_hash`, `roadmap_item_ids` | Remove block and its marker |

`DOC-BODY-START` = the position after YAML frontmatter (if any) and before the first body block. Frontmatter is never patchable (§3.1); there is deliberately no `DOC-START` that could land an insertion above it.

No move op (express as `delete_block` + `insert_after`). No first-class section-level or reorder ops. Stated honestly, in three tiers, because "no structural ops" alone would overclaim: (a) **section-scale restructuring shapes** (heading ops, section-count changes, high touched-ratio) are caught deterministically by the §3.3 structural-shape triggers; (b) a **content-faithful relocation** (delete + re-insert of byte-equal text) is recognized mechanically by the §3.3 pure-move check and recorded as such; (c) a **low-touch relocation-with-rewording** below the trigger thresholds can land as ordinary ops — its exposure is exactly the touched blocks themselves, the same prompt-level exposure class as any `replace_block` (§4), no worse and no better. The vocabulary shrinks and surfaces structural change; it does not claim to prohibit what composition can express.

**Constraints (all machine-checked at apply time):**

- `old_hash` = first 12 hex chars of SHA-256 over the block's normalized text (LF line endings; marker line excluded; block-level leading/trailing blank lines stripped; intra-line whitespace untouched — trailing double-space is markdown-significant). **Normalization exists for hash computation ONLY; it is never written back (§3.3).** 48 bits is ample: the hash is a per-target staleness/wrong-target check against the *named* block, not a lookup key and not a security boundary; a false pass requires the stale and current text of the *same block* to collide (~2⁻⁴⁸).
- `base_draft_hash` = same construction over the entire anchored base file's raw bytes. This is the document-level staleness gate (anything changed ⇒ reject whole patch); the per-op hashes additionally catch the *wrong-target* failure the document hash cannot — a writer naming a block ID whose content is not what it thinks it is (per-op hashes are **copied from the block manifest**, §3.1, never computed by the writer).
- Each `block_id` appears in **at most one** op, in any role. This single rule removes whole classes of op-interaction ambiguity (replace+delete of the same block, insert anchored on a deleted block, double-insert races on one anchor). Multi-block insertion is expressed inside one `insert_after.new_text`, not by repeating the target. Ops are defined **simultaneously against the base** — array order is not semantic; the apply script splices in base-document order (§3.3).
- `new_text` MUST NOT contain `<!--block:` markers (ID assignment is the apply script's exclusive authority) and MUST follow the v3.7.1/v3.7.3 citation-marker obligations for any citation it introduces — patch mode does not relax citation discipline; the finalizer resolves new markers on its normal pass (§3.4).
- `roadmap_item_ids` is required and non-empty on every op. Honest framing: the *presence* of the trace is machine-checked; whether the edit semantically serves that roadmap item remains an LLM/human-layer judgment. This makes Anti-Pattern 7 (revision scope creep) **visible** — an op must publicly claim which reviewer concern it serves — but does not deterministically prevent a mislabeled edit.

### 3.3 Deterministic apply

`scripts/ars_apply_revision_patch.py` (name final at implementation). **Two-phase, fail-closed:**

**Phase 1 — validate everything, touch nothing.** Schema-validate the patch; verify `base_draft_hash` against the base file's raw bytes; parse the base draft with the shared parser; check every op: target ID exists, `old_hash` matches the current normalized block text (the one exception: an `insert_after` targeting the `DOC-BODY-START` sentinel carries no `old_hash` — there is no anchor block to hash; the schema encodes this as the only legal hash-less shape), no duplicate targets, no `<!--block:` in `new_text`, `roadmap_item_ids` non-empty. ANY failure → exit non-zero with a structured report (op index, failure kind, expected vs actual hash) and the base file **byte-untouched**. There is no partial apply: a stale-base or hallucinated-target patch is rejected whole. This is the sparse-severe defense: the catastrophic single-step failure shape (applying edits against the wrong base) is made impossible by construction rather than improbable by prompting.

**Phase 2 — apply all, by byte-span splicing.** The load-bearing implementation constraint, stated normatively because the §4 headline claim is false without it: the apply script edits the original **byte stream**, not a parsed-and-re-serialized representation. The parser's role is to map block IDs to byte spans; ops are spliced at those spans in base-document order (simultaneous-against-base semantics — §3.2); every byte outside the spliced spans, **including untouched blocks' marker lines and the inter-block separator bytes**, is copied verbatim from the base. Hash normalization (§3.2) is a read-side computation only and never appears in the output. Segment inserted/replacement `new_text` and assign fresh IDs; write the result to a temporary file and atomically rename it into place as a new versioned artifact (supersession convention, `pipeline_orchestrator_agent.md:567`) — an interrupted apply leaves no partial artifact; re-parse the output and assert marker uniqueness + grammar as a post-write self-check.

**Structural-shape triggers (deterministic, advisory-by-classification).** §3.2's vocabulary has no first-class restructure op, but composed ops can still express one. Phase 1 therefore computes structural-shape flags mechanically: any op whose target or segmented `new_text` is a **heading block**; net section count change; and `blocks_touched / blocks_total` above a threshold (a **required Slice B ship decision**, not deferred tuning — the "re-emission wearing a patch costume" guard depends on it; whatever the value, the ratio itself is recorded in every report). Any flag raised ⇒ the apply refuses to proceed unless invoked with an explicit acknowledge flag, which the orchestrator may set only after the §3.6 escalation checkpoint. Honest boundary: detecting that a patch *touches structure* is deterministic; deciding that it *is* a restructure in the paper's sense remains a judgment — the trigger forces that judgment to happen at a visible checkpoint instead of never. And the triggers have a stated floor, not a pretended ceiling: a low-touch non-heading relocation rides below them by design (§3.2 tier (c)).

**Pure-move check (deterministic content-faithfulness for relocations).** When a patch contains both deletes and inserts, Phase 1 additionally compares normalized-text hashes: an inserted block whose hash equals a same-patch deleted block's `old_hash` is recorded in the report as a `pure_move` pair — a relocation whose content fidelity is *machine-verified*, not trusted. No similarity heuristics for the near-miss case (a moved-and-reworded block): that is undecidable mechanically, lands as ordinary touched-block exposure, and is exactly the kind of distortion re-review exists to judge — the report's delete/insert listing makes it visible to that judgment.

**Apply report** (JSON + human-readable summary, written beside the revised draft and carried in the same versioned-artifact trail — it shares the draft's lifecycle and is named as a required input to re-review and the integrity gates in the protocol doc): ops applied, new block IDs, per-op roadmap trace, structural-shape flags, and the headline counters — `blocks_total`, `blocks_touched`, `blocks_preserved_byte_identical`, `preserved_ratio`. The report is the provenance record that a round ran in patch mode (or, per §3.6, that it deliberately did not) and the data source for §8.4.

### 3.4 Sequencing with the cite-time provenance finalizer

Normative order per revision round: **anchorize (manifest refresh) → writer emits patch → apply → finalizer pass → next round.** The writer copies hashes from the manifest generated against the text it was shown, so nothing may rewrite the draft between manifest generation and apply (a finalizer pass in between would legitimately mutate `<!--ref:-->` markers and produce spurious hash mismatches). After apply, the finalizer's existing revision-loop rerun (`pipeline_orchestrator_agent.md:690,718`) resolves any newly inserted bare markers.

**The preservation claim is bounded to the apply step — stated precisely.** "Untouched blocks byte-identical" holds between the base and the apply output. The finalizer that runs *after* apply may still legitimately mutate `<!--ref:-->` status tokens inside untouched blocks when the joined evidence changed (acquire / verify / mark-read events) — that is its shipped, audited contract, not a leak in this design. So the full honest statement: **no LLM generation pass runs over untouched blocks (this design's guarantee), and the only post-apply mutations of those blocks are the finalizer's deterministic, evidence-driven marker token updates (the pre-existing contract).** The apply report covers the apply step; finalizer marker deltas remain visible through the finalizer's own output, and the two reports are deliberately not merged — they answer different questions. When evidence is unchanged, the v3.7.1 byte-identical idempotency promise (`:718`) is now trivially satisfied for untouched blocks rather than requested from the model: those bytes were never regenerated.

### 3.5 Roles, and the #134 write-guard fit

- **Emit** — `draft_writer_agent` (Bucket A): produces the patch document as its Phase 6-invocation deliverable, written inside its `phase6_*/**` fence, with hashes copied from the block manifest in its context (§3.1 — it cannot compute them: all Bash denied). It cannot run the apply script even if prompted to, for the same reason.
- **Apply** — orchestrator / main session (unconstrained by the Bucket A fence): runs anchorize and apply, owns the resulting versioned draft artifact. In Mode B (phase-by-phase cross-session use), the user runs the same scripts by hand; the protocol doc ships the exact commands (§10).
- **Schema 8 split follows the role split.** Several Response-to-Reviewers fields are knowable only *after* apply (`word_count_delta`, final `change_location`s, the IDs of inserted blocks). The writer therefore emits **provisional** response items (response text, status, decline justifications — the judgment content); the orchestrator completes the mechanical fields (`change_block_ids` incl. fresh insert IDs, word-count delta, counters) from the apply report before the response moves to re-review. Asking the writer to pre-state post-apply facts would be asking it to guess — the same failure shape the hash manifest exists to remove.
- This split is not incidental: the agent that wants the change cannot be the agent that lands it, mirroring the v3.6.7 partial-inversion discipline (narrative side emits, deterministic/audit side acts) and turning the #134 guard from a constraint into the enforcement of the design's role boundary.

### 3.6 Escalation and failure paths

**Structural-rewrite escalation (the only road to full re-emission).** Two trigger layers, because each catches what the other cannot:

- **Pre-drafting (prompt-level classification):** any roadmap item in the round demands restructuring — section split/merge/reorder, `commitment_type: restructure`, or the writer determines the requested change cannot be expressed in the op vocabulary.
- **At apply (deterministic shape detection):** a §3.3 structural-shape flag fires on an emitted patch (heading-block ops, section-count change, touched-ratio threshold) — catching the case where the writer *mis*classified a structural change as local and expressed it through composed ops.

Behavior on either trigger: STOP; surface a MANDATORY-checkpoint-style block to the user stating (a) which items / which ops are structural, (b) that proceeding by re-emission means the DELEGATE-52 exposure this mode exists to remove applies to the whole document for this round, (c) the alternatives — narrow the items, or (for the apply-time trigger) acknowledge the structural patch and apply it anyway with the flag recorded in the report. Only on explicit user confirmation does a round run as legacy full re-emission, after which the draft is re-anchorized (new ID generation) and the apply report records `mode: full_reemission_escalated` — provenance never pretends a patch round happened.

MVP granularity is **per-round, binary**: one confirmed restructure item ⇒ the whole round is full re-emission. A mixed round (patch the local items, re-emit only a restructured span) requires span-scoped regeneration semantics that this spec defers (§9 forward-scope) — the honest cost, stated plainly: **restructure-heavy revision rounds get no patch protection in the MVP**, on exactly the operation class the paper says corrupts most. What the MVP does change: that exposure is now explicit, user-confirmed, and provenance-stamped instead of silent and default.

**Hash-mismatch / validation-failure retry.** Apply rejection feeds the structured failure report back to the writer for ONE re-emission of the patch against the current base (mirrors the v3.6.6 retry-once convention). Second failure → escalate to user (options: re-anchorize + retry round, fall back to escalated full re-emission, or abort). Never auto-fallback to full re-emission on apply failure — fallback is always a user decision, because silent fallback would quietly reopen the exposure this design closes.

**Legacy drafts.** Revision-mode intake of a pre-anchor draft: run anchorize (idempotent, content-untouched — verified by the §8 byte-identity test), then proceed normally. No migration of historical artifacts.

## 4. Honest coverage claim

Stated in the #134-spec discipline (deterministic vs best-effort vs not-covered), because a preservation mechanism that overstates itself is the false-enforcement illusion this repo has twice refused to ship:

| Layer | Status |
|---|---|
| Untouched-block byte preservation **at the apply step** | **Deterministic by construction** — byte-span splicing; no generation pass runs over unnamed blocks. Post-apply, the finalizer may still update `<!--ref:-->` status tokens in untouched blocks under its own shipped, evidence-driven contract (§3.4 bounds the claim) |
| Stale-base / wrong-target application | **Deterministic fail-closed** — document-level `base_draft_hash` + per-op `old_hash`, two-phase validate rejects the whole patch |
| Hash provenance | **Deterministic source, mechanical copy** — hashes computed by anchorize into the block manifest; the writer copies, never computes; a mis-copy fails at apply |
| ID assignment integrity | **Deterministic** — script-owned; LLM-supplied markers rejected |
| Patch emission (op choice, edit quality, `new_text` content) | **Prompt-level.** The writer can still write a bad edit, miss a roadmap item, or address the wrong concern — inside the blocks it names |
| Roadmap traceability | **Presence machine-checked; semantic fit is not.** Scope creep becomes visible, not impossible |
| Structural rewrites | **Not patch-protected** — routed to user-confirmed escalation (§3.6); a confirmed re-emission round reopens full-document exposure, stated there |
| Restructure detection | **Three-tier (§3.2):** section-scale shapes → deterministic triggers; content-faithful moves → deterministic `pure_move` hash check; low-touch relocation-with-rewording → rides below triggers as ordinary touched-block exposure, visible in the report's delete/insert listing but classified by no machine. A *section-scale* structural patch cannot land silently; a *small* one can, at replace-equivalent exposure |

One sentence, because every summary of this feature must survive it: **diff/patch mode removes the silent-distortion channel for text the revision does not touch; it does not make the revision itself better.**

## 5. Scope

### 5.1 In scope (MVP)

- `academic-paper` **revision mode** (standalone), which is also what pipeline revision stages dispatch (mode: revision). Agent flow within the mode (8→5→6) is unchanged; what changes is `draft_writer_agent`'s revision-invocation deliverable (patch document instead of complete draft) and the orchestration step that applies it.
- The deterministic toolchain (shared parser, anchorize, apply) + schemas + tests + protocol doc + lint.
- Schema 8 additive delta (§6).

### 5.2 Explicitly NOT in scope

- **`academic-paper full` in-pair Phase 6→4 loop** — its Phase 4b lint contractually requires a full `## Draft Body`; patching it means redesigning the writer contract, which is the Item 9 boundary (§7). Deferred with rationale, not forgotten.
- **#89 Item 8's four internal round-trip loops** (integrity FAIL correction, Socratic coaching, deep-research internal, full-mode writer/evaluator attempts) — Item 8 audits those and applies this spec's shape "where structurally possible" per #89; each adoption is its own change.
- **`revision-coach` mode** — produces a roadmap from unstructured comments; emits no draft; nothing to patch.
- **Reviewer-side block references** (reviewers citing `BNNNN` directly in roadmap items) — forward-scope (§9); MVP keeps Schema 7 untouched and lets the writer map `target_section` → block IDs, since "which blocks to change" is already the writer's decision.
- Any runtime-enforcement claim beyond the apply script's own checks (no new hooks; #134 remains the write-path guard).

## 6. Schema deltas (additive only)

- **New:** `shared/contracts/patch/revision_patch.schema.json` (§3.2) + the block-manifest shape emitted by anchorize (§3.1; sidecar artifact, not a passport field).
- **Schema 8 `ResponseItem`:** optional `change_block_ids: list[string]` — machine-checkable sibling of the free-text `change_location`, cross-checkable against the apply report's op list. **Populated by the orchestrator from the apply report, not by the writer** (§3.5 — several Schema 8 fields are post-apply facts). Existing fields untouched; absent field = pre-patch-era response (valid).
- **Schema 7, Schema 9, Schema 13.1:** untouched. A passport-level patch/apply ledger is deliberately deferred until Item 9 decides what the revision contract gate needs to consume (§9) — same restraint as #134 Slice 2's "annotation, not ground truth" framing. *Recorded cross-model divergence (R1):* the reviewer argued a minimal passport pointer is load-bearing now, lest the apply report get lost to context hygiene / cross-session resume. First-party position: the report is a **file** in the same versioned-artifact trail as the draft (§3.3) — filesystem persistence is not at risk; what must not get lost is *consumption*, which the protocol doc fixes by listing the report as a required re-review / integrity-gate input. If Item 9 (or lived experience) shows file-plus-protocol is insufficient, the pointer lands there with a consumer attached, not speculatively here.

## 7. Interaction with Item 9 (forward note, no design here)

Item 9 (#89) extends the Schema 13.1 contract gate to revision mode. This spec intentionally produces the artifact that gate will want to gate: a structured, lintable deliverable (the patch document) with per-op acceptance surface (`old_hash` validity, roadmap trace, op-vocabulary compliance). When Item 9 designs `shared/contracts/writer/revision.json`, its acceptance dimensions can bind to patch properties instead of full-draft properties — and the full-mode in-pair loop (§5.2) becomes addressable in the same stroke, since both reduce to "what does a contract-gated writer emit in a revision round." Nothing in this spec presumes Item 9's answers; the patch schema carries `patch_format_version` so the contract can pin what it audits.

## 8. Validation plan (implementation round)

1. **Shared parser tests** — segmentation per block class (§3.1 list), idempotent anchorize (second run = byte-identical), anchorize-is-content-neutral (output minus marker lines = input), block-manifest agreement (per-block hashes AND `base_draft_hash` == apply-side recomputation), the §3.1 malformed-state rejections (duplicate IDs, orphan marker, marker-in-fence treated as content), and the unsupported-construct rejections (setext underline, raw-HTML opener, footnote definition each rejected **by name**, not swallowed into a text run).
2. **Apply script tests** — per-op positive/negative; `base_draft_hash` mismatch rejects; per-op hash-mismatch rejects whole patch with file byte-untouched (the two-phase test); duplicate-target reject; `<!--block:` in `new_text` reject; `DOC-BODY-START` insertion with and without frontmatter present + schema rejects a hash-less op of any other shape; multi-paragraph `insert_after` segmentation + fresh-ID assignment; multi-block `replace_block` (head keeps ID, rest fresh); structural-shape triggers fire on heading ops / section-count change / touched-ratio and block without the acknowledge flag; `pure_move` pair detection (byte-equal relocation recorded; reworded relocation NOT claimed as pure); temp-file + atomic rename (no partial artifact on injected failure); post-apply marker uniqueness.
3. **Byte-identity property test** — for arbitrary patches over fixture drafts: every block not named in ops — *including its marker line and adjacent separator bytes* — is byte-equal between base and apply output. This is the core claim (§4 row 1) tested directly, not asserted.
4. **Measurement hook** — apply reports accumulate `preserved_ratio` + escalation frequency. Two questions it must eventually answer: (a) what fraction of real revision rounds escape to full re-emission (if high, the MVP's per-round binary granularity is the wrong cut and §9 mixed-round work is justified by data); (b) whether patch-mode rounds show fewer downstream integrity-gate findings than re-emission rounds — the §1.2 hypothesis check, feeding the #184 eval-harness track when fixtures exist.
5. **Lint** — new `check_*` script asserting the draft_writer revision-invocation block carries the patch-output discipline (block-scoped string checks per repo convention) + schema example validation; wired into `spec-consistency.yml` + the pytest manifest; mutation tests per the established discipline (commit before mutating; case-aligned probes).

## 9. Slice roadmap (each independently shippable)

1. **Slice A — deterministic toolchain.** Shared parser + anchorize + apply + schemas + tests. Touches zero prompts; usable standalone by a careful user immediately. *Stops cleanly with value (the tools exist and are tested).*
2. **Slice B — revision mode adoption.** `draft_writer_agent` revision-invocation output contract (patch document), orchestration sequencing (§3.4), escalation gate (§3.6), Schema 8 delta, protocol doc + Mode B commands, lint. *This is the MVP ship gate target.*
3. **Forward-scope (post-MVP, each gated on need):** mixed-round span-scoped regeneration (gated on §8.4(a) data); reviewer-side block references in Schema 7; passport patch-ledger (gated on Item 9); Item 8 loop adoptions (tracked under #89); full-mode in-pair loop (gated on Item 9's revision contract).

## 10. Open items for the implementation round

- Script names final (`ars_anchorize_draft.py` / `ars_apply_revision_patch.py` proposed); shared parser module location (`scripts/_block_parser.py` proposed, underscore-helper convention); block-manifest filename + exact field set.
- Parser dialect extensions beyond the §3.1 normative core — setext headings, raw HTML blocks, footnote definitions. Per §3.1 these are availability gaps (the parser rejects what it cannot classify), so they gate *which documents can use patch mode*, not correctness. R3 P2 advisory on the raw-HTML detector: `line-initial <tag` is an explicit detector subset, not full CommonMark HTML-block coverage — implementation either documents it as the supported detector or widens it to the intended HTML-block shapes. Also: marker interaction with `formatter_agent` Phase 7 conversion (expectation: formatter strips `<!--block:-->` like other markers at format time — verify, don't assume) and with word-count conventions (whether `<!--...-->` lines are excluded from whitespace-split counts — align with however v3.7.1 ref markers are already handled, as one rule for all marker kinds).
- Patch emission format details: fenced-JSON robustness vs a sidecar file write into `phase6_*/`; max single-op `new_text` size guidance (a `replace_block` spanning the whole paper would be re-emission wearing a patch costume — likely folded into the touched-ratio trigger rather than a separate cap). Note the `touched_ratio` threshold **value** is NOT an open item in the deferrable sense — §3.3 marks it a required Slice B ship decision.
- Whether the apply report's `preserved_ratio` should also be surfaced in the Budget Transparency block shipped by #389 (one-line synergy, decide at implementation).
- Exact MANDATORY-checkpoint wording for the §3.6 escalation block (both trigger layers).

## 11. Ship gate + definition of done

**This design round:**

- [x] First-party verification of all current-state claims (re-emission sites, marker conventions, #134 manifest scope for `draft_writer_agent`, finalizer sequencing constraint).
- [x] Honest premises preserved verbatim where they bound claims (§1.2 paper inference + tested-harness negative result; §1.3 Fable 5 re-baseline, "modestly strengthens").
- [x] Spec written: mechanism, coverage claim, escalation, scope cuts, Item 9 boundary, validation plan, slices.
- [x] Independent cross-model design review (design-decision class) reached **CONVERGED: 0 P0 / 0 P1** (codex `exec` read-only, reasoning=high, 3-round trajectory). **R1** = 0 P0 / 10 P1 / 3 P2 → all addressed; 1 divergence recorded with rationale (§6 Schema 9 row). **R2** closure check = 10/13 CLOSED, 3 residuals + 2 new P2 → all addressed (catch-all guarded by unsupported-construct rejection; `base_draft_hash` added to the block manifest — the writer-can't-hash rule applied to the document hash too; relocation honesty restated as three tiers + `pure_move` check; `DOC-BODY-START` hash exemption encoded in validation wording; `touched_ratio` threshold promoted to required Slice B decision). **R3** = A–E all CLOSED, converged; 1 P2 advisory carried into §10 (raw-HTML detector subset).
- [ ] Spec PR merged closing #390; #89 progress comment updated (Item 7 design done → implementation tracked via Slice A/B follow-ups).

**Implementation rounds (Slices A/B):** quality pass → cross-model review at 0 P0/P1 → full pytest manifest green → PR per slice, per standing repo discipline.
