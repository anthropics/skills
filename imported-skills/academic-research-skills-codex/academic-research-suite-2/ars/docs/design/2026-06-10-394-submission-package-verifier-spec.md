# ARS #394 — Deterministic submission-package verifier (design-first)

**Status**: COMPLETE — all four §9 slices SHIPPED. Slice 1 (CLI skeleton + Family C + report schema + fixtures); Slice 2 (venue profile + intake Step 3 follow-up + Family B); Slice 3 (Family A residue scan + Family D assessment, see `2026-06-10-394-family-d-repro-lock-assessment.md`); Slice 4 (terminality: `terminal_policies.submission_package` + `--policy` / `--check-freshness` + orchestrator Stage 5 gate + formatter advisories section + `check_394_submission_policy.py`).
**Issue**: #394 (blindspot-audit F-5, adjudicated design-first).
**Decision trail**: 2026-06-10 researcher-blindspot audit; cross-model review corrected the initial claim — the formatter's prompt-layer checklist already exists; the gap is deterministic enforcement, not absence.

## 0. TL;DR

`formatter_agent.md` carries prompt-layer submission checks — the Pre-Output Final Checklist (content integrity, required elements, package completeness) plus the Journal Submission Adjustment Checklist (blind-review version, CRediT, Data Availability) — but every item is LLM self-checking, the same trust level citation verification sat at before #182 promoted it to a script gate. Submission-package errors are mechanical, high-embarrassment-cost, and script-verifiable. This spec designs `scripts/verify_submission_package.py`: a deterministic post-Phase-7 verifier with three check families (blind-review residue, venue limits vs actuals, reference integrity) plus a stretch assessment of `repro_lock` linkage. Advisory by default; terminality follows the `terminal_policies` opt-in model with a hard rule: **heuristic checks are never eligible for strict** — only deterministic checks can block.

## 1. Motivation and honest premises

### 1.1 What exists today

The Phase 7 formatter ends with a Pre-Output Final Checklist (~30 items across Content Integrity / Format Compliance / Required Elements / Submission Package). It is prompt prose: the same LLM that produced the package attests the package is fine. For most items that is acceptable — they need judgment. But a subset is *mechanical*:

- author metadata embedded in a "blind" PDF/DOCX is a string in a known field;
- a 9,400-word manuscript against a venue's declared 8,000 limit is one subtraction;
- a reference cited in text but absent from the list (or vice versa) is a set difference.

These are exactly the failures a desk reject is made of, and exactly what a solo researcher (no second pair of eyes) misses at 2 a.m. before a deadline.

### 1.2 Honest premise 1 — the verifier reads artifacts, not intentions

The verifier checks the *files in the output package* against *scholar-declared expectations*. It cannot know what the venue actually requires (it reads the intake-declared venue profile, §4), cannot judge whether an acknowledgment is de-anonymizing in context (it detects the section's presence in the anonymized variant), and cannot decide whether "our previous work" is a real identity leak (it flags the phrasing). Detection is deterministic; *meaning* stays with the scholar. This is the same division #182 drew: lookup answers "does this DOI resolve," never "is this citation appropriate."

### 1.3 Honest premise 2 — artifact ≠ rendered view

Blind-review residue lives disproportionately in places no visual scan reaches: PDF/DOCX metadata author fields, DOCX tracked-changes authors and comment authors, embedded file properties. A checklist run by re-reading the rendered text systematically misses this class (the deliverable is the raw file, not what it looks like). The residue scan therefore operates on raw structure (`python-docx` part XML, PDF info dictionary / XMP) — never on extracted display text alone.

### 1.4 Honest premise 3 — extraction dependencies are environment-shaped

PDF parsing needs a library (`pypdf`) that the repo's lint environment does not currently ship; DOCX parts turned out to be readable with stdlib `zipfile`+XML (slice-3 refinement, §9), so for DOCX the residual incompleteness class is corrupt/oversized artifacts rather than a missing parser. Either way, a check that silently skips when it cannot read its object reads as "covered" when it isn't — the #349 lesson ("a skipped safety test reads as covered"). Every check therefore reports one of `pass | fail | NOT-CHECKED(reason)` (plus `warn` per §3.3 and `not_applicable` per §3.1), and `NOT-CHECKED` is surfaced in the report header, never folded into `pass`.

## 2. Existing skeleton this design builds on

| Piece | Reuse |
|-------|-------|
| `terminal_policies` (v3.10, `shared/contracts/passport/terminal_policies.schema.json`) | New additive key `submission_package ∈ {advisory, strict}`; per-key absence = advisory (Invariant 7). |
| #182 gate shape (`verification_gate/` + `verify_passport.py` CLI) | Same shape: standalone CLI + callable API, detection unconditional, terminality policy-gated, finalizer/orchestrator is the policy evaluator. |
| `provenance_summary.md` carrier (#333) | Advisory findings land in a `Submission Package Advisories` section of the output package's existing advisory carrier — no new marker grammar, no ref-marker churn. |
| Intake Step 3 (target journal) | Extended to optionally collect the venue profile (§4) when a target journal is declared. Scholar-declared only. |
| `venue_type_provenance` no-inference rule (R-L3-2-D) | Mirrored: the venue profile is never scraped or inferred from the journal name — declared values only, absent = that check is `NOT-CHECKED(no venue profile)`. |
| Formatter Pre-Output Checklist | Stays. The script is the deterministic backstop for its mechanical subset, not a replacement for the judgment items. |

## 3. Check families (priority order, per the adjudication)

### 3.1 Family A — blind-review residue scan

Runs when the package contains an anonymized variant **or the venue profile declares `blind_review: double`**. The formatter's Journal Submission Adjustment Checklist instructs producing a blind-review version, but it is not a guaranteed artifact in the output package table — so the trigger is presence-or-declaration, and a declared-double-blind package with NO anonymized variant is itself a `fail` (the most basic residue of all: the blind version is missing). **Slice-3 refinements:** (a) the missing-blind-version fail carries its own check id **A7** (deterministic, strict-eligible) so the family-level trigger failure has a per-check carrier in the report contract; (b) an UNTRIGGERED Family A reports the new `not_applicable` status — visibly distinct from `not_checked`, so a single-blind package is not permanently reported as incomplete (`not_applicable` does not count toward `not_checked_count` and does not affect the exit code); (c) the anonymized variant is detected by filename stem token (`anonymized`/`anonymised`/`anonymous`/`anon`/`blind`/`blinded`); (d) A4's strict eligibility is declared via the venue-profile field `acknowledgments_forbidden_in_blind: true`.

| Check | Method | Class |
|-------|--------|-------|
| A1 PDF metadata authors | PDF info dict `/Author` + XMP `dc:creator` non-empty | deterministic |
| A2 DOCX metadata authors | `docProps/core.xml` creator/lastModifiedBy non-empty | deterministic |
| A3 DOCX revision/comment authors | `w:ins`/`w:del`/`w:comment` author attributes present in document parts | deterministic |
| A4 Acknowledgments present in anonymized variant | section-heading match in the anonymized file | deterministic signal, **advisory-only eligibility** (see below) |
| A5 Self-citation phrasing | pattern list ("our previous work", "our earlier study", "we previously showed", + zh-TW equivalents) over extracted text | **heuristic** |
| A6 Supplementary filename leakage | author-name tokens (from the non-anonymized variant's metadata) appearing in package filenames | heuristic (token match) |

**FP tolerance (load-bearing) — `signal_class` and `strict_eligible` are separate axes.** A1–A4 are deterministic *signals* (a hit is a fact about the file); A5–A6 are heuristic (legitimate prose — "our previous work *on this dataset* [12]" in a single-blind venue — and coincidental name tokens will false-positive). But deterministic signal ≠ block-worthy: A4's *signal* (heading present) is deterministic while the *judgment* (is this acknowledgment de-anonymizing?) stays with the scholar, so **A4 is `strict_eligible: false`** unless the venue profile explicitly declares acknowledgments must be removed from the blind version. **A5/A6 are advisory-only structurally** — excluded from strict terminality by class, not defaulted out of it. Net: only A1–A3 (plus profile-declared A4) are promotable by `terminal_policies.submission_package: strict`. Every check in the report schema carries both fields.

### 3.2 Family B — venue-declared limits vs actuals

Mechanical comparison of package actuals against the intake-declared venue profile (§4): manuscript word count (**B1**), abstract word count (**B2**), keyword count range (**B3**), required sections present (set comparison against `required_sections[]`, **B4**), reference count ceiling if declared (**B5**) — check ids assigned at slice 2. All deterministic; all promotable under strict. Without a venue profile: every Family B check is `NOT-CHECKED(no venue profile)` — never guessed from the journal name (R-L3-2-D mirror).

Word-count method must be declared in the report (the venue's counting rules differ — with/without references/captions). The profile carries `word_count_scope` so the comparison states what it counted; mismatch tolerance ±2% before `fail` (format conversion noise; same tolerance class as the formatter's existing <1% conversion check, widened because venue counting rules are coarser).

### 3.3 Family C — reference integrity

Two-way set check over the package source: in-text citation keys ↔ reference-list entries. **The marker path requires a join source**: `<!--ref:slug-->` markers (v3.7.1+) carry prose-sourced `ref_slug`s, which #182 deliberately keeps separate from `citation_key` (verify_passport refuses passport-only verification without the prose join for the same reason). The deterministic path therefore needs one of: the run's `citation_verification_summary[]` (already carries the per-citation join), a parsed `.bib` whose keys map to slugs by the documented relation, or an explicit scholar-supplied join map. With markers but **no join source**, Family C reports `NOT-CHECKED(missing prose-reference join)` rather than guessing. Non-ARS or post-converted sources fall back to format-aware citation-key extraction (`\cite{}` for LaTeX, author-year regex for Markdown/DOCX text) and the report header downgrades to `best-effort extraction`. Orphan in-text citation = `fail`; uncited reference entry = `warn` (some venues allow further-reading entries). Deterministic on the joined marker path; the fallback path is heuristic-classed (advisory-only), by the same rule as §3.1.

### 3.4 Family D (stretch) — `repro_lock` linkage assessment

`repro_lock` is documentation-only today and explicitly not read by integrity gates (`shared/artifact_reproducibility_pattern.md` — a recorded boundary). This spec does NOT overturn that. The slice-3 assessment question is narrower: when a passport carries `experiment_provenance[]` with a `repro_lock`, should the *submission verifier* (not the integrity gates) check the lock's **presence and shape** as part of package completeness — the same way it checks a Data Availability Statement's presence? Outcome of that assessment may be "no" (boundary stands untouched); the assessment itself is the deliverable. Until adjudicated, Family D ships nothing.

## 4. Venue profile (scholar-declared, additive)

New standalone schema `shared/contracts/submission/venue_profile.schema.json` (NEVER inside the passport entry schema — the Invariant 11 pattern):

```yaml
venue_profile:
  venue_name: string                  # display only, never used for inference
  word_limit: integer | null
  word_count_scope: enum [body_only, body_plus_references, all] | null
  abstract_word_limit: integer | null
  keyword_range: {min: int, max: int} | null
  required_sections: [string] | null  # e.g. ["Data Availability", "CRediT"]
  reference_limit: integer | null
  acknowledgments_forbidden_in_blind: boolean | null  # true ⟹ A4 strict-eligible (§3.1; slice-3 addition)
  blind_review: enum [double, single, open] | null
  declared_by: const "scholar"        # no other provenance value exists
```

All fields nullable: a partially-declared profile runs the checks it can and `NOT-CHECKED`s the rest. Collected at intake Step 3 when a target journal is named (optional follow-up, not a new mandatory step); storable and re-feedable across runs like any declared input.

## 5. Seams — where it hooks

1. **Standalone CLI (always available):** `python scripts/verify_submission_package.py <package_dir> [--venue-profile profile.yaml] [--passport passport.yaml]` → human-readable report + JSON (`submission_verification_report.json`). Works with zero pipeline context — a scholar can point it at any folder before any submission.
2. **Pipeline hook (Stage 5 FINALIZE, post-formatter) — explicitly a NEW package-level gate, not the ref-marker stamp path:** the v3.10 terminality machinery is finalizer-stamped ref markers + the formatter's stamp-only rule 11; this verifier runs *after* the formatter on the whole package, so that carrier cannot serve it. Instead the report itself is the evaluated carrier: it embeds a `package_fingerprint` (manifest of file hashes; the fingerprint excludes the report file itself AND `provenance_summary.md` — the advisory carrier is appended to AFTER the report is stamped, so including it would self-stale every evaluated report; the guard's threat model is manuscript/package drift, not the pipeline's own advisory carrier — slice-4 amendment, gate-1 review) and the policy slug in force at evaluation, plus an `inputs_fingerprint` over the external inputs (venue profile / passport / join map — Family B/C verdicts depend on them, and the package fingerprint cannot see them; gate-2 cross-model review), and the orchestrator MUST NOT reuse a report whose fingerprint, inputs fingerprint, or slug no longer matches (the freshness guard, package-level analog of the `policy_hash` stamp; mechanically: `--check-freshness --policy <resolved>` plus the reuse context's input flags, where a null-stamped standalone report never satisfies freshness). A FRESH report re-emits its policy verdict — same token and exit semantics as a live run — so a recorded terminal verdict can never silently evaporate across a resume (gate-2 review). Terminal signals are the CLI's stdout tokens (`TERMINAL-BLOCK policy=submission_package` / `VERIFICATION-INCOMPLETE` / `STALE-REPORT`), never raw exit codes — exit 1 also covers nonterminal heuristic fails (slice-4 amendment, gate-1 review). Advisory results append to `provenance_summary.md` (`Submission Package Advisories`); under `terminal_policies.submission_package: strict`, a strict-eligible `fail` returns the package to the formatter fix loop (bounded: 2 fix rounds, then surface to the scholar — mirroring the revision-loop cap philosophy) instead of emitting. **Strict fails closed on incompleteness:** a strict-eligible check that reports `NOT-CHECKED` under strict is `VERIFICATION-INCOMPLETE` and blocks emission exactly like a `fail` — otherwise a missing parser silently waives the one check class the scholar opted into blocking on (the fail-open hole). Advisory default is unaffected (`NOT-CHECKED` is surfaced, never blocking).
3. **Policy evaluation stays single-homed:** the orchestrator (finalizer side) decides terminality by reading `terminal_policies`; the script only reports per-check `{pass, fail, warn, NOT-CHECKED}` + class `{deterministic, heuristic}` (slice-1 reconciliation: §3.3 already assigns `warn` to the uncited-reference case, so the status set here carries it too — `warn` is advisory-only and never policy-promotable). The script never reads `terminal_policies` — same division as #182's gate (detection unconditional, terminality decided by the policy evaluator). **Slice-4 sharpening (maintainer-adjudicated Option B, 2026-06-11, gate-1 P0):** "single-homed" binds the *reading and selection* of the policy — the orchestrator is the sole reader of the passport key and sole selector of the value in force; it hands the already-resolved value down via the `--policy` CLI argument, and the script *mechanically applies* it (stamps `policy_slug`, emits the terminal stdout tokens, exits 4 on fail-closed incompleteness). The mechanical application lives script-side deliberately: fail-closed and token emission are then pytest-pinned behavior rather than lint-pinned prose, and — unlike `citation_existence`, whose signal and carrier both live in the LLM layer (passport aggregate, ref marker) — this gate's signal and carrier are both the script-produced report file. The AST-level single-homed guard (`check_394_submission_policy.py` invariant 4) enforces that the script never ACCESSES the `terminal_policies` key at runtime.
4. **No ref-marker change:** nothing in this design touches the v3.7.3 marker grammar; the carrier is the report file + `provenance_summary.md` section (the #333 precedent for "advisory needs a home but the marker slot is taken").

## 6. Boundary

- **Deterministic script layer only.** No LLM judgment inside the verifier (#182/#134 direction). Anything needing judgment (is this acknowledgment de-anonymizing? is "our previous work" a leak?) is surfaced as a flagged location for the scholar, never auto-resolved, never auto-edited. The verifier reads the package; it never writes manuscript content (read-only with respect to #134 write-scope).
- **Advisory by default.** `terminal_policies.submission_package` absent = advisory = current behavior plus a report. The invariant is scoped precisely: **no manuscript, ref-marker, or final formatted-artifact bytes change** for non-opting users. The report file is a new additive artifact, and `provenance_summary.md` gains an additive section — those are deliberate additions, not byte-equivalence claims.
- **Heuristic checks never block** (§3.1) — structurally, not by default.

## 7. Schema deltas (additive only)

1. `terminal_policies.schema.json`: new optional key `submission_package ∈ {advisory, strict}` (closed enum, per-key absence = advisory). Wired-but-narrow on arrival: strict promotes only deterministic-class `fail`s.
2. New `shared/contracts/submission/venue_profile.schema.json` (§4).
3. New report schema `submission_verification_report.schema.json`: per-check `{id, family, signal_class, strict_eligible, status, detail, location}` + header `{extraction_path, not_checked_count, package_fingerprint, policy_slug}` (the last two are the freshness-guard carrier, §5.2).

## 8. Validation plan (implementation rounds)

- Fixture packages: a clean package, a metadata-leaking DOCX (creator + tracked-changes author), a PDF with `/Author`, an over-limit manuscript with a declared profile, an orphaned in-text citation, a marker-path vs fallback-path pair. Mutation discipline per repo convention: every check gets a fixture that fails it and a test proving the failure fires.
- `NOT-CHECKED` honesty test: remove `pypdf` from the environment → PDF checks report `NOT-CHECKED(parser unavailable)`, exit code distinguishes "all checked, pass" from "passed what was checkable".
- Strict-path tests: strict-eligible `fail` + `submission_package: strict` → orchestrator fix-loop instruction emitted; non-strict-eligible `fail` + strict → advisory only (the structural exclusion holds); strict-eligible `NOT-CHECKED` + strict → `VERIFICATION-INCOMPLETE` blocks (fail-closed); stale report (fingerprint or policy-slug mismatch) → refused, never reused.
- Family C join test: markers present but no join source → `NOT-CHECKED(missing prose-reference join)`, never a guessed comparison.

## 9. Slice roadmap (each independently shippable)

Slices are **dependency-ordered, not priority-ordered** — §3's A/B/C/D order is the adjudicated *importance* ranking, but Family A needs new parser dependencies and the anonymized-variant trigger while Family C ships on existing repo machinery, so the cheapest end-to-end slice goes first. The importance ranking governs what gets cut if effort runs out, not what ships first.

| Slice | Content | Ships |
|-------|---------|-------|
| 1 | CLI skeleton + Family C (reference integrity, joined marker path + fallback) + report schema + fixtures | smallest end-to-end value; zero new parser deps |
| 2 | Family B (venue profile schema + intake Step 3 follow-up + limits checks) | first scholar-declared profile |
| 3 | Family A (residue scan; `pypdf` declared in requirements-dev — the DOCX parts are read RAW via stdlib `zipfile`+XML (`defusedxml` when available), a slice-3 refinement over the planned `python-docx`: the §1.3 raw-structure premise is served more directly and the DOCX residue class has NO missing-parser `NOT-CHECKED` hole; only the PDF scan can be parser-blocked, reported honestly per §1.4) + Family D assessment doc | the high-embarrassment-cost class |
| 4 | `terminal_policies.submission_package` key + orchestrator Stage 5 hook + freshness guard + strict fix-loop + VERIFICATION-INCOMPLETE fail-closed | terminality, last |

Advisory-only through slice 3; nothing blocks until slice 4 lands the policy key.

## 10. Open items for the implementation round

1. zh-TW self-citation phrasing list (A5) needs first-party curation — no anglophone-only pattern list. **CURATED (maintainer, 2026-06-10):** the slice-3 draft six (我們先前的研究/我們過去的研究/我們先前曾/我們已於先前/筆者先前的研究/本研究團隊先前) confirmed, plus 本文作者先前 (third-person self-reference; anchored on the 本文 prefix because bare 作者先前 matches 該作者先前, a cited third party). Shortened catch-alls like 我們先前 rejected — they false-positive on within-paper back-references (the same reason the English list binds "we previously" to a verb). Extend in place as usage surfaces.
2. Family D adjudication (§3.4): presence/shape check vs leaving `repro_lock` fully out — maintainer call at slice 3. **ADJUDICATED (maintainer, 2026-06-10): Option 2** — no check, the `repro_lock` documentation-only boundary stands, `venue_profile.required_sections` + B4 is the escape hatch. Rationale recorded in `docs/design/2026-06-10-394-family-d-repro-lock-assessment.md`; Family D ships nothing, permanently (the `D` prefix + `repro_lock_linkage` vocabulary stay reserved).
3. Whether the report's `package_fingerprint` should reuse the audit-snapshot hashing convention or a plain file manifest — decide at slice 1. **ADJUDICATED (slice 1):** reuse the audit-snapshot manifest convention (`scripts/audit_snapshot.py` `write_manifest`), adapted to package level: one `<package-relative-path>:<sha256>` line per file, LC_ALL=C byte-sorted, newline-joined with a trailing newline; the fingerprint is the SHA-256 of that manifest text. The report file itself is excluded (it cannot fingerprint its own bytes). Pinned by an independent reimplementation in `scripts/test_verify_submission_package.py`. **Slice-4 amendment (gate-1 review):** `provenance_summary.md` joins the exclusion set — the formatter appends the `Submission Package Advisories` section to it AFTER the report is stamped, so fingerprinting the advisory carrier would self-stale every evaluated report on its own findings.
4. LaTeX word counting (`texcount` vs detex-and-count) — declare the method, don't promise venue-exact numbers. **ADJUDICATED (slice 2):** naive detex (strip `%` comments and `\commands`, unwrap braces/brackets) + canonical whitespace-split (`shared/references/word_count_conventions.md`), zero new dependencies; the report's B1 detail names the method and the counted file, and the ±2% tolerance absorbs the divergence from venue-exact counters. `texcount` rejected for slice 2 (an external binary dependency for a precision the tolerance makes unnecessary).

## 11. Ship gate + definition of done (per slice)

Each slice: fixtures + mutation tests green, `NOT-CHECKED` honesty test green, CHANGELOG entry, and — for slice 4 — byte-equivalence proof that an advisory-default run changes no existing artifact. Design doc updates in the same PR as the slice that deviates from it.
