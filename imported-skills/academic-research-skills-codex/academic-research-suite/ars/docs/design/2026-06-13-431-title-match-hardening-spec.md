# ARS #431 — Title-match hardening (normalization + in-loop contradiction veto + per-candidate metadata corroboration)

**Issue:** #431 (split from #250 as the production-code defect; the #430 strict-xfail pins are the acceptance signal)
**Date:** 2026-06-13
**Type:** Architecture design spec — cross-index behavior change (runs the ranking-lift gate)
**Decision authority:** owner-confirmed scope (this session: "全三層一次到位" + "negation veto 納入,但保守"; v2 = "改" after the adversarial review)
**Prerequisites shipped:** v3.9.0 cross-index triangulation (`_text_similarity` single-sourcing across 4 clients), v3.11 four-index gate + `_resolve_doi_then_title` queried_by signal (C-V6(a)), #430 strict-xfail pin.
**Cross-model consult:** 2 design consults + 4 adversarial reviews, all gpt-5.5 xhigh. R1 found 4 P1s (→ v2); R2 found 1 P1 + a doc-P1 (→ v3, §0.4/§0.10); R3 broke the v3 whole with 4 P1s + 1 P2 (→ v4, §0.11); R4 broke v4 with 4 more P1s and named the **root cause** — the strength-2 `author_state==agree` tier, not the missing vetoes — proving the enumerated-veto path is whack-a-mole (→ **v5, §0.12: the architecture pivot to exact-title-or-bust**). The §1+ body is the v1 design-round record and stands unedited — where it conflicts with §0, **§0 wins**; within §0, the highest-numbered disposition block wins (§0.12 > §0.11 > §0.10 > §0.4).

## §0 amendment (2026-06-13, post-adversarial-review — FOUR review rounds; v5 is FINAL)

This block went through four adversarial review rounds. **Round 1** broke the v1 body
(resolver-layer gate + missing-metadata-compatible) with four P1s → v2. **Round 2**
broke v2 with one more P1 (year-only corroboration too weak) + a doc-P1 → v3
(§0.4/§0.10). **Round 3** broke the v3 whole (first review of §0.4 + the §0.3
anchored-prefix/neither-has-both wording, neither of which existed at round 2) with
four more P1s + one P2 → v4 (§0.11). **Round 4** broke v4 with four MORE P1s — and,
crucially, named the **architectural root cause**: the strength-2 `author_state==agree`
tier lets *any* non-exact high-overlap same-author/same-year title match, which is the
shared signature of an author's own *related-but-distinct* works (a correction and its
original; a reply and its target; Part I / Part II; Study 1 / Study 2; companion papers
with no ordinal at all). Three (or thirty) enumerated structural vetoes cannot close
that class — it is whack-a-mole, proven across four rounds. **v5 (§0.12) is the
architecture pivot:** title similarity + author/year can no longer *alone* promote a
**non-exact** title to `matched`; non-exact → `unresolvable`. This collapses the whole
related-work false-positive class (including cases no reviewer enumerated) and **deletes**
§0.11.1's three vetoes + the §0.11.3 fold as no-longer-needed. The **FINAL (v5)** logic
is §0.12; where any earlier §0 prose conflicts, **§0.12 wins**.

The v1 body (§1 onward) put the metadata gate at the **resolver layer** (after
`title_search` returns one best candidate) and let missing candidate metadata
default to "compatible." Round-1 P1s, all first-party reproduced:

| # | P1 finding | Reproduced | v2 fix |
|---|---|---|---|
| F1 | `Author Correction: <title>` (Nature, +1 yr, same surname, ratio 0.847) accepted as the original work | ✓ | **Notice-relation veto** (§0.3) |
| F2 | Candidate missing year+author ⇒ "compatible" ⇒ old title-only false-positive survives | ✓ | **Positive-corroborator requirement** (§0.4): missing ≠ compatible |
| F3 | `title_search` returns only `scored[0]`; a wrong high-ratio #1 that fails metadata hides a correct lower-ratio #2 ⇒ real work dropped to unresolvable | ✓ (`crossref_client.py:203` `return scored[0][0]`) | **Gate moves INTO the candidate loop** (§0.2) — the resolver-layer落點 in the v1 body is wrong |
| F8 | 90-day cache returns pre-fix `matched` without recompute; key has no gate version | ✓ (`verification_cache.py:45`) | **Cache decision-version bump** (§0.6) |

Plus P2s adopted: F4 (acronym normalization made non-destructive via `max(old,new)`),
F6 (morphological-antonym veto), F7 (`No.`-as-number guard), F9 (keep a client-layer
contract test, re-scoped), F10 (lift claim retracted — measured, not inferred).

The v2 architecture is **two layers, not three** — the v1 "client negation veto"
and "resolver metadata gate" collapse into **one in-loop acceptance decision** per
candidate, because F3 proved the decision must see every candidate, and the veto +
corroboration must apply to the same candidate together:

### §0.1 Layer 1 — non-destructive dotted-acronym normalization (`_text_similarity.py`)

`_similarity(a,b)` returns `max(ratio(base_norm), ratio(acronym_norm))` where
`base_norm` is today's normalization and `acronym_norm` additionally collapses
dotted acronym runs (`R.A.G.`→`rag`). Taking the **max** means the new pre-pass can
only ever *raise* a score — it is provably non-destructive (F4: `D.H.` vs `D. H.`
stayed at 1.000 under max, vs 0.981 if the acronym form replaced the base form).
The `(?:[A-Za-z]\.){2,}` collapse still never touches `A/B` / `R&D` / `Q&A` / spaced
`D. H.` (those aren't dotted runs); `e.g.`/`i.e.` collapsing is harmless under max.

### §0.2 Layer 2 — per-candidate acceptance decision (in the client candidate loop)

Each client's title-search candidate loop accepts a candidate as a title match iff:

```
ratio(cited, cand) >= 0.70
  AND NOT contradiction(cited, cand)          # §0.3 — negation/antonym/notice
  AND has_positive_corroborator(cited, cand)  # §0.4
```

The loop returns the **first candidate that passes** (candidates are already
ratio-sorted desc; F3's correct lower-ratio #2 is now reachable because #1 failing
the gate no longer ends the search). A no-pass loop returns no match.

This replaces the v1 "resolver layer does the gate" design: the gate is where the
full candidate list lives. `_resolve_doi_then_title` / `_resolve_arxiv_id_then_title`
keep their existing shape — they just consume a return value that is now
corroboration-gated rather than ratio-only. s2's `_lookup_by_title` already loops and
already has `year`; it gets the same in-loop decision.

### §0.3 contradiction(cited, cand) — three sub-vetoes, title-decidable

1. **Single-sided negation** (v1 §3.2, kept): negator set `{not, no, without, non,
   never, cannot}`; fires only when the symmetric negator-difference is non-empty AND
   residual overlap after stripping the differing negators ≥ 0.92. **`No.`-as-number
   guard (F7, v3 narrowing):** the guard keys off the **raw source text** — a `No.` /
   `no.` abbreviation form (dot present) immediately before a numeral is not a negator
   (`Experiment No. 2` ≠ negation). It does NOT key off the post-normalization token
   `no` followed by a numeral-like token, so the round-2 P3 (`No 1` stylized as
   "no one", `No I in team`) does not silently get the number-exemption — those stay
   subject to the ≥0.92 residual-overlap floor, which they do not clear anyway. P3
   logged as a known limit (§0.10), not separately defended.
2. **Morphological antonym (F6):** a closed phrase-pair list — `supervised/unsupervised`,
   `supervised/self supervised`, `increase(s)(ing)/decrease(s)(ing)`,
   `positive/negative`, `gain/loss`, `presence/absence`, `activation/inactivation`,
   `with/without`, `inclusion/exclusion`. Fires only when one side has X and the other
   has Y of a pair **and neither side has both** (so a survey titled "Activation and
   inactivation mechanisms…" vs a truncated "Inactivation mechanisms…" does NOT trip —
   the survey side carries both poles; round-2 P2 rejected on this rule, reproduced in
   §0.10). NOT broad stemming — an explicit curated list, because broad `un*`/`in*`
   stripping over-fires (`unique`, `index`, `infer`).
3. **Notice relation (F1, v3 = anchored prefix, owner-decided):** the candidate's
   title **begins with** a high-confidence notice form immediately followed by a colon
   or space boundary, which the cited title does not — `Author Correction:`,
   `Publisher Correction:`, `Correction to:`, `Erratum:`, `Corrigendum:`, `Addendum:`,
   `Retraction:`, `Retraction Note:`, `Expression of Concern:`. **Anchored at string
   start (`^`), not a bare substring** — so a legit content title that merely *contains*
   "comment"/"reply"/"correction" as subject matter is not vetoed. Owner decision this
   session: anchored-prefix tier, NOT the type-field-augmented tier (candidate payloads
   don't carry bibliographic type today; adding it is a larger change deferred). Residual:
   a real article titled `Correction to <topic>` with no colon variant is rare and fails
   to `unresolvable` (safe direction). `comment on` / `reply to` dropped from the anchored
   set — too collision-prone as content phrases even anchored; left to the metadata gate.
   These are *distinct related works* (a correction notice is a different DOI), so
   veto-as-distinct.

### §0.4 candidate acceptance — corroboration with conflict-rejection (v2 F2 + v3 round-2 P1)

**Round-2 P1 (reproduced, ratio 0.896):** the v2 `exact OR year OR author` gate
accepts `Federated learning for mobile keyboard prediction` (2019, Hard) vs `…mobile
health prediction` (2019, Li) — distinct works, same year, *different* author — on the
year corroborator alone. Year is not identity evidence. **The OR gate is replaced by
conflict-rejection + tiered identity strength (this is the final v3 logic; supersedes
the OR block):**

```
# A present field CONFLICTS if both sides present and disagree.
year_state   = agree(|Δ|<=1) | conflict | missing
author_state = agree(surname casefold-equal) | conflict | missing   # first-author family

reject  if ratio < 0.70
reject  if year_state == conflict   OR  author_state == conflict     # round-2 P1 core
accept  if exact_normalized_title                                     # strength 3 (metadata may be missing)
accept  if author_state == agree                                     # strength 2 (surname is strong ID)
accept  if year_state == agree AND author_state == agree             # strength 2
reject  otherwise   # ← non-exact title + year-only (author missing) is INSUFFICIENT
```

The decisive change: **a single weak field can never carry a non-exact-title match
while another present field conflicts**, and **year-alone never suffices for a
non-exact title**. Exact-title remains accept-on-its-own (it is the strongest signal;
covers the candidate-missing-metadata legit case). The resolver evaluates **all**
ratio-qualified candidates, drops hard conflicts, and returns the **highest
identity-strength** one (exact-title > author-agree), ratio breaking ties — so a weak
same-year candidate can never terminate the loop ahead of the real exact-title work
(round-2 second P1).

- **Acknowledged precision cost (§0.4-cost):** a real work cited by a *non-exact*
  title whose index entry *also* lacks the author (year-only available) → `unresolvable`.
  Stricter than v2, by round-2 P1's demand. The failure is `unresolvable` ("can't
  verify"), never a false `matched` — strictly the safer direction, C-V6(a)-consistent.
  Round-2 P2 fairly notes "rarity is asserted not measured" → §7 test plan adds a
  sampled candidate-metadata-coverage check per client + a missing-metadata-variant
  regression fixture, so the cost is bounded by evidence, not assertion.
- year tolerance ±1 (online-first vs print); author casefold-equal on first-author
  family; transliteration/particle surnames that differ-but-same-work fall back to
  exact-title (non-exact + differing surname → `unresolvable`, an accepted recall cost
  in the safe direction).

### §0.5 Verdict mapping (v3 wording fix — round-2 P2)

Per-candidate now, not per-fallback: a single vetoed/uncorroborated candidate does
**not** end the search. **Only when the candidate loop exhausts all ratio-qualified
candidates with none passing** does the title fallback yield no match. That no-match,
on the title-keyed path, reduces to **`unresolvable`** (coverage gap, C-V6(a)), never
`false`. ID-keyed entries whose ID missed keep `queried_by='id'` and the existing
fabrication signal. No new verdict enum value.

### §0.6 Cache decision-version (F8)

`_cached_verdict` (`contamination_signals.py`) returns a stored `matched` without
recompute, and the cache key `(citation_key, resolver_name, query_form)` has no
notion of *which decision logic* produced it. v2 adds a module-level
`RESOLVER_DECISION_VERSION` constant, bumped for #431, folded into the cache so
pre-#431 rows miss and force a live recompute. Implementation choice (decided at
impl time, recorded in the impl-amendment): either append the version to the stored
value and treat a version-mismatch as a miss (preserves the 90-day TTL for the new
logic, no destructive wipe), or extend `query_form`. The value-field approach is
preferred (no schema migration; old rows simply re-resolve once).

### §0.7 Pin rewrite (F9 re-scope)

- **negation pin** → client layer, marker removed, real passing assertion (title-only
  decidable). Unchanged from v1.
- **superstring pin** → asserted at the **candidate-loop / resolver boundary**, NOT
  deleted from the client surface (F9): a client-layer contract test still pins that
  `title_search` does not *promote* an uncorroborated superstring to a match, plus a
  resolver-level test for the distinct-work-with-mismatched-metadata case, plus the
  **new positive** (BERT short-name with matching metadata → matched) and the **F3
  ordering test** (correct lower-ratio #2 reached past a failing #1).

### §0.8 empirical validation (v3, 12/12, measured this session)

Full matrix re-run under the **v3** gate (conflict-rejection + identity-strength
ranking, §0.4): 4 defects → unresolvable; **round-2 P1 `year-only-distinct`
(same-year diff-author) → unresolvable**; BERT-shortname / acronym / year-drift-±1
exact-title → matched; **F1 correction-notice → unresolvable; F2 missing-cand-meta-
distinct → unresolvable; F3 second-candidate-is-real → matched (exact #2 reached past
conflicting #1); F6 antonym → unresolvable; F7 No.-as-number → matched**;
`prefer-exact-over-weak` (weak same-year #1 does not block exact #2) → matched;
`year-only-noexact` → unresolvable; controls (both-sides-"not" symmetric → matched;
author-confirm-no-exact → matched) all correct. The §0.4-cost false-negative
(non-exact + year-only) reproduced and accepted as the acknowledged precision
tradeoff. (The v2 15/15 matrix is superseded — its OR-gate let `year-only-distinct`
through; v3 closes it.)

### §0.10 Round-2 disposition (P1 fixed, 2 P2s rejected, P3 logged)

**P1 accepted + fixed** (the §0.4 rewrite): year-only corroboration of a non-exact
title; reproduced at ratio 0.896 (Federated keyboard/health, same year, diff author).
The second round-2 P1 (first-corroborated return can accept a weak candidate before
the real one) is the same fix — §0.4 now ranks by identity strength over *all*
candidates rather than returning the first passer.

**P1 (documentation) accepted:** v1 §4.4's residual claim ("only title+year+surname-all-
collision survives") is **false under §0** and is hereby marked **superseded by §0.4**.
The v3 residual is genuinely narrow again: a distinct work survives only if it shares an
**exact normalized title** with the cited work (or matching first-author surname with no
conflicting year). Same-year-only and same-surname-only-with-conflicting-year no longer
pass. This is materially tighter than the v2 OR-gate residual the reviewer flagged.

**P2 rejected — antonym truncation:** `Activation and inactivation mechanisms…` vs
`Inactivation mechanisms…` does NOT false-veto: the §0.3 rule requires "neither side
has both poles," and the survey side carries both `activation` and `inactivation`, so
the single-sided condition is not met (reproduced: `veto=None`). Rule already correct.

**P2 rejected — notice content-word:** `Bayesian correction to multiple testing` vs
`Correction to multiple testing in Bayesian models` does NOT false-veto under the v3
anchored-prefix rule: the cited title also contains "correction to," so the
prefix-not-in-cited condition fails. The remaining sliver (`Correction to <topic>` as a
genuine article title, candidate-only) is the acknowledged anchored-prefix residual in
§0.3 — owner-decided to accept rather than add a type field.

**P3 logged as known limits** (owner-decided, not separately defended): stylized `No 1`
= "no one" titles, `No I in team` roman-numeral collisions, and antonym/notice slivers
that survive the narrow rules. All fail in the **safe direction** (`unresolvable`, never
false `matched`), and are rare enough that the whole `citation_extraction` corpus is
unlikely to contain one. Consistent with the LLM-defect-class posture: this class is
*mitigated*, not *eliminated*, and the spec says so rather than over-claiming.

### §0.9 Ranking-lift claim retracted (F10)

The v1 §5 "precision-increasing ⇒ lift won't drop" inference is **withdrawn**.
`run_evals.py` reduces *static* `resolver_outcomes` from `expected_outcomes.json`
(`run_evals.py:114`) — it does not execute the clients, so the gold-set lift is
largely disconnected from this live-behavior change (the #250 finding's exact point).
v2 position: **lift is unknown until measured**; the PR runs the harness and records
the signed delta verbatim. Live-behavior correctness is pinned by the client unit
tests (mocked raw-API responses), which is where #250 concluded this class belongs —
NOT by adding gold tuples (which #250 proved is architecturally a no-op here).

### §0.11 Round-3 disposition — v4 (4 P1s fixed, 1 P2 fixed; FINAL logic)

Round 3 was the first adversarial pass over the v3 *whole* — §0.4 and the §0.3
anchored-prefix / neither-has-both wording had not existed when round 2 ran. It broke
v3 with four P1s, every one a **false-positive** (distinct work → `matched`, the
dangerous direction), every one first-party reproduced on this machine, and every one
grounded by the reviewer in **real DOIs / arXiv records** (not hypotheticals). The v3
§0.8 "12/12" self-test is hereby **superseded** — it never exercised these cases.
This is the third consecutive round to break a self-tested-green design; the
metadata-gate-class "self-test passes" signal is treated as non-load-bearing
([[feedback_ship_gate_dual_track_not_optional]], [[feedback_ai_only_chains_fail_at_fluent_wrongness]]).

**Root-cause grouping (mine, not the reviewer's):** P1-a/c/d are *one* failure mode in
three guises — **`author_state == agree` (strength 2) wrongly merges related-but-distinct
works by the SAME first author in the SAME year** (a correction and its original; a reply
and its target; Part I and Part II of a serial). The strength-2 premise "shared surname is
strong identity evidence" *inverts* for an author's own related corpus: shared authorship
is exactly what these distinct works have in common, not what separates them. P1-b is a
separate root cause — **exact-title strength-3 bypasses metadata entirely**, which fails as
a class for low-information generic titles. Reproduction (this machine, synthetic titles,
`SequenceMatcher` per §0.1): P1-a ratio 0.857, P1-b 1.000, P1-c 0.896, P1-d 0.724, P2-e
0.991 — all ≥0.70, all triggering as the reviewer traced.

The v4 fixes. Two changes: a **fourth contradiction sub-veto** (§0.3 gains item 4)
absorbing P1-a/c/d, and a **strength-3 narrowing** (§0.4) for generic titles absorbing
P1-b. Plus a pre-veto lexical fold for P2-e.

#### §0.11.1 §0.3 item 4 — related-work structural-wrapper veto (P1-a/c/d)

`contradiction(cited, cand)` gains a fourth sub-veto. Fires (candidate vetoed as a
distinct related work) on ANY of three structural relations, each a guarded
title-decidable test — NOT a bare substring or a metadata question:

1. **Notice-prefix asymmetry made SYMMETRIC (P1-a fix).** v3 §0.3 item 3 only checked
   whether the *candidate* begins with a notice form. Round 3's P1-a is the **reverse**:
   the *cited* title is `Author Correction: <X>` and the candidate is the bare original
   `<X>` — candidate has no prefix, so v3 does not veto, and author+year agree → wrong
   `matched`. Fix: if **exactly one** side begins with a notice form (anchored `^`, the
   §0.3 item-3 set) and the other does not, **veto** (regardless of which side). If
   **both** begin with the *same* notice class, do not veto (they may be the same notice).
   This is the reviewer's minimal fix, adopted verbatim — symmetry introduces no new
   false-negative (a real article and its own correction are *always* distinct DOIs).

2. **Reply/comment wrapper (P1-c fix) — structural, NOT a re-added prefix.** v3
   deliberately *dropped* `comment on` / `reply to` from the item-3 anchored-prefix set
   ("too collision-prone as content phrases even anchored"). Re-adding them as bare
   prefixes would reintroduce exactly that. Instead this is a **wrapper-containment**
   test: veto iff one side matches a relation-wrapper shape — `^(reply to|comment on|
   reply to comment on|response to)\b … <X>` — AND the *other* side's normalized title is
   (near-)equal to the embedded `<X>` (the wrapper's payload after stripping the relation
   lead). i.e. one title literally *wraps the other whole*. A title that merely contains
   "comment" / "reply" as a content word does not wrap another candidate's full title, so
   it does not trip. Narrower than a prefix rule, and keyed on the structural
   wrapper-wraps-payload relation the reviewer named.

3. **Structural designator (P1-d fix).** Veto when the principal delta between two
   otherwise-high-overlap titles is a **serial designator** — `part`, `paper`, `chapter`,
   `volume`, `vol`, `version`, `v` — immediately followed by an ordinal (arabic `1/2/…` or
   roman `i/ii/iii/…`), AND the two sides carry **different** designator ordinals. Guards:
   (a) fires only if **both** sides carry a designator token of the *same* family with
   *differing* ordinals (`Part I` vs `Part II` → veto; `Part I` vs `Part I` → no veto =
   same work; `Part I` vs a title with no designator → no veto, handled by the metadata
   gate); (b) the roman-numeral reading is restricted to a closed `{i,ii,iii,iv,v,vi,vii,
   viii,ix,x}` set immediately adjacent to a designator word, so a bare `I`/`V` elsewhere
   in a title (e.g. "Section V results", roman-as-pronoun) is NOT read as a designator
   ordinal — this is the same safe-direction discipline as the §0.3 item-1 `No.` guard.

**False-negative check (all three):** each veto fires only on a *structural relation that
makes the two works provably distinct* (a correction ≠ its original; a reply ≠ its target;
Part I ≠ Part II). There is no legitimate "same work" that these shapes drop — the dropped
candidate is genuinely a different DOI. So all three fail in the **safe direction even when
they over-fire** (worst case: a real citation whose only index hit happens to be the
related work → `unresolvable`, never a false `matched`). New negative-control tests (§7)
pin that a content-word "comment"/"reply"/"part of speech" title is NOT vetoed.

#### §0.11.2 §0.4 — generic-title strength-3 narrowing (P1-b)

P1-b: two distinct 2022 `Editorial` records by the same first author (real Crossref DOIs
`…15131` / `…15467`) both normalize to `editorial`, both hit exact-title strength 3, both
have agreeing metadata → the gate cannot tell them apart and accepts one as `matched`.
exact-title strength-3 is a **metadata bypass**, and for a low-information generic title it
is unsound: the title carries no identifying content.

**The reviewer's fix is rejected as written.** Its rule — "if multiple exact-normalized
candidates are plausible → `unresolvable`" — depends on the client *seeing multiple
candidates*, which **re-treads R1-F3**: s2's public surface is `lookup(entry)` → a single
`{matched, paperId}`, and arxiv/title-search clients do not guarantee a multi-candidate
return. A collision-detection rule that only works when ≥2 candidates surface would silently
pass the single-candidate path — the exact落點 error round 1 already caught.

**v4 fix (candidate-count-independent):** a closed **generic-title denylist** (normalized
forms): `editorial`, `introduction`, `preface`, `foreword`, `letter`, `letters`,
`reply`, `comment`, `response`, `book review`, `review`, `erratum`, `corrigendum`,
`addendum`, `obituary`, `news`, `correspondence`, `commentary`, `acknowledgements`,
`in memoriam`, `front matter`, `back matter`, `table of contents`. When the **cited
title's normalized form is in this denylist**, exact-title alone does **NOT** confer
strength 3 — the candidate must additionally clear **author_state == agree AND
year_state == agree** (strength-2 metadata corroboration) to be accepted, and even then
yields `matched` only if no *other* qualifying candidate exists; absent that corroboration
(or with any conflict) it is `unresolvable`. Non-generic exact-title matches keep
strength 3 unchanged — the BERT-short-name / acronym / subtitle-variant legitimate cases
are not generic titles, so they are **untouched** (verified: none of those cited titles
normalize into the denylist). This fix works on the single-candidate path because it keys
off the *cited* title alone, not off seeing the collision.

**Residual (honest):** two distinct same-author same-year `Editorial`s *with* agreeing
metadata still cannot be separated by title+year+author — but that now requires the
near-duplicate-metadata collision §4.4 always named as the irreducible floor, not a bare
exact-title bypass. The denylist demotes generic titles *out of* the strength-3 bypass; it
does not claim to resolve a genuine same-author/same-year/same-generic-title collision
(that is `unresolvable` in the safe direction when corroboration is absent, and an accepted
known-limit when metadata happens to fully agree — materially rarer than the bare bypass).

#### §0.11.3 P2-e — `non-` hyphenation pre-veto fold

`Noninvasive` vs `Non-invasive`: the candidate tokenizes `non invasive` (hyphen→space),
surfacing a standalone `non` token; the cited `noninvasive` does not. Symmetric negator
diff = `{non}`, residual overlap after strip 0.971 ≥ 0.92 → §0.3 item-1 negation veto
fires on what is a pure spelling variant of the **same** work (reproduced: 0.991 base
ratio, veto fires). Safe direction (`unresolvable`), but systematic for common `non-`
compounds (non-linear, non-negative, non-convex, non-invasive). Fix: **before** the
negation veto's tokenization, fold hyphenated `non-<word>` to the solid form `non<word>`
(and symmetrically, so both sides agree) so `non` never surfaces as a standalone negator
token from a hyphenation variant. Scope: only the `non-`+hyphen case (the only negator in
the set that is also a productive prefix); `not`/`no`/`without`/`never`/`cannot` are not
prefixes and need no fold. This removes the false-veto without weakening genuine `not`/`no`
negation detection.

#### §0.11.4 Pin / test additions (extends §0.7)

- New **resolver/client negative-control tests**: notice-reverse (cited=correction,
  cand=original) → not matched; reply-wrapper → not matched; Part I vs Part II → not
  matched; generic `Editorial` same-author-year-without-extra-disambiguator → not a bare
  strength-3 accept.
- New **positive-control tests** (guard against over-veto): `Part I` vs `Part I` (same
  designator) → still matched on metadata; a content-word title containing "comment"/"reply"
  not wrapping another title → not vetoed; `Noninvasive`/`Non-invasive` variant → matched
  (P2-e fold); `Section V` roman-as-non-designator → not vetoed.
- The §0.8 "12/12" claim is replaced by a v4 matrix that includes all four round-3 P1
  cases + the P2-e case + the over-veto positive controls; re-run and recorded at impl time.

#### §0.11.5 Gate (before code)

Per owner decision this session: a **fourth** codex re-verify (gpt-5.5 xhigh) over the v4
logic — specifically whether the new item-4 vetoes over-fire on legitimate same-work titles
and whether the generic-title denylist drops any legitimate non-generic exact match — must
return **0 P1** before implementation begins.

### §0.12 v5 — ARCHITECTURE PIVOT: exact-title-or-bust (FINAL; supersedes §0.4 strength tiers + §0.11)

Round 4 returned not "one more case" but a **root-cause verdict**: the strength-2
`author_state == agree` tier is the defect. It accepts a non-exact high-overlap title on
shared first-author surname alone, and that surname is the *common* attribute of an
author's own related-but-distinct corpus, not a discriminator. Round 4's four P1s
(notice-reverse, `Authors' reply:` outside the wrapper anchors, `Study 1`/`Study 2`
outside the designator family, `Non-invasive` vs `Invasive` where the §0.11.3 fold
*erased real negation evidence* and produced a NEW false-positive) plus a no-ordinal
companion (`: Theory` vs `: Experiments`, ratio 0.878, which **no** enumerated veto
catches) prove the enumerated-veto path is whack-a-mole. **First-party reproduced (this
machine): all five ratios ≥0.70** (0.857 / 0.897 / 0.975 / 0.961 / 0.878), all
strength-2 accepts → wrong `matched`.

**The decision (owner-confirmed this session):** demote title+author/year so it can no
longer *alone* promote a **non-exact** title. The four-client topology forces this to be
the fix rather than the reviewer's "venue+volume+issue+page uniqueness": volume/issue/page
is **only retrievable from Crossref** (OpenAlex doesn't `select` it, arXiv has no such
concept, and **s2's `_lookup_by_title` returns only `{matched, paperId}` — it discards the
candidate dict entirely**, so it cannot even see candidate year/author today). The **only
disambiguator all four clients can compute is the exact normalized title**.

#### §0.12.1 The v5 acceptance logic (replaces the §0.4 tiered block)

```
reject  if ratio(cited, cand) < 0.70
reject  if year_state == conflict  OR  author_state == conflict      # conflict-rejection KEPT (§0.4)
# --- the pivot: NON-EXACT NEVER ACCEPTS ON METADATA ALONE ---
if NOT exact_normalized_title(cited, cand):
    -> not a match (this candidate); loop continues; exhaustion -> unresolvable
# --- exact normalized title ---
if generic_title(cited):           # §0.12.2 — exact but low-information
    accept only if an ID/DOI hit corroborates; else -> unresolvable
accept  (exact, non-generic)       # the one strong title signal, four-client-computable
```

- `year_state` / `author_state` (agree/conflict/missing) and the conflict-rejection line
  are **unchanged from §0.4** — a present-field conflict still rejects (kills round-2's
  same-year-different-author P1). What changes: **`missing`/`agree` metadata no longer
  *rescues* a non-exact title.** Author-agree and year-agree are demoted from "accept"
  signals to (at most) tie-breakers among already-exact candidates.
- **`exact_normalized_title`** uses the §0.1 normalization (lowercase + punctuation→space
  + collapse, with the non-destructive dotted-acronym pre-pass via `max`). So legitimate
  punctuation/case/subtitle/`R.A.G.`-acronym variants that normalize to byte-equal **still
  match at exact tier** — they are not the casualty.
- **Multi-candidate:** the loop still evaluates all ratio-qualified candidates and only
  exact-normalized ones can be accepted; among exact ones, ratio (==1.000) ties break by
  the existing order. If the only exact-normalized candidate is generic and no ID
  corroborates → `unresolvable` (the generic-collision case, now safe).

#### §0.12.2 generic_title(cited) — exact-equality classifier, NOT substring/endswith

`generic_title(t)` is true iff the **normalized cited title is byte-equal** to a member of
a closed genre/section/type set. **Exact set-membership only** — NOT a substring or
`endswith` test. The set (normalized forms):

```
editorial, guest editorial, editorial comment, introduction, preface, foreword,
letter, letters, letter to the editor, letters to the editor, reply, comment,
commentary, response, correspondence, book review, book reviews, review, news,
obituary, in memoriam, acknowledgements, front matter, back matter,
table of contents, abstracts, abstract, proceedings, keynote, panel discussion,
workshop summary, special issue, untitled, note, notes, highlights, errata,
erratum, corrigendum, addendum, author correction, publisher correction,
retraction, expression of concern, short communication, rapid communication,
brief communication, short report, brief report, technical report, meeting report,
conference report, case report, case study, research article, original article,
original research, short paper, perspective, perspectives, viewpoint, opinion,
discussion, summary, conclusion, conclusions, abstract only, supplementary material
```

**v5 round-5 expansion (P1-1 fix):** round 5 found the v4 set underinclusive — `Short
Communication` (Crossref: 100 exact records in the first 100 results, 11 in 2004, several
author-missing), `Case Report`, `Original Article`, `Publisher Correction`, etc. were NOT
in the set, so an exact match with missing candidate metadata fell through to `accept` — a
**dangerous** false-positive (reproduced this machine: `generic_title` returned False for
all 14 reviewer-named terms). The set above adds the common section/type/notice phrases +
plural/variant forms. **The expansion is purely safe-direction and introduces zero
false-veto** because it is byte-equality, not substring: re-verified this machine that
content titles which merely *begin with or contain* a type word — `Case Report of a Rare
Tumor`, `A Brief Report on Climate Models`, `Research Article Processing Charges in Open
Access`, `Discussion of Bell's Theorem`, `Summary of Product Characteristics` — are **all
NOT generic** (their normalized form ≠ the bare type word), so none is wrongly demoted.
The earlier `endswith` design was rejected for exactly the误傷 this byte-equality form
avoids (`Deep Learning Review` / `A Comprehensive Review` end in "review" but are real
content). A genre word still not in the set (e.g. a non-English equivalent) falls through to
the non-generic exact path — which still requires exact title, stricter than the old bare
strength-3 bypass, so the miss is in the **safe direction** (never a false `matched`).
**This set is the single source of truth: the implementation reads exactly this list, and a
regression fixture pins `Short Communication` / `Editorial Comment` / `Case Report` /
`Publisher Correction` (exact title + no citation ID) → `unresolvable`.**

#### §0.12.3 What v5 DELETES (this is a simplification, not another layer)

- **§0.11.1 — all three structural sub-vetoes (notice-symmetry / reply-wrapper /
  designator) are DELETED.** They existed to catch related-work false-positives that
  slipped through strength-2 author-agree. With non-exact titles no longer accepting on
  metadata, the entire class is gone *by construction* — the vetoes are dead code. (The
  §0.3 items 1–3 negation/antonym/notice vetoes from the v1/v3 design are likewise moot on
  the accept path, since a non-exact contradicting title was never going to reach `matched`
  anyway; they may be dropped from the implementation, or kept only as an early-skip
  optimization with **no** correctness role. Owner-decided: drop them to keep the surface
  minimal.)
- **§0.11.3 — the `non-` hyphenation fold is DELETED.** It only existed to stop a false
  *veto*; with the negation veto gone from the accept path, there is nothing to fold, and
  round 4 proved the fold itself manufactured a false-positive (`Non-invasive`/`Invasive`).
  Deleting it removes that regression outright.
- Net: the acceptance decision shrinks from "ratio + 3 contradiction sub-vetoes + a
  4-branch strength ladder" to "ratio ≥ 0.70 + conflict-rejection + exact-title (with a
  generic exact-equality carve-out)". Fewer moving parts, smaller client diff, easier to
  pin.

#### §0.12.3b Cache decision-version is MANDATORY in v5 (P1-2 fix — ship blocker, not optional)

§0.6 (F8) offered the cache decision-version bump as an *implementation choice*. **In v5 it
is non-optional.** Round 5 reproduced (this machine) the bypass: `_cached_verdict`
(`contamination_signals.py:226`) returns a stored `matched` whenever the payload has a
`matched` key, with **no decision-version check**, and the SQLite key
`(citation_key, resolver_name, query_form)` carries no version
(`verification_cache.py`). So a **pre-v5 row** written under the v3/v4 author-agree logic —
e.g. `{"matched": true, "matched_by": "title", "queried_by": "title"}` for a `Study 1` vs
`Study 2` same-author pair — is returned as `matched` and **`client.title_search` is never
called**, bypassing the entire v5 loop. Confirmed: stale `matched=True` → `unmatched=False`,
no live call. This is a **dangerous false-positive path that survives the pivot** if the
cache is not invalidated.

**Mandatory in the v5 implementation:**
- Add a module-level `RESOLVER_DECISION_VERSION = "431-v5"`.
- Fold it into the cache: either append it to the stored value and treat an absent/mismatched
  version as a **miss** (preferred — preserves the 90-day TTL for new rows, no destructive
  wipe; pre-v5 rows simply re-resolve once under v5), or extend the cache key. The value-field
  approach is preferred (no schema migration).
- A pre-v5 row (no version field, or version ≠ `431-v5`) MUST force a live recompute.
- **Regression test (required):** a stale `{"matched": true, "matched_by": "title"}` row with
  no decision version → treated as a miss → `client.title_search` IS called → v5 logic decides.

This is the §0.6 mechanism made load-bearing, not a new design — but it is a **release gate**:
without it, the entire #431 fix is a no-op for every citation already cached under the old
logic (up to 90 days of stale `matched` rows).

#### §0.12.4 Empirical validation (this machine, v5 — 17/17)

A 17-case matrix under the v5 logic: **all 11 dangerous cases → `unresolvable`** — the four
round-1/2 defects, round-2's same-year-different-author, **all four round-3 P1s**, **all
round-4 P1s including the no-ordinal `Theory`/`Experiments` companion that no enumerated
veto caught**, and the generic `Editorial`/`Guest Editorial` collisions. **All five
legitimate positives → `matched`** — exact subtitle variant, `R.A.G.` acronym,
case+trailing-dot, exact full-title, generic-with-ID. The one acknowledged recall-cost case
(non-exact same-author, ratio 0.895) → `unresolvable`, as designed. Separately verified:
**`BERT` vs `BERT: Pre-training of Deep Bidirectional Transformers…` has ratio 0.096** — it
never cleared the 0.70 threshold under *any* version, so v5's removal of author-agree has
**zero** effect on it; the legitimate BERT short-name match was always going to come from
the **ID hit**, never from the title-fallback metadata tier.

#### §0.12.5 §4.4 / §0.8 / §0.11.4 reconciliation + BERT acceptance restated

- v1 §4.4's residual claim and the §0.8 / §0.11 "N/N matrices" are **superseded** by
  §0.12.4. The v5 residual is the genuine irreducible floor: a **distinct work sharing an
  exact normalized title** with the cited work (e.g. two same-author same-year
  non-generic identical titles) — far rarer than the substring/related-work classes v5
  closes, and generic exact-title collisions are themselves now gated behind an ID hit.
- **BERT short-name acceptance (was a v3 §0.7/§0.11.4 positive-control) is restated:** the
  legitimate "short name cited, long title indexed" match is verified via the **ID/DOI
  hit**, not the title fallback. The pin set is updated accordingly: the title-fallback
  positive-control becomes an **exact-normalized** legitimate variant (punctuation/case/
  acronym), and the BERT-by-short-name expectation moves to the ID-resolution path tests.
  This is an honest recall tradeoff stated in the open: a real work cited by a **non-exact**
  short title **with no resolvable ID** now returns `unresolvable` (safe direction,
  C-V6(a)-consistent), where v3 would have accepted it on author-agree.

#### §0.12.6 Gate (before code) — supersedes §0.11.5

A **fifth** codex re-verify (gpt-5.5 xhigh) ran over the v5 logic — questions (a) generic
collision the classifier misses, (b) classifier dropping a legitimate exact match, (c) any
*non-exact* false-positive path left.

**Round-5 result (2026-06-13):** the reviewer **confirmed the architecture** — *"the live v5
candidate-loop shape itself does block non-exact metadata rescue"*, and BERT-class no-ID
recall loss is *"safe-direction and not P1."* It found **two P1s, both
implementation-completeness gaps, NOT architecture defects** (a categorical change from
rounds 1–4, each of which broke a design layer):
- **P1-1 (question a, accepted + fixed):** the v4 generic set was underinclusive — `Short
  Communication` / `Case Report` / `Original Article` / `Publisher Correction` etc. fell
  through to `accept` on exact-title + missing candidate metadata. Reviewer grounded it in
  Crossref (100 exact `Short Communication` records, 11 in 2004). Fixed by the §0.12.2 set
  expansion; first-party verified the expansion is byte-equality so it adds **zero**
  false-veto (content titles containing a type word stay non-generic).
- **P1-2 (question c, accepted + fixed):** stale **pre-v5 cache** rows (`matched_by=title`)
  bypass the v5 loop entirely (`title_search` never called) because the cache has no
  decision-version. This is the §0.6 mechanism — round 5 correctly flags it as **non-optional
  in v5** (without it the fix is a no-op for up-to-90-days of cached rows). Made mandatory in
  §0.12.3b with a required stale-row regression test.

Question (b) **held** (byte-equality classifier drops no legitimate non-generic exact match).
Both P1s are **"expand a closed list" + "make an already-specified cache bump load-bearing"**
— no new design decision, nothing for a further spec round to re-litigate. **Owner decision
(this session): the two fixes are spec-complete; correctness of the *expanded list's
completeness* and the *cache-version implementation* is verified at the implementation-layer
ship gate (`/codex review` + `/security-review`, 0 P1/P2) — which inspects real code — rather
than a sixth round of pure-spec re-verify. Five rounds of spec re-verify have converged: the
marginal finding is now "add denylist terms," which is the signal the spec layer is done and
implementation + its own dual-track gate should take over.**

### §0.13 Round-6 disposition — P2 fixed, one P3 logged (post-code dual-track gate)

The shipped code went through the dual-track ship gate (security-review: 0 P1/P2;
codex review: gate PASS / 0 P1). Codex raised **one P2**, now fixed, and on
re-verification of the fix named **one further precision sliver**, logged here as a
known limit (owner-decided, not engineered away).

**P2 (fixed).** `exact_normalized_title` originally compared *only* the
dotted-acronym-collapsed forms. That regressed a punctuation-only variant where exactly
one side is a contiguous initialism: `D.H. Lawrence` vs `D. H. Lawrence` is byte-equal
under the **base** normalization (`d h lawrence`) but unequal under the acronym form
(`dh` vs `d h`), so it wrongly fell to `unresolvable` — a recall regression. Fix: the
helper now returns `base-equal OR acronym-equal`, mirroring `_similarity`'s `max` and
honouring the §0.1 F4 non-destructive contract (the acronym pre-pass may only *add*
matches over the base form, never drop one). Re-verified first-party and cross-model:
the fix fully closes the regression and introduces no new false match from the OR
interaction (a pair is added only when base-equal, which is already the safe identity
signal). Pinned by `ExactNormalizedTitleHelperTest` in `test_431_exact_or_bust.py`.

**P3 (logged, NOT a P2 regression — see §3.1).** Re-verification surfaced the
acronym-collapse name collision: `C.A.T.`→`cat`, `R.A.G.`→`rag`, `C.A.N.`→`can` can
make a genuine dotted acronym byte-equal to a same-spelled ordinary word. **Unlike the
§0.10 P3s, this one fails in the UNSAFE direction** (it can promote two distinct works
to a false `matched`, not merely to `unresolvable`) — stated plainly here rather than
folded into the safe-direction batch. It is logged rather than fixed for three reasons,
none of which is "it's safe":
1. **Not introduced by the P2 fix.** The acronym branch is byte-for-byte unchanged
   across the fix; the *old* acronym-only `exact_normalized_title` already returned
   `True` for `C.A.T.`/`Cat`. It is intrinsic to the §0.1 pre-pass that predates this
   round, so it does not block the P2-closed verdict.
2. **Removing it forfeits the pre-pass's only purpose.** The pre-pass exists *to*
   collapse dotted acronyms so `R.A.G.`/`RAG` reaches an exact match. Any tightening
   that dodges `C.A.T.`/`Cat` (e.g. requiring the other side to also be dotted or an
   all-caps run) re-breaks the legitimate variant the pre-pass was added for, and would
   reopen the 5-round-settled "exact via acronym equality" design — i.e. it must be
   re-reviewed, not patched in passing.
3. **Vanishingly rare in a real citation corpus.** It requires a cited title whose
   token is a 2+-letter dotted initialism *and* a genuinely distinct work whose title is
   identical except that same token is the de-dotted word — a coincidence the
   `citation_extraction` corpus is unlikely to contain even once.

Consistent with the LLM-defect-class posture (§0.10): this class is *mitigated*, not
*eliminated*, and the spec says so — including the unsafe direction — rather than
over-claiming.

---

> The text below is the v1 design-round record. Retained for the reasoning trajectory
> (why the metric-only approach fails, the BERT-vs-ResNet structural argument, the
> consult calls). Where it says "resolver layer does the gate" or "missing defaults
> compatible," **§0 supersedes it.**

## 0. TL;DR

The title-fallback match criterion is `difflib.SequenceMatcher.ratio() >= 0.70` over
punctuation-stripped titles, shared by all four resolver clients via `_similarity`.
Character-level ratio scores **distinct works** above 0.70 whenever titles share a
long substring (superstring 0.815, negation 0.926, shared-prefix 0.808 / 0.729), so
a title-fallback hit on a *different* near-identically-titled paper is collapsed to
`matched` — the false-positive path #250 named.

**The load-bearing finding (empirically established, §2):** no single scalar
similarity metric clears both the four false positives AND the legitimate
carve-outs. The binding constraint is the acronym case (`R.A.G.` → `r a g` vs `rag`,
raw 0.750) — it survives *only* under character-level ratio, while the superstring/
shared-prefix cases are caught *only* by token/length signals. The two requirements
point in opposite directions. Worse, superstring-of-a-distinct-work (ResNet vs a
real embedded-devices paper) and superstring-of-the-same-work (BERT cited by short
name vs its full title) are **structurally identical at the title layer** — prefix
detection does not separate them; only metadata (year/author) does.

Therefore the fix is **not a better similarity formula**. It is a three-layer
re-architecture that demotes title similarity from "proof of identity" to "candidate
retrieval," and moves the identity decision to a metadata-corroboration gate:

1. **Normalization layer (`_text_similarity.py`)** — collapse *dotted* acronyms
   (`R.A.G.` → `rag`) before comparison so the acronym carve-out becomes an exact
   match and exits the metric conflict. Narrow: only `(letter.)2+` runs, never
   `A/B` / `R&D` / `Q&A`.
2. **Client negation veto (4 clients' `title_search` / s2 `_lookup_by_title`)** — a
   *narrow, high-confidence* single-sided-negation contradiction rejects a candidate
   from the title alone. Negation is a genuine semantic flip, not a metadata
   question, so it is safe to decide at the client layer.
3. **Resolver metadata gate (`_resolve_doi_then_title`, `_resolve_arxiv_id_then_title`,
   s2 `_lookup_by_title`)** — after a title hit, require year (±first-author surname
   when both sides carry authors) corroboration before promoting to `matched`. A
   superstring candidate with mismatched metadata → `unmatched`; on the title-
   fallback path that reduces to **`unresolvable`, not `false`** (C-V6(a): a
   title-keyed miss is a coverage gap, not fabrication evidence). BERT short-name
   with matching year+author → accepted.

**The one claim that does not depend on tuning getting "perfect":** a title-only
fuzzy hit can no longer *alone* clear a citation to `matched` — identity now
requires either an ID hit (unchanged) or metadata corroboration. Edit-quality of the
similarity score is not improved; what changes is what a title-alone match is
*allowed to claim*.

## 1. The defect, restated against the code

`_resolve_doi_then_title` (`scripts/contamination_signals.py:269`) runs the title
fallback and collapses any non-None hit straight to `matched`:

```python
hit = client.title_search(title)        # only title passed — no year
if hit is not None:
    return False, "title", queried_by   # hit != None  ⇒  matched-by-title
```

The two production consumers of `title_search` are both this shape (crossref +
openalex via `_resolve_doi_then_title`; arxiv via `_resolve_arxiv_id_then_title`).
s2 takes a different public surface (`lookup(entry)` → `{matched, paperId}`,
`semantic_scholar_client.py:114`) and **already passes `entry.get("year")`** into
`_lookup_by_title` (line 153) — but only as a `+0.05` *tiebreaker*, not a gate, so
s2 carries the same defect: a single wrong-year candidate above 0.70 still wins.

So `title_search` / `lookup`'s non-None return is currently treated as
**authoritative** (= matched). That is the contract that must change: it becomes
*candidate retrieval*, and the resolver decides identity. (Codex's adversarial
caveat — "widening title_search silently widens the clients' false-positive
surface" — is answered by Layer 3 adding the gate the same PR, not by widening alone.)

## 2. Empirical basis (stdlib difflib, measured this session)

REJECT = distinct works currently wrongly accepted. MATCH = legitimate, must survive.

| case | raw | token_set | token_sort | jaccard | len_penalty | want |
|---|---|---|---|---|---|---|
| superstring (ResNet vs …Embedded Devices) | 0.815 | 1.000 | 0.815 | 0.667 | 0.543 | REJECT |
| negation (Attention …All vs …Not All) | 0.926 | 1.000 | 0.926 | 0.833 | 0.772 | REJECT |
| shared-prefix (RL Healthcare vs Deep RL Robotics) | 0.808 | 0.871 | 0.808 | 0.667 | 0.707 | REJECT |
| shared-prefix (Fed Keyboard vs Fed Health) | 0.729 | 0.763 | 0.729 | 0.500 | 0.729 | REJECT |
| **acronym (R.A.G. vs RAG)** | **0.750** | 0.500 | 0.500 | 0.000 | 0.250 | **MATCH** |
| subtitle (punct/colon variant) | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | MATCH |
| case+trailing-dot | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 | MATCH |

**Reading:** every token/length/jaccard metric kills the acronym carve-out (it has
zero token overlap). Raw ratio is the only metric the acronym survives — and raw
ratio is the defect. No single scalar wins. This is the §0 finding, with numbers.

A composite title-only decision (raw≥0.70 AND len_ratio≥0.80 AND ¬single-sided-
negation AND content_jaccard≥0.55) was tested: it rejects all four false positives
and accepts acronym/subtitle/case — **but** it false-negatives `BERT:
Pre-training…Transformers` (short name, raw 0.794, len_ratio 0.700) vs the full
indexed title. That legit short-name citation has the *same shape* as the ResNet
superstring defect. **This is the proof that the length veto cannot live at the title
layer** (§4.2).

## 3. Design

### 3.1 Layer 1 — dotted-acronym normalization (`_text_similarity.py`)

`_normalize_title` gains a pre-pass that collapses dotted acronym runs *before*
punctuation→whitespace translation:

```python
_DOTTED_ACRONYM = re.compile(r"\b(?:[A-Za-z]\.){2,}")
# "R.A.G." -> "RAG"  (then lowercased by the existing path -> "rag")
```

Matched span: two-or-more consecutive `<letter>.` units at a word boundary. The dots
inside the matched span are stripped; everything else is untouched, then the existing
lowercase + punctuation-strip + whitespace-collapse runs unchanged.

**What this deliberately does NOT collapse** (codex-named false-collapse risks):
`A/B testing`, `R&D`, `Q&A`, `S&P 500`, `model A B`. None of these is a dotted run —
the `/`, `&`, and bare spaces are not matched by `(?:[A-Za-z]\.){2,}`, so they reach
the existing punctuation path as before. The pre-pass is *additive over the dotted
form only*; the byte-equivalent contract for every non-dotted title is preserved.

**Acronym-collapse name collision (round-6 P3, logged — see §0.13).** Collapsing a
dotted run can make a genuine acronym byte-equal to a same-spelled ordinary word:
`C.A.T.`→`cat`, `R.A.G.`→`rag`, `C.A.N.`→`can`. This equivalence class is intrinsic
to the pre-pass (it predates the round-6 base-OR-acronym fix and is the very behaviour
that earns `R.A.G.`/`RAG` its exact match). It is a *precision* sliver, not a recall
one — logged as a known limit in §0.13, not engineered away, because tightening the
pre-pass to dodge it would forfeit the only reason the pre-pass exists.

Effect: `R.A.G.` vs `RAG` → 1.000 (was 0.750). The acronym carve-out is now an exact
match and no longer the binding constraint for any downstream metric.

### 3.2 Layer 2 — narrow single-sided-negation veto (client layer)

A shared helper (in `_text_similarity.py`, single-sourced like `_similarity`):

```python
_NEGATORS = {"not", "no", "without", "non", "never"}
def _negation_contradiction(a: str, b: str) -> bool:
    """High-confidence title-only contradiction: the two titles are otherwise
    highly overlapping AND exactly one side carries a negator that is the main
    semantic delta. Narrow by construction — NOT a generic 'contains not' penalty."""
```

Gating conditions (all required, so a title that merely *contains* "no"/"not" is not
vetoed):
- the symmetric-difference of negator tokens is non-empty (one side has a negator the
  other lacks), AND
- removing the differing negator(s) raises `_similarity` to a high overlap floor
  (≥ 0.92) — i.e. the negation really is the principal difference, not one of many.

Applied inside each client's candidate loop: a candidate that clears the 0.70 ratio
but trips `_negation_contradiction(cited, candidate)` is skipped. Lives at the client
layer because negation is a semantic flip decidable from title alone (§4.3).

### 3.3 Layer 3 — resolver metadata gate + verdict narrowing

The real identity gate. After a title hit, corroborate with metadata before
promoting to `matched`.

**Cited-side metadata** is always available: `literature_corpus_entry.schema.json`
makes `year` and `authors` (CSL-JSON, `family`/`given`) **required**.

**Candidate-side metadata:** crossref/arxiv have `_extract_year`; openalex has
`publication_year`; s2 has `year`. First-author surname: crossref `author[0].family`,
openalex `authorships[0].author.display_name`, s2 `authors[0].name`, arxiv `<author>`.

**Gate (applied on the title-fallback path only — DOI/ID hits are unchanged):**

```
corroborated = year_compatible AND author_compatible
  year_compatible:   cited.year is None OR cand.year is None OR |cited.year - cand.year| <= 1
  author_compatible: (cited or cand lacks first-author surname) OR surnames match (casefold)
accept-as-matched  iff  ratio>=0.70 AND ¬negation_contradiction AND corroborated
```

- **year tolerance ±1** absorbs online-first vs print / preprint vs published
  (codex-named year failure modes). Missing year on *either* side → year_compatible
  defaults True (do not punish coverage holes — C-V6(a) spirit), so the author key
  and the negation veto carry that case.
- **author is corroboration, not a sole hard gate**: missing-author or
  transliteration/particle cases (codex-named) default compatible; a *positive*
  surname match strengthens, a clear surname *mismatch* with both present fails
  corroboration.

**Verdict on gate failure:** the resolver returns `unmatched` (the title hit is
discarded). On the fallback path `queried_by` is `title` for the no-ID case, so the
existing reducer maps it to **`unresolvable`** — a coverage gap, *not* `false`. For
an ID-keyed entry whose ID missed and whose title-fallback then fails corroboration,
`queried_by` stays `id` and the existing C-V6(a) path applies unchanged (the ID miss
is the fabrication signal; the failed title fallback does not manufacture a new one).
**No new verdict enum value is introduced** — this is purely "a title hit that
doesn't corroborate is not a hit."

s2 parity: `_lookup_by_title` already has `year`; it gains the same ±1 gate +
negation veto + (new) author corroboration, changing year from tiebreaker to gate.

### 3.4 Pin rewrite (the acceptance signal)

`test_title_fuzzy_false_positive_xfail.py` holds two strict-xfail pins. Post-fix:

- **negation pin** → stays at the client layer (title-only decidable), `xfail`
  marker removed, becomes a real passing assertion: `CrossrefClient.title_search`
  rejects the negated candidate from title alone.
- **superstring pin** → **moves to the resolver layer**. The title-only assertion
  (`title_search` returns None for the ResNet superstring) is *over-specified*: §2/§4.2
  prove it forces an over-broad length veto that false-negatives the BERT short-name
  case. Replaced by a resolver-level assertion: `_resolve_doi_then_title` returns
  `unmatched` for the ResNet superstring **when candidate metadata disagrees**, AND a
  **new positive test** that the same superstring shape **with matching year+author**
  (the BERT case) is accepted. Per codex: this is moving the assertion to the layer
  that has the information to make it, not weakening the contract — the contract being
  hardened is *resolver correctness*, and it is now stated explicitly in the module
  docstring (title search retrieves candidates; the resolver decides identity).

The file is renamed `test_title_fuzzy_false_positive.py` (the `_xfail` suffix no
longer describes it) and its header rewritten from "deliberately xfail" to the
resolved-contract description.

## 4. Honest premises and the calls codex made

### 4.1 This defect class cannot be closed by a similarity metric alone
Stated plainly (codex Q-d "honest assessment": Yes). Title-only fuzzy matching finds
*candidates*; it cannot *prove* work identity (BERT vs ResNet superstrings are
identical at the title layer). The correct product behavior is to narrow the claim,
not to chase a perfect scalar. If a future reviewer asks "why not just tune the
threshold," the answer is §2 + §4.2: it has been measured, and it whack-a-moles.

### 4.2 Why the length/content veto must NOT live at the client title layer
The composite title-only decision (§2) rejects all four defects but false-negatives
the legit BERT short-name citation, because superstring-of-distinct-work and
superstring-of-same-work are structurally identical and prefix detection does not
separate them (codex Q-3, confirmed: both are clean prefixes). A dropped real
citation → `unresolvable` → "looks unverifiable" is arguably *worse* than the false
positive it fixes. So length/content corroboration moves to Layer 3 where metadata
exists to separate the two; the client layer keeps only the negation veto (which has
no such false-negative).

### 4.3 Why the negation veto IS safe at the client layer
Negation is a genuine semantic inversion (`Learning X` vs `Not Learning X`), not a
metadata ambiguity — decidable from title alone (codex Q-2). The false-negative risk
(a legit title containing "not"/"no") is contained by the narrowness in §3.2: the
veto fires only when the titles are otherwise ≥0.92-overlapping AND the negator is
the single-sided principal delta. A title that merely contains "no" among many
differing tokens does not trip it.

### 4.4 What is explicitly NOT claimed
- Not claimed: the similarity score is more accurate. (It is the same `SequenceMatcher`
  plus one normalization pre-pass.)
- Not claimed: all real-but-unindexed false positives are eliminated. A distinct work
  that shares title AND year AND first-author surname with the cited work would still
  corroborate — but that is a near-duplicate-metadata collision, a different and far
  rarer class than the substring-similarity defect #431 targets.
- Not claimed: any change to DOI/ID-keyed verification. The gate is title-fallback-only.

## 5. Ranking-lift gate (#431 acceptance bullet 4)

`_text_similarity.py` and `contamination_signals.py` are **not** in the
`eval-harness.yml` path filter, but the four clients **are**. This PR touches the
clients, so the eval harness fires. The acceptance bullet requires *no negative
signed lift* on the `citation_extraction` gold set (or acknowledgment per the gate's
protocol). The change is precision-increasing on the fallback path (fewer
false-positive `matched`), which should not reduce ranking lift; if the signed lift
moves, §8 records the measured delta and the acknowledgment rather than silently
acking. **No silent cap** — the measured numbers go in the PR body.

## 6. Scope boundary

- **In:** the four resolver clients' title-fallback acceptance, the two
  `_resolve_*_then_title` resolvers, s2 `_lookup_by_title`, `_text_similarity`
  normalization + negation helper, the pin rewrite, new positive/negative tests.
- **Out:** DOI/ID-keyed paths (unchanged); the reducer / gold-set tuples (#250 is a
  no-op there, by its own trace — this spec does not reopen that); any new verdict
  enum value; `venue_type` corroboration (year+author is sufficient for the named
  cases; venue is a future tightening if a year+author collision is ever observed).

## 7. Test plan (each step gated)

1. Layer 1: `R.A.G.`→`rag` exact; `A/B`/`R&D`/`Q&A` unchanged; full
   `test_text_similarity.py` green (byte-equivalent contract for non-dotted titles).
2. Layer 2: negation pin → pass from title alone; a legit "...No Free Lunch..." style
   title with low overall overlap is NOT vetoed (new negative-control test).
3. Layer 3: four defect pairs → `unmatched`/`unresolvable`; BERT short-name +
   matching metadata → `matched` (new positive); acronym/subtitle/identical →
   `matched`; year ±1 tolerance + missing-year-defaults-compatible covered.
4. Regression: `test_crossref_client.py`, `test_openalex_client.py`,
   `test_semantic_scholar_client.py`, `test_arxiv_client.py`,
   `test_contamination_signals.py`, `test_verification_gate.py` all green.
5. ranking-lift: `run_evals.py` + `check_ranking_lift.py` on citation_extraction →
   record signed lift in PR body.
6. dual-track: codex review (gpt-5.5 xhigh) + security-review, 0 P1/P2 before merge.

## 8. Open decisions for owner review

1. **author-surname corroboration strictness** — current design: a *clear* surname
   mismatch with both sides present fails corroboration; missing/transliteration
   defaults compatible. Alternative: author as advisory-only (year is the sole gate).
   Recommendation: keep author as corroboration (it is what separates the BERT-vs-
   ResNet class when years happen to collide), with the conservative defaults above.
2. **year tolerance window** — ±1 chosen for online-first/print. Alternative: exact
   (stricter, risks the print-vs-online false-negative) or ±2 (looser). Recommend ±1.
3. **negation lexicon** — `{not, no, without, non, never}`. Add `lacks`/`absent`/
   `fails`? Recommend keeping the closed 5-set (each is an unambiguous negator;
   broadening invites the false-negative the narrowness is designed to avoid).
