# v3.11 Roadmap (draft)

**Status:** DRAFT — candidate scoping inferred from open issues, not a commitment.
**Date:** 2026-06-01 (just after v3.10.0).
**How this was built:** the repo has no milestone mechanism; this draft is synthesized from
the open-issue set as of v3.10.0 ship. Every item links its source issue. Priorities and
final selection are the owner's call — this is a menu, not a plan of record.

> Theme candidate: **provenance + calibration hardening across artifact types** — almost
> every mature open item EXTENDS existing machinery (claim decomposition, field-norm
> calibration, citation verification, instruction/data boundary) rather than introducing a
> greenfield system, which keeps v3.11 scope tractable. The alternative framing is a
> narrower **citation-integrity release** anchored on the one P0 (#182).

---

## Tier 0 — ship-early, dependency-free (do regardless of theme)

The Co-Scientist design-lesson docs are S-scope, pure documentation, no code, no
dependencies — and **#223 (L4) updates the paper-derived issue template**, which every
future paper-derived sub-issue depends on. Landing these first costs little and unblocks the
boundary discipline for everything else.

- **#220** Co-Scientist L1 — hidden-ranking red line (design-lesson doc)
- **#221** Co-Scientist L2 — feedback-propagation user-approval gate (design-lesson doc)
- **#222** Co-Scientist L3 — transferable vs non-transferable mechanisms (transfer matrix)
- **#223** Co-Scientist L4 — control-plane ownership (who may write / rank / route) + issue-template update
- Parent epic: **#219**

---

## Tier 1 — mature spec, no blocking deps, high leverage

### Citation integrity (the one self-assessed P0)

- **#182** — Deterministic citation verification gate (Crossref/DOI/arXiv/PubMed lookup +
  source-text anchor; three status columns `lookup_verified` / `anchor_present` /
  `reviewer_approved`; a draft with any `lookup_verified: false` cannot reach "ready for human
  review"). **Scope: L** (new resolver module + caching + schema + tests). The #184 eval
  harness already left a hook ("verify_citation has not shipped — reconcile when it does"), so
  this closes a known forward-reference. **Highest leverage in the citation cluster.**
  - **Note (raised in review):** the gate FLAGS unverified citations (they stay visible — it
    is not hidden culling, so it does not cross the Co-Scientist L1 hidden-ranking red line).
    But "a draft cannot reach ready-for-review" is a *deterministic block*, and ARS philosophy
    is "the human decides at every gate." The #182 spec should state explicitly whether this
    block is hard (auto) or surfaced-for-human-override, so it reads as a flag-and-surface
    gate, not an AI culling decision. This is a #182 spec clarification, not a roadmap blocker.
  - **#250** (non-blocking) — gold-set coverage gap: the `false` class is only exercised by
    fabricated tuples, not real-but-unindexed citations. Closing condition (a paper unmatched
    across all four resolvers) is hard to satisfy and may stay open; tracked, not committed.

### Kim et al. peer-review failure modes (epic #217)

All four sub-issues have full specs naming exact files/lines.

- **#213** — Decompose multi-part claims before citation judgment (adds Step 0 sub-claim
  split + `PARTIAL` verdict; addresses the 76% partial-evidence error class). **M**
- **#214** — Sub-claim inventory before consensus aggregation in `editorial_synthesizer`
  (inventory primary key `Weakness` → `sub_claim`). Independently shippable from #213 (no hard
  blocking dependency), **but coordinate the `sub_claim` shape/vocabulary with #213** — both
  introduce sub-claim-level reasoning at different layers (citation vs synthesis) and will
  drift if specced separately. Land them in one pass or share the schema. **M**
- **#215** — Field-norm severity calibration (domain_reviewer must cite external literature
  for field-norm claims; DA gains `field_norm_boundary`; calibration miscalibration histogram). **M**
- **#216** — Reviewer-type asymmetry parity audit in Devil's Advocate (4th anti-sycophancy
  rule). DA text change is **S**; the authorship-metadata design question splits off as a
  separate, larger decision — not required to ship the text change.

### Kong et al. Tier A — ALL SHIPPED (no v3.11 work here; see stale-open cleanup below)

Cross-checked against git history (not just issue state): the entire Kong Tier A is already
in v3.10, even though several issues are still OPEN.
- A1 #256 — shipped (Schema 11 ledger + follow-ups #266/#268/#269).
- A2 #257 — shipped via `#270 feat: add idea-diversity advisories` (commit `9f60d11`, **before
  the v3.10.0 tag**).
- A3 #258 — shipped via `#267 feat: add version-family citation reconciliation` (commit
  `48378bb`, before the v3.10.0 tag).
- A4 #259 — shipped (CLOSED).

→ #256 / #257 / #258 are **open-but-shipped stale issues**, NOT v3.11 work. See the
stale-open cleanup item under Tier 2.

### Opus 4.8 behavioral-signal cluster (recent, 2026-05-29)

- **#273** — Calibration may be optimistic under same-model / rubric-aware judging; recommend
  cross-model evaluation as opt-in "for best results" (epistemic framing, not a gate). **S**
- **#274** — Concise reviewer output + a behavioral check that hard boundaries / DA
  non-softening hold under 4.8 after user pushback (guidance + verification). **S**
- **#272** — Treat retrieved external content as data, not instructions. **This is a separate,
  still-open SAFETY TRACK, not a low-cost guidance add.** The #134 design spec (§ "open
  items", line ~138) is explicit: "#272 remains a separate, still-open safety track … #134
  must NOT close #272 or claim any mitigation … revisit #272's home only when a concrete
  envelope substrate exists (Slice 3+)." Do **NOT** co-locate #272 with #134 or treat it as a
  quick guidance patch. If taken on in v3.11, it needs its own design pass on the
  instruction/data trust boundary — scope accordingly, or defer until the envelope substrate
  exists. (Resolved against the #134 spec text, which is explicit on this point.)

---

## Tier 2 — deferred-from-v3.10 + hygiene (S each)

- **#160** — Move `scripts/_test_helpers.py` → `tests/test_helpers.py` (drop the `sys.path`
  hack across ~24 import sites). `defer:v3.10`.
- **#151** — Evaluate generic repo-hygiene CI (gitleaks / detect-secrets). `defer:v3.10`;
  scope explicitly constrained to avoid maintainer-specific rules in a public repo.
- **#138** — Parallelize OpenAlex + Crossref calls per entry in the migration script
  (`ThreadPoolExecutor`, ~halves backfill wait). Verify the script is still the right target
  post-v3.10.
- **#242** — `venue_disclosure_policies.md` ACL row: revisit canonical source (Admin Wiki URL
  returns HTTP 418 to curl → needs a CI link-checker exemption or alternate URL).
- **Stale-open issue cleanup (not feature work, but do it this cycle).** Several Kong issues
  are OPEN but their implementation already shipped in v3.10 — git history confirms, even
  though the issues never got auto-closed: **#256** (A1, via #266/#268/#269), **#257** (A2, via
  #270 `9f60d11`), **#258** (A3, via #267 `48378bb`), and #259/#263 (already CLOSED). Verify
  each against the merged work and close. Leaving them open distorts any future roadmap read
  (this very draft's first pass mis-scoped #257/#258 as v3.11 work because they looked open).

---

## Tier 3 — needs an owner decision before scoping

- **#89 Item 7 — diff/patch revision mode.** Ranked #1 by #89's own analysis as the highest-
  leverage *unfiled* work; **no design doc, no dedicated issue**. To take it on, write a spec
  first. Decide consciously: scope into v3.11 or defer.
- **#244** (external — TriggerMinds "Structural Limitations" critique). Not a proposal; a
  discussion thread. Its two actionable children — **#246** (discipline-relative grading, also
  cross-linked from Kong A4 #259) and **#247** (dual-use scope clarification) — **already
  shipped and closed** (`#280 docs(#246,#247)`, `Closes #246` / `Closes #247`). So #244 itself
  is now "verify residual discussion → likely close or re-scope," NOT waiting on children.

---

## Explicitly NOT in v3.11 (per source epics)

- **Kong Tier B (#260 / #261 / #262)** — the Kong epic #255 tags B-track as a **v3.12
  candidate**, not v3.11. (B1 experiment provenance, B2 figure/table fidelity, B3 cross-paper
  contradiction — all have full specs and could be pulled forward, but the epic's own tiering
  puts them after v3.11.)
- The anti-pattern non-features the source epics list as first-class rejections (autonomous
  idea generation, autonomous experiment execution, hidden ranking, open-ended self-play).
  These are boundary entries for `POSITIONING.md` / `NEGATIVE_SCOPE.md`, not features.

---

## Open questions for the owner

1. **Theme:** broad "provenance + calibration hardening" (Kim subs + #182 + Opus-4.8
   guidance) vs a narrow "citation-integrity release" (#182-centered)? Note Kong Tier A is
   already shipped, so the v3.11 substance is really #182 + Kim (#213-216) + the two Opus-4.8
   guidance items (#273/#274), with the Co-Scientist docs as the cheap Tier 0 opener.
2. **#272 (instruction/data boundary):** the #134 spec quarantines it as a separate safety
   track needing an envelope substrate. Take it on in v3.11 as its own design pass, or defer
   until the substrate exists? (Do NOT fold it into general guidance.)
3. **#89 Item 7 (diff/patch revision):** the highest-leverage unfiled item — scope a design
   doc for v3.11, or defer?
4. **Pull Kong Tier B (#260/261/262) forward?** Specs are ready; only the epic's tiering holds
   them at v3.12.
