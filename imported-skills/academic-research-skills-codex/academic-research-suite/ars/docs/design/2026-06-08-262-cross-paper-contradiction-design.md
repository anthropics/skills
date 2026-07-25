# #262 — Structured cross-paper contradiction inventory (synthesis layer)

**Status**: design (2026-06-08)
**Issue**: [#262](https://github.com/Imbad0202/academic-research-skills/issues/262) (Kong et al. 2026 META #255, Tier B)
**Target agent**: `deep-research/agents/synthesis_agent.md`
**Paper anchor**: Kong et al. 2026 (arXiv:2605.18661, L. Kong, "Roadmap & User Guide") §7.4.2 — "systems increasingly retrieve and summarize individual papers well, but still struggle with multi-paper relational reasoning, methodological lineage, and cross-paper contradictions."
**Sibling precedent**: [#261](https://github.com/Imbad0202/academic-research-skills/issues/261) (figure/table fidelity, prose-layer) and [#214](https://github.com/Imbad0202/academic-research-skills/issues/214) (synthesis sub-claim inventory, prose-layer) — both shipped prose-layer-only because producer and consumer are LLM agents, not a deterministic parser.

---

## Problem

`synthesis_agent` (Phase 3, Analysis) already has prose-level contradiction handling:

- **Anti-Pattern 3: Unresolved Contradictions** (synthesis_agent.md § Anti-Patterns) — bars "Some studies found X while others found Y" stated without analysis.
- **Step 3: Contradiction Resolution** (synthesis_agent.md § Process → Step 3) — a 5-step prose procedure: identify conflicting claims → compare evidence quality → examine context → assess method → verdict reconcilable/irreconcilable.
- **Output "Contradictions & Resolutions" table** (synthesis_agent.md § Output Format) — a 3-column prose table (Claim A | Claim B | Resolution).

What is **not yet** present, per Kong §7.4.2:

1. A **structured, inspectable inventory** of which paper-pairs were assessed and what the verdict was — the current prose narrative-discusses contradictions (reconcilable and irreconcilable alike) but does not make the *set of assessed pairs* and the *unresolved / checked-clear* pairs enumerable for the scholar to confirm.
2. **Explicit candidate-pair scoping** — the current pass relies on the LLM noticing contradictions ad-hoc during synthesis. For a large corpus there is no stated way to bound *which* pairs get looked at, and no honest statement of what the scan does and does not cover.

(A calibration reference is discussed later as an optional, non-shipping sanity-check — it is **not** a deliverable of this change.)

This is the cross-paper-relational sibling of #214 (which decomposed within-review sub-claims) and #261 (figure fidelity). All three **enumerate before asserting "addressed."**

## Scope decision (chosen: prose-layer-only — deliberately departs from the issue's literal acceptance)

**The issue's acceptance text overclaims, and following it literally would manufacture the exact "false rigor" the repo rejected in #261.** This section records why we depart from the issue wording and ship the lighter form.

The issue acceptance says "Synthesis output **schema** adds `contradiction_pairs[]` block" and the rationale invokes "downstream agents (formatter, integrity_verification) cannot **programmatically** check." Read literally that points to a JSON Schema + lint invariant + CI gold gate. But:

- The named "downstream consumers" — `formatter_agent`, `integrity_verification_agent` — are themselves **LLM agents reading a markdown report**. There is **no deterministic non-LLM parser** that consumes a contradiction block.
- The judgment that actually matters — "is this a genuine contradiction, or a conditional difference, or no material conflict" — is **irreducibly semantic and LLM-side**. A JSON Schema would validate that `paper_a` is a non-empty string; it would not validate that Paper A actually contradicts Paper B. That is field-presence rigor masquerading as fidelity rigor.

This is the same scope call #261 made — its rationale was that machine-validating the YAML shape proves field presence, not fidelity, and adds an unrequested maintenance surface, whereas #213 earned schema+lint only because it has a deterministic machine consumer. #262 has no machine consumer either.

**Decision: prose-layer-only.** Extend the existing `synthesis_agent` contradiction section with a YAML-shaped *markdown* inventory block + a scoping subsection + a worked `examples/` file. **No JSON Schema, no lint invariant, no CI gold fixture.** Vocabulary is aligned with the issue (`contradiction`, `conditional_difference`) to avoid drift, but no schema architecture is imported.

The departures from the issue's literal acceptance, to be stated plainly in the PR body:

| Issue acceptance (literal) | What ships | Why |
|---|---|---|
| "Synthesis output **schema** adds `contradiction_pairs[]` block" | YAML-shaped **markdown** block in the existing Contradictions section | No deterministic consumer; schema = false rigor (#261 precedent) |
| "Calibration gold set … **accuracy ≥ 0.75**" as acceptance | **No calibration artifact ships**; any future/manual calibration is recorded out-of-band (model/date/prompt + confusion matrix + per-class recall) and stays non-blocking | 20 LLM-judged pairs is too small and too nondeterministic across runs to be a hard CI gate; wiring it as one would be false precision |

## Field model (codex-corrected — the issue's draft model is not MECE)

The issue's draft field model has four defects, all carried into this corrected model:

1. **`conflict_type` mixed two orthogonal axes.** The issue enum `{contradictory, conditional_difference, resolved_in_synthesis}` folds a *conflict nature* (`contradictory`, `conditional_difference`) together with a *resolution status* (`resolved_in_synthesis`). These are separated into two fields.
2. **`insufficient_overlap` was referenced but not in the enum** (the `resolution_in_manuscript` required-when clause names it). It is now a first-class `pair_assessment` value.
3. **No evidence pointers.** `a_finding` / `b_finding` as free text invites the agent to state claims the papers do not make. Each side gains an evidence pointer grounded in the corpus context.
4. **`candidate_basis` was implicit.** Recording *why* a pair was checked makes the scan's coverage inspectable (and exposes same-camp bias — see scoping).

The shipped block (markdown, inside the existing Contradictions & Resolutions section):

```yaml
cross_paper_tensions:
  - pair_id: CP-001                      # synthesizer-assigned, stable within the synthesis
    paper_a: "<citation_key or ref slug>"
    paper_b: "<citation_key or ref slug>"
    candidate_basis: "shared RQ subtopic | shared construct/outcome/measure | opposite finding direction | bibliographic coupling | scholar flag | agent-noted cross-cluster"
    overlap_topic: "..."
    a_finding: "..."
    a_evidence_pointer: "..."            # where in the corpus context Paper A's finding is grounded
    b_finding: "..."
    b_evidence_pointer: "..."
    pair_assessment: "contradiction | conditional_difference | no_material_conflict | insufficient_overlap"
    resolution_status: "resolved_in_synthesis | flagged_unresolved | not_applicable"
    resolution_pointer: "Synthesis Report > Contradictions & Resolutions, ¶N"   # required when resolution_status == resolved_in_synthesis
    scholar_confirmation: "pending | confirmed | disputed"   # scholar-set; agent emits 'pending'
```

Field rules:

- **`pair_assessment` and `resolution_status` are orthogonal.** A pair can be `conditional_difference` + `resolved_in_synthesis`, or `contradiction` + `flagged_unresolved`. The two axes never collapse into one enum.
- **`resolution_pointer` is required iff `resolution_status == resolved_in_synthesis`** — a claimed resolution must point at where in the report it was resolved, so the scholar can confirm it. For `flagged_unresolved` / `not_applicable` the pointer is omitted.
- **`no_material_conflict` and `insufficient_overlap` pairs MAY be listed but are not obligations to resolve.** Listing a checked-but-clear pair documents coverage; it does not manufacture a contradiction. (This mirrors #214's `not-mentioned is NOT opposition` discipline — a checked pair that is clear is not a tension.)
- **`scholar_confirmation` is scholar-set.** The agent always emits `pending`; it never self-confirms (narrative-side / audit-side separation, below).
- **Evidence pointers cite the corpus context already in the prompt** — never invented, never read from entry frontmatter (v3.6.7 partial-inversion discipline).

## Candidate-pair scoping (recall-limited heuristic — NOT a sound algorithm, NOT MECE)

The issue framed scoping as "cluster-then-pairwise, O(K²) per cluster." That framing overstates what an LLM agent does: it does not execute an O(K²) enumeration; it is given a **candidate-selection heuristic** in prose. Calling it an algorithm with complexity guarantees would be dishonest unless a deterministic script built the clusters — and none does. So the design states it as bounded, recall-limited candidate generation.

Two failure modes are real and are disclosed in the output, not hidden:

- **Cross-cluster contradictions can be missed.** Two contradicting papers can sit in different topic neighborhoods; if neither the agent nor the scholar surfaces the cross-pair, it is silently absent. This is acceptable **only because the output never claims completeness** — it carries an explicit coverage note. If the synthesis ever asserted "all contradictions addressed," this would be a load-bearing hole.
- **Bibliographic coupling biases toward same-camp papers.** Papers citing the same priors tend to agree; cross-camp contradictions often have low citation overlap. Therefore **shared references are an *inclusion* signal, never an *exclusion* rule** — a low-coupling pair is not ruled out.

The heuristic, stated as guidance:

1. Generate **candidate edges** (not disjoint clusters). Include a pair if it shares an RQ subtopic, shares a construct/outcome/measure, shows opposite finding direction, is bibliographically coupled, or is scholar-flagged.
2. Bibliographic coupling and shared-RQ are inclusion signals; never use them to *exclude* a pair from consideration.
3. Deduplicate by sorted `(paper_a, paper_b)`.
4. Emit a **Coverage Note**: number of papers, candidate pairs considered, classes of pairs not exhaustively checked, and the explicit recall limitation ("this is a scoped advisory scan, not complete pairwise contradiction detection").

## Advisory-only / narrative-side discipline (inherited, not new)

`synthesis_agent` already runs under a strict narrative-side contract: it emits, it does not audit; it does not simulate audit steps; it does not read entry frontmatter (synthesis_agent.md § PATTERN PROTECTION + the citation-emission narrative-side rules). The contradiction inventory inherits all of it:

- The agent **emits** `cross_paper_tensions[]` and `pending` scholar confirmations. It does **not** decide whether the manuscript adequately addressed a tension — the scholar makes the final call (advisory-only).
- The agent does **not** claim to have run any external contradiction-checking tool, and output metadata must not claim an audit-passed state.
- Evidence pointers and findings come from corpus context in the prompt, never from frontmatter reads.

## Relationship to existing machinery (additive, no duplication)

- **Existing `synthesis_agent` prose contradiction handling** — this *extends* it (makes the existing obligation inspectable), it does not create a parallel artifact. The Step 3 prose procedure and the Contradictions table stay; the inventory block sits alongside them.
- **`devils_advocate_agent`** — DA stress-tests a *single argument* adversarially; it does not enumerate pairwise paper conflicts. Different scope, untouched (#262 non-goal).
- **Claim-manifest / claim-alignment audit (#103/#213)** — that chain asks "is this manuscript claim supported by its citation?" (deterministic, claim-keyed). #262 asks "did the synthesis acknowledge a known tension between Paper A and Paper B?" Different obligation; it does **not** reimplement the claim audit. `resolution_pointer` points at a report location, **not** a claim id — claim ids are not the primary key. (A future `related_manifest_claim_id` could be added as an *optional* link if a resolution becomes a tracked manuscript claim, but that is out of scope here.)
- **#261 / #214** — closest precedent; both prose-layer. #262 follows the same scope call.

## Calibration (non-blocking manual reference, not a CI gate)

A calibration reference may be recorded to sanity-check contradiction-judgment quality: a small set of paper pairs (e.g. contradictory / conditional / compatible) judged by the agent, reported as a **confusion matrix + per-class recall**, with the **model id, date, and prompt recorded**. It is **not** wired into CI and is **not** a pass/fail acceptance gate — 20 LLM-judged pairs are too few and too nondeterministic across runs for a hard threshold. Recorded as a behavioral observation, not a guarantee.

## Out of scope

- No JSON Schema, no lint invariant, no CI gold fixture (see Scope decision).
- No auto-resolution — the scholar decides (#262 non-goal).
- No credibility ranking to "pick a winner" (would violate #244 epistemological neutrality).
- No change to `devils_advocate_agent` or the claim-audit chain.
- No `#111` dependency (that is a single boolean, not lineage clusters — the issue's own correction).
- No deterministic clustering script; scoping is prose guidance.

## Acceptance (corrected from #262 — see Scope decision for departures)

- [ ] `synthesis_agent.md` Step 3 / Output Format extended to emit a `cross_paper_tensions[]` markdown block **in addition to** the existing prose (no schema).
- [ ] Candidate-pair scoping subsection added as a **recall-limited heuristic** (inclusion-not-exclusion signals; explicit Coverage Note; not framed as an O(N²)/O(K²) algorithm; no #111 dependency).
- [ ] Field model uses orthogonal `pair_assessment` + `resolution_status`, evidence pointers, and `candidate_basis` (codex-corrected, not the issue's non-MECE draft).
- [ ] `examples/contradiction_pairs_example.md` shows contradiction / conditional_difference / insufficient_overlap rows + a Coverage Note with a cross-cluster recall caveat.
- [ ] Output Format gains a Contradiction Section listing the inventory for scholar confirmation.
- [ ] Cross-reference to the existing prose-level handling clarifying the change is **additive**.
- [ ] Calibration kept as **non-blocking manual reference**, not a CI gate (departure recorded in PR).
- [ ] Narrative-side discipline (advisory-only, no audit-simulation, no frontmatter read) confirmed inherited.

## Verification

- **Prose self-consistency**: the worked example round-trips through the new inventory block + scoping note + Output Format Contradiction Section without contradiction.
- **Additive check**: existing Anti-Pattern 3, Step 3 procedure, and Contradictions table are unchanged (grep-confirm not deleted).
- **Line-budget**: if a v3.6.7 pattern-protection line-budget test covers this agent, update the expected count for the added section.
- **Paper-derived discipline**: full citation to Kong et al. 2026 (L. Kong, Roadmap & User Guide, arXiv:2605.18661, §7.4.2); no internal / personal / institutional content in the change; leak scan clean.
