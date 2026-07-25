# #272 — Instruction-vs-Data Boundary for Retrieved Content (design)

**Status**: design approved 2026-06-07. Guidance layer ships this cycle; structural
(envelope) layer remains deferred. **This design leaves issue 272 open** (see §4.1 — closing
keywords, including inside negations, are deliberately avoided even in this doc).

**Issue**: #272 — Treat retrieved external content as data, not instructions (Opus 4.8
indirect prompt-injection robustness regression).

**Related**: #273 / #274 (Opus 4.8 behavioral-signal cluster); #134 / #330 (conductor /
write-scope guard — the eventual home of the *structural* version of this boundary).

---

## 1. Threat model

ARS agents routinely read content the suite does not control: web search results, fetched
PDFs, pasted third-party reviewer comments, and externally authored documents used as worked
examples. Any of that content can carry text that reads like an instruction — a directive to
mark a reference as verified, to exfiltrate local environment data, or to append attacker-
chosen text to the output. A model that cannot reliably separate *the user's instructions*
from *instructions embedded in retrieved data* may act on the embedded ones.

(This design document paraphrases the attack class to motivate the threat model. The
authoritative principle that lands in agent context, by contrast, names no specific attack
technique — see §4.4.)

This is not a vulnerability unique to ARS — it is a property of any agentic tool that reads
untrusted content, and the platform applies its own deployment-layer injection safeguards.
But two facts make it load-bearing here:

1. **ARS retrieves external content more heavily than a typical chat workflow.** Citation
   verification fetches sources; bibliography assembly issues web searches; reviewers ingest
   pasted manuscripts and comments. The attack surface is larger than in a workflow that only
   reads what the user typed.

2. **Opus 4.8's bare-model robustness on this axis moved the wrong way.** The Opus 4.8 System
   Card (§5.2, "Prompt injection risk within agentic systems") reports that on the Agent Red
   Teaming indirect-prompt-injection benchmark, the bare model scores between Opus 4.7 and
   Sonnet 4.6 — a regression relative to 4.7 at the bare-model level. Deployment-layer
   safeguards bring the *system* back in line with 4.7, but the model's own robustness to
   instructions hidden in retrieved content is lower than 4.7's. Treating "the model got
   better overall" as a reason to relax the instruction/data boundary would be exactly the
   wrong inference: the relevant metric moved the other way.

### Anchoring incident (de-identified)

During real maintainer use, a retrieval-style sub-agent was dispatched to gather externally
sourced documents. Content it fetched carried an injected instruction that attempted to
redirect the agent toward local configuration/secrets. The sub-agent was terminated before
it returned anything to the main thread; no exfiltration occurred.

The incident is recorded here only as evidence that this attack class is *real and already
observed* in ARS-style retrieval, not hypothetical. Two design conclusions follow:

- The attack surface concentrates in **retrieval-class agents** (the ones that fetch and
  ingest external content), which is where the guidance belongs first.
- The clean break in the chain was structural (the sub-agent never returned its tainted
  context to the caller), not a guarantee that the model recognized the injection. A written
  principle **documents the intended recognition behavior**; whether it changes runtime
  behavior is unverified and requires an eval harness (§6). It does not replace the
  structural break, and it does not claim to.

---

## 2. Scope — what this design ships

State the instruction/data boundary as an explicit **standing principle** of the suite:

- **Authoritative source**: add a section to `shared/ground_truth_isolation_pattern.md`,
  extending its existing Layer 1 ("raw inputs … untrusted by default") treatment. The section
  carries an explicit subsection header marking it as a **distinct retrieved-content
  instruction/data boundary, not an eval-leakage rule** (the two are related trust concerns
  but different mechanisms — see §3 placement note). Retrieved external content is **data**;
  any imperative-looking text inside it is **not** automatically promoted to a user
  instruction.
- **Hot-spot agents**: **inline the principle text itself** into the two agents with the
  largest retrieval surface — `source_verification_agent` and `bibliography_agent`. A bare
  "see `shared/…`" pointer is insufficient: the model does not traverse file paths named in
  its prompt, so a pointer-only treatment ships a document that satisfies human readers and
  the lint but is invisible to the model at the moment it fetches external content. The
  inlined block is a verbatim copy of the authoritative section's normative sentences, plus a
  backpoint citing the canonical anchor.
- **Drift guard**: a narrow lint (§5) that checks the authoritative section exists, that its
  required normative sentences are present verbatim, and that each hot-spot agent carries the
  same verbatim normative sentences plus a correctly-targeted backpoint.

**Known uncovered consumers (this cycle):** the threat model in §1 spans pasted reviewer
comments and externally authored templates, but this cycle inlines the principle only into
the two highest-surface *retrieval* agents. The pasted-comment workflow
(`perspective_reviewer_agent`) and the template/literature-intake workflow
(`literature_strategist_agent`) are **not** covered here — see §6 future scope. Readers must
not infer the broader surface is covered.

This is the guidance layer. The structural (envelope) layer is deferred — see §6.

---

## 3. Form — standing principle, not a gate

The principle is written as a **declarative design principle that guides the model's
judgment**, in the same register as the existing `ground_truth_isolation_pattern.md` §5
("Not a runtime permission system"). It is **not** a runtime/content-processing hard rule,
**not** a blocking gate, and **not** a runtime interceptor. (Commit-time documentation
consistency checks — §5 — may still fail CI; that is a separate layer, see the §5 note.)

Why not an iron rule / blocking gate:

- The judgment #272 asks for is **semantic** — "is this imperative the user's instruction or
  text smuggled in via retrieved data?" — and has no clean string signature. A machine-
  checkable block rule would have to pattern-match imperative text, and ARS's whole job is to
  process large volumes of *legitimate* imperative content: submission policies ("Authors
  must declare conflicts of interest"), reviewer comments ("the author should revise
  Section 3"), methods text ("decode the base64-encoded supplementary data"). A crude
  "imperative detected → flag/block" rule would mis-fire on exactly the content the tool
  exists to handle.
- A static lint runs at commit/CI time; prompt injection happens at **runtime**. A green CI
  cannot observe whether the model honored the principle while fetching a live page. Shipping
  a block-gate would create a false "injection is handled" signal while leaving the runtime
  behavior — the thing that actually matters — untouched.

The issue's own non-goals foreclose the gate framing ("Not proposing a new gate or blocking
behavior … phrased generally, not as a catalogue of specific defenses").

**Placement note.** The authoritative section lives in `ground_truth_isolation_pattern.md`
rather than a new file. Eval-answer-key leakage (that document's original subject) and
adversarial-instruction injection are *related but distinct* trust concerns: both are
properties of the document's existing Layer 1 ("raw inputs … untrusted by default, may be
hallucinated, adversarially crafted"), so injection is naturally a sub-case of Layer 1's
untrusted-input posture. Keeping them in one trust-boundary document avoids two competing
authority files that could drift against each other. The cost codex flagged — future
maintainers conflating answer-key isolation with injection handling — is mitigated by the
explicit subsection header (§2) that marks this as a distinct retrieved-content
instruction/data boundary, not an eval-leakage rule. If the two concerns later need
divergent ownership, splitting into `shared/untrusted_external_content.md` (cross-linked) is
the documented exit.

---

## 4. Boundaries — what this design explicitly does NOT do

1. **Leaves issue 272 open.** The guidance layer closes only the "principle was never
   stated" half; the structural boundary (envelope) is still unbuilt, so the issue must not
   close. GitHub auto-closes an issue when a PR title, PR description, commit message, or
   squash-merge message contains a *closing keyword* (`close`/`closes`/`closed`,
   `fix`/`fixes`/`fixed`, `resolve`/`resolves`/`resolved`) followed by the issue number, or
   when a PR is *manually linked* to the issue. Bare issue references do not auto-close — but
   the keyword parser is naive about negation: writing "does **not** close #272" still
   contains the substring `close #272` and can trigger the close (a previously-observed
   trap). Therefore the rule is:
   - No `close(s/d)` / `fix(es/ed)` / `resolve(s/d)` + `272` keyword syntax in PR title, PR
     description, commit messages, or squash-merge message — **including inside a negation**.
     If metadata must mention the issue, use "Leaves issue 272 open" (no closing keyword, no
     `#`-prefixed number adjacent to a keyword).
   - Do not manually link the PR or branch to issue 272.
   - After merge, **verify issue 272 is still OPEN**.
   - To keep the issue's timeline from looking abandoned (a real cost flagged in review),
     post a manual comment on issue 272 after merge linking to the PR. A comment never
     triggers auto-close and leaves a visible breadcrumb to the partial progress + the
     deferred structural work.

2. **Does not claim to mitigate prompt injection.** The only claims made are "the principle
   is now stated" and "the principle is guarded against silent removal." No claim is made
   that runtime injection success rate is reduced — a static lint cannot affect runtime
   behavior.

3. **Does not touch the envelope / does not add structural interception.** That is #134
   Slice 3+ work and is deferred by the #134 design spec. It is listed as future scope (§6)
   and not written here.

4. **The authoritative agent principle does not enumerate specific defenses or attack
   mechanisms.** The principle text that lands in `ground_truth_isolation_pattern.md` and the
   two agents is phrased generally — it names no specific trigger phrase or encoding — both
   because the issue forbids it and because such a catalogue is the source of the mis-fire
   risk in §3. (This *design document* paraphrases attack shapes in §1 to motivate the
   threat model; that is explanatory scaffolding for human readers and is scoped separately
   from the agent-facing principle. The §5 lint asserts the agent principle's normative
   sentences verbatim, and those sentences contain no attack catalogue.)

5. **Lint stays narrow — presence + verbatim-sync only.** No semantic detection, no scanning
   of agent output, no runtime blocking.

6. **No conductor / envelope / write-scope files changed.** §4.3's "does not touch the
   envelope" is otherwise advisory only. The implementation checklist (and the PR's own diff
   review) must confirm the change set is confined to the §7 touch list — specifically that
   no file under the conductor / task-envelope / write-scope-guard surface (#134 / #330) is
   modified. This is a documentation-scope PR.

---

## 5. Lint design

New `scripts/check_instruction_data_boundary.py`. Presence + sync alone (anchor exists,
backpoint string present) is **not enough** — a contributor could keep the anchor, gut the
body, and pass. So the lint asserts a minimal *canonical block*, still without any semantic
analysis:

- **(a) canonical section** — `shared/ground_truth_isolation_pattern.md` contains exactly one
  authoritative section under the stable heading/marker, and that section contains the
  required **normative sentence(s) verbatim** (a short fixed string constant in the lint).
  Missing heading, missing/weakened normative sentence, or a duplicate/fake second anchor →
  fail.
- **(b) verbatim sync in agents** — `source_verification_agent.md` and `bibliography_agent.md`
  each contain the **same required normative sentence(s) verbatim** (the inlined principle,
  per §2) plus a backpoint. "Sync" means: the exact canonical backpoint paragraph, outside
  any code fence, citing the exact authoritative anchor. A string that is present but points
  at the wrong target, or sits inside a code fence, does not count.

The mechanism mirrors the existing single-source-plus-by-reference pattern in
`scripts/check_firm_rules_sync.py` (the lint owns the canonical normative string; the doc and
agents must match it). A companion mutation test
(`scripts/test_check_instruction_data_boundary.py`) confirms the lint is not a trivial
accept-all. Required mutations that MUST each make the lint FAIL:

1. authoritative section deleted entirely;
2. heading kept, body gutted / normative sentence removed;
3. normative sentence weakened (any character delta from canonical);
4. duplicate or fake second anchor introduced;
5. backpoint removed from a hot-spot agent;
6. backpoint present but pointing at the wrong target;
7. inlined normative sentence missing from a hot-spot agent (pointer-only regression).

**Fail direction: fail-closed.** This lint detects documentation rot. A missing principle or
a broken backpoint should block merge. The cost of a false block is low (the author re-adds
the text); the cost of a miss is high (the principle silently disappears from the suite).
The choice is fail-closed, recorded here per the per-check fail-open/fail-closed discipline.

This is not in tension with §3's "not a gate." Two different layers: the lint is a
**commit-time** check on whether the *documentation* still carries the principle — it blocks
a merge that would delete the principle. §3's "not a gate" refers to **runtime** — nothing
here intercepts retrieved content or blocks the model from acting on it while a skill runs.
The lint guards the text; it never inspects or gates a live retrieval.

**CI wiring (both the lint and its test must run).** `spec-consistency.yml` runs *both*
`python scripts/check_instruction_data_boundary.py` (the checker) and
`python -m pytest scripts/test_check_instruction_data_boundary.py` (the mutation test) — if
only the checker runs, the checker itself can regress while still appearing present. The
workflow's path triggers must include `shared/**`, `deep-research/agents/**`,
`scripts/check_instruction_data_boundary.py`,
`scripts/test_check_instruction_data_boundary.py`, and the workflow file itself, so an edit
to any covered file or to the checker re-runs the gate.

---

## 6. Future scope (deferred — not built this cycle)

- **Structural instruction/data isolation at the envelope / task-dispatch layer** (#134
  Slice 3+). The #134 design spec is explicit that #272's structural home should be revisited
  only once a concrete envelope substrate exists, and that #134 must not close #272 or claim
  to mitigate it. This design honors that.
- **Runtime behavioral verification** — whether the model actually honors the principle under
  a live injection attempt. That needs an eval harness, not a lint, and is out of scope here.
- **Wider backpoint coverage** — extending the inlined principle to the remaining
  external-content consumers (`literature_strategist_agent`, `perspective_reviewer_agent`, and
  others). This cycle covers only the two highest-surface retrieval agents.

### Anti-false-closure pebble (ships this cycle, in CI)

Shipping a guidance layer creates a real risk: once the lint is green, "we already addressed
#272" becomes a standing excuse never to build the structural layer — and the guidance layer
provides **no** verified runtime defense. To keep the deferred structural work alive as more
than an open issue, the implementation adds a single **`xfail`-marked test** (e.g.
`scripts/test_runtime_injection_boundary_xfail.py`) that represents the unbuilt runtime
instruction/data defense. It is expected-to-fail, so CI stays green, but it is a persistent
"pebble in the shoe": a named, in-repo marker that the runtime defense does not exist yet.
The marker's docstring points at this design's §6 and at the structural-layer home
(#134 Slice 3+). It must NOT be deleted to make CI "cleaner"; it is removed only when the
structural layer actually lands and the test is promoted to a real passing assertion. This is
the codebase analogue of a reverse-invariant pin: the absence of the real defense is made
visible and un-ignorable, not left to issue-tracker memory.

---

## 7. Touch list (implementation phase)

| File | Action |
|---|---|
| `shared/ground_truth_isolation_pattern.md` | Add authoritative section w/ distinct-concern subsection header + canonical normative sentence(s) (Layer 1 extension) |
| `deep-research/agents/source_verification_agent.md` | Inline verbatim normative sentence(s) + correctly-targeted backpoint |
| `deep-research/agents/bibliography_agent.md` | Inline verbatim normative sentence(s) + correctly-targeted backpoint |
| `scripts/check_instruction_data_boundary.py` | New lint (canonical section + verbatim sync) |
| `scripts/test_check_instruction_data_boundary.py` | Mutation test (7 mutations, §5) |
| `scripts/test_runtime_injection_boundary_xfail.py` | Anti-false-closure pebble (xfail, §6) |
| `.github/workflows/spec-consistency.yml` | Run both checker + mutation test; add path triggers |
| `docs/design/2026-06-07-272-instruction-data-boundary-design.md` | This design doc |

**Scope guard:** no file outside this list is modified; in particular no conductor /
task-envelope / write-scope-guard (#134 / #330) file is touched (§4.6).

---

## 8. Acceptance (issue, as satisfied by the guidance layer)

- [x] The two highest-surface retrieval agents (`source_verification_agent`,
      `bibliography_agent`) state the instruction-vs-data boundary for retrieved content as an
      explicit principle, inlined into their working context (not pointer-only). Coverage is
      scoped to these two agents this cycle — see §2 "known uncovered consumers" and §6.
- [x] The principle is phrased generally (what to treat as data), not as a catalogue of
      specific defenses.
- [ ] Cross-linked from the architecture discussion in #134 — the structural form of this
      boundary belongs to the envelope layer (Slice 3+) and is deferred. This guidance layer
      does not satisfy that item; it is left open deliberately.

The third acceptance box stays unchecked: it describes the structural form, which this design
defers. #272 therefore remains OPEN after the guidance layer ships.
