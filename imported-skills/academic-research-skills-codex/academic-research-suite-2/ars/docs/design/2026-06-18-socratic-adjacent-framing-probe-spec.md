# Adjacent-Framing Probe — Socratic Mode Perspective-Expansion Mechanism

**Status:** Design (pre-implementation)
**Date:** 2026-06-18
**Author:** Cheng-I Wu
**Borrowing source:** Stanford OVAL STORM / Co-STORM — https://github.com/stanford-oval/storm
**Target file:** `deep-research/agents/socratic_mentor_agent.md` (single agent, prose-layer)

---

## 0. One-line

When an *exploratory* Socratic dialogue is stuck in Layer 1 (Problem Framing), the
Mentor may surface **one adjacent framing the user has not raised** — as a pure
question, never a proposed idea — to help a researcher who simply has not seen
enough of the field. Borrows STORM's *perspective-discovery intent* and Co-STORM's
*moderator unknown-unknowns injection*, but anchors framings in LLM internal
knowledge (zero retrieval dependency) and is hard-bounded by ARS's existing
"never generate ideas for the user" red line.

This is an **opt-in, additive, prose-layer** mechanism: gated by a new env flag,
no new agent, no new schema, no new mode. Same shape as the existing
`Optional Reading Probe Layer` (v3.5.1).

---

## 1. The gap this fills

ARS already has three mechanisms that touch "don't let the dialogue close too
early," but **none of them is this one**:

| Existing mechanism | What it does | Why it doesn't cover this gap |
|---|---|---|
| `[Q:CHALLENGE]` taxonomy | Gives the counter-position to the user's **stated** stance | Known disagreement, not an *unseen* facet |
| Divergence Reveal (SCR) | Introduces info that tests the user's commitment | Locked to the axis the user already declared |
| Persistent-Agreement injection (Dialogue Health) | Stops the AI from serial agreeing | Guards the **AI's** behavior, not the user's frame-lock |
| FINER `Novel` guiding Q ("where do you think the gaps are?") | Asks the user to find the gap | **The user cannot name a facet they don't know exists** |

The fourth row is the hole. ARS's Layer 1 framing discovery depends entirely on
the user's own mental map of the field. A researcher who has not encountered an
adjacent subfield, a neighbouring stakeholder, or a different level of analysis
**cannot surface it when asked "where's the gap?"** — they will answer only
within what they already know.

STORM solves the equivalent problem by fetching the **real table-of-contents of
related Wikipedia articles** and using that external structure to seed
perspectives, so the perspectives are anchored in how the topic is *actually*
structured in the world, not in what the LLM feels is relevant
(`persona_generator.py`: `FindRelatedTopic` → `get_wiki_page_title_and_toc()` →
`GenPersona`). Co-STORM goes further with a **moderator** agent that deliberately
injects information "related to the topic but not directly answering the current
question" to push the discourse out of local stagnation
(reranking unused sources by `cos(i,t)^α · (1−cos(i,q))^(1−α)`, α=0.5).

This mechanism borrows the **intent** of both (surface what the user did not think
to ask) but **not** the retrieval (see §6 for the deliberate divergence and §7
for the forward note).

---

## 2. Who this serves (the load-bearing scoping decision)

This mechanism **deliberately serves exploratory novice researchers**, and that
decision determines everything below — including why majority-favoured framings
are a feature here, not a bug.

**The reasoning (settled 2026-06-18):**

- A novice's frame-lock is usually *not seeing enough*, not stubbornness. Surfacing
  a mainstream adjacent facet they missed is **filling a visibility gap** — exactly
  what they lack. Here, an LLM's natural pull toward majority/well-trodden framings
  is a **feature**: it shows the novice the landmarks of the field.
- An experienced researcher has already swept the mainstream facets; surfacing them
  is noise, and worse, risks pushing them back into a frame they intentionally
  bypassed. **But experienced researchers are structurally not at this entry point.**
  With a draft → `plan`/`full`/`revision` mode. With a clear question →
  *goal-oriented* intent, where this mechanism is dormant. The
  **exploratory + Layer 1** gate is itself a coarse-but-effective novice filter:
  the people who land in exploratory mode, stalled at problem definition, skew
  toward "still exploring, hasn't seen enough."

**Consequence for design:** an earlier draft of this spec added a "deliberately
pick the most *non-mainstream* adjacent facet" bias to counter LLM majority-favour.
That is **removed**. In a novice-majority entry point, pushing a beginner to the
*edge* of the field before they have found their footing is counterproductive. The
mechanism keeps only a light **diversity** requirement (consecutive probes should
not be the same kind), not a contrarian bias.

**Majority-favour is recorded as a design tradeoff, not a limitation** (§6).

---

## 3. Trigger conditions

Borrows Co-STORM's "intervene only when the discourse is circling" principle, but
reuses ARS's existing dialogue state rather than adding new tracking.

All of the following must hold:

1. **Env flag on** — `ARS_SOCRATIC_ADJACENT_PROBE=1` (exactly the string `1`;
   unset/empty/`0`/other keeps the layer dormant). Default dormant, same gate
   discipline as `ARS_SOCRATIC_READING_PROBE`.
2. **Exploratory intent** — per the existing Intent Detection Layer. (Note: this is
   the **opposite** gate to the Reading Probe, which fires only goal-oriented.
   The two mechanisms have opposite purposes: Reading Probe checks whether a cited
   paper was read; Adjacent-Framing Probe expands what the user is looking at.)
3. **Layer 1 (PROBLEM FRAMING) only** — frame-lock is worth opening only at problem
   definition. Injecting adjacent facets during Methodology/Evidence layers would
   disrupt legitimate convergence.

**Not a hard "fire once a lock is detected" trigger.** In exploratory + Layer 1,
the adjacent-framing probe is an **available tool from the moment the layer opens**,
parallel to how exploratory mode already raises the `[Q:CHALLENGE]` ratio to 40%+.
It is a standing tendency, not an emergency patch.

### Intensity knob (not an on/off switch)

The existing **S4 (Scope Stability)** convergence signal is **repurposed as an
intensity knob**, not a trigger gate:

- In the standard convergence model, S4 active = good (scope is settling).
- **In Layer 1 exploratory mode, S4 going active *early* is the warning sign** —
  it means the framing locked fast, possibly before the user saw enough.
- The faster scope stabilises (S4 active sooner / more rounds stable), the **higher**
  the adjacent-probe tendency, via the existing Adaptive Intensity mechanism.
- A dialogue that is *not* stabilising is already diverging on its own and needs no
  push — low/zero probe tendency.

**Why reuse S4, not add a counter:** prompt-only skills accrete semantic seams at
new state-tracking points (cf. `feedback_prompt_skill_self_review_blindspots`,
`feedback_linter_mutation_test_discipline`). S4 is already computed every 5 turns;
reusing it avoids a new "frame-lock counter" that could collide with the existing
convergence logic.

### Soft cap

- The Mentor **proactively** surfaces an adjacent framing **at most 2 times** per
  session (vs the Reading Probe's once — two allows covering two distinct facets).
- This is a **soft** cap on *AI-initiated* surfacing. If the user then asks to
  explore a facet themselves, that is user-driven and does not count against the cap.
- **Minimum spacing:** the two AI-initiated probes must be at least 3 dialogue
  rounds apart. Back-to-back surfacing turns "expansion" into a burst of
  direction-pushing — the red line this cap exists to guard. The user must have
  room to engage (or decline) the first facet before a second is offered.
- The cap guards "this is not the AI endlessly pushing directions" (red-line risk)
  without forcing the AI silent when the user genuinely wants to keep exploring.

---

## 4. Probe form (the make-or-break surface)

The **only** legal shape: surface an adjacent **facet name** + ask whether to
include or consciously exclude it. Ends in a question mark; contains **no** formed
RQ / hypothesis / conclusion.

```markdown
[ADJACENT-FRAMING-PROBE]
Your question is framed around <quote the user's own framing, verbatim>.
There's an adjacent facet you haven't raised: <facet name, a category phrase>.
Would you want to bring it into scope, or are you consciously setting it aside?
```

Hard constraints:

- `<facet name>` is a **category word** — a perspective / dimension / stakeholder /
  time-scale / level of analysis (e.g. "the institutional-incentive angle", "the
  longitudinal dimension", "the perspective of those being evaluated"). It is
  **never** a sentence, an RQ, or a finding.
- The closing question is fixed as **"include OR consciously exclude"** — this hands
  the decision fully back to the user; the AI does not hint which is right.
- **One facet at a time.** No menu. Listing 3 facets to pick from is a select/rank
  variant and violates the red line (§5).

---

## 5. Red-line compliance — the verb test

Aligned with the Kong L2 verb test cited by `plan_mode_protocol.md` Step 2.5
(`docs/design/2026-06-08-kong-255-l2-advisory-not-generation.md`): the Mentor must
never **propose / substitute / rank / expand / select** an idea for the user.

| | Example | Verdict |
|---|---|---|
| **GOOD** | "You're framed around 'the effect of AI tools on student grades.' An adjacent facet you haven't raised: the teacher's-eye-view angle. Include it, or set it aside?" | surface facet + ask. ✅ |
| **BAD (propose)** | "You could reframe this as 'how teachers mediate AI's effect on grades.'" | gives a formed RQ. ❌ |
| **BAD (rank)** | "The teacher-mediation angle is more novel than your current frame." | comparison / implies better. ❌ |
| **BAD (menu/select)** | "Consider: teacher mediation, parental involvement, or policy level — which?" | lists candidates to pick. ❌ |
| **BAD (expand)** | "Teacher mediation could become three sub-questions: …" | expands it for the user. ❌ |

Only the first row passes. The moment a probe contains "you could research X",
"X is better/more novel", or "consider A, B, or C", it is a violation.

---

## 6. Anchoring source: LLM internal knowledge (the deliberate tradeoff)

The facets are **LLM-generated**, not fetched from an external TOC. STORM anchors
perspectives in real Wikipedia structure precisely so they are independent of the
LLM's training distribution. This version forgoes that. The consequences are
recorded honestly:

### 6a. What this buys and costs

- **Buys:** zero retrieval dependency, no fetch-failure fallback, fastest to ship,
  same operational shape as the Reading Probe.
- **Costs:** the "adjacency" judgment carries the LLM's training-distribution skew —
  it will tend toward **majority / well-trodden** framings.

### 6b. Why majority-favour is acceptable *here* (per §2)

For the **target user** (exploratory novice), surfacing mainstream adjacent facets
is the value, not the defect. This is logged as a **design tradeoff**, not a bug:
the mechanism intentionally serves researchers who have not seen enough; mainstream
facet visibility helps them. Experienced / task-oriented researchers are filtered
out upstream by intent detection and mode choice and are not this mechanism's
service population.

### 6c. Compensation that does NOT rely on retrieval

The probe still constrains itself in three ways, none of which require an external
anchor:

1. **De-load, don't opine.** Because the anchor is weak, the probe's *assertion
   strength* drops to match. The AI asserts only two **verifiable** things —
   (i) the user has not mentioned this facet (checkable against the transcript),
   (ii) the facet is adjacent to the topic. It asserts **nothing** about the facet's
   value: never "more novel", "better", "you should." (cf.
   `feedback_positive_finding_anti_sycophancy_evidence_question`: claims must be
   anchored to identifiable basis; here the only basis is conversational absence,
   which is anchorable.)
2. **One push, then retreat (no-defense).** If the user says "I've considered that,
   it's not relevant" or "I want to stay in this frame," the Mentor **accepts
   immediately, does not argue, and does not re-surface the same facet** — logs
   `outcome=declined` and moves on. This aligns with
   `feedback_respect_contributor_expertise`: the user is the domain expert; the
   LLM's internal knowledge does not override their "not relevant." It also serves
   as the safety net for the **experienced exploratory researcher the
   exploratory+Layer-1 filter fails to exclude** (§2 residual risk): one "I've seen
   the mainstream take" and the mechanism goes silent.
3. **Diversity-only requirement.** Consecutive probes must surface **different kinds**
   of facet (don't surface two stakeholder facets in a row). This is the light
   diversity floor — **not** a contrarian "pick the most edge facet" bias, which §2
   explicitly removed.

### 6d. Audit signal (post-hoc bias visibility)

Emit a machine-readable tag so Stage 6 AI Self-Reflection can audit how often the
AI surfaced facets and how often the user accepted/declined. **A high decline rate
is itself the bias-detection signal**: if the AI's adjacency judgments are
consistently rejected, the LLM's internal-knowledge adjacency is mis-calibrated for
this user — the audit sees it even though generation-time cannot stop it.

```
[ADJACENT-PROBE: surfaced="<facet name>", anchor=internal_knowledge, turn=<N>, outcome=<considered|declined|deferred>]
```

---

## 7. Forward note: pluggable external anchor (not implemented)

Majority-favour is fundamentally constrainable **only by an external source** — a
real TOC reflects how a topic is actually structured, independently of the LLM's
training distribution. This spec deliberately does **not** build that (per the
zero-dependency decision). It is recorded as a forward extension:

- A future version may make the **anchoring source pluggable**, with internal
  knowledge as provider #1 and a **STORM-style external-TOC retrieval** (WebSearch
  over related-topic section structures) as provider #2.
- The motivating use case for the external anchor is **not** "fix a bug" — for the
  novice target population internal knowledge is fine. It is "**serve the rare
  experienced exploratory researcher**" for whom external, non-mainstream facets
  add value the internal anchor cannot.

---

## 8. Lint / regression discipline (deferred specifics to plan stage)

Prose-layer mechanisms degrade silently; a linter is required (cf.
`feedback_linter_mutation_test_discipline`, `feedback_prompt_skill_self_review_blindspots`).

At minimum the linter must:

- Assert the `[ADJACENT-FRAMING-PROBE]` section exists and is env-gated.
- Reject candidate-RQ / propose / rank / select phrasing inside the probe block
  (the §5 BAD patterns) — guarding against the form drifting into idea-generation.

Mutation-test design (which mutations must FAIL the linter, case-alignment with
IGNORECASE) belongs in the implementation plan, including the two discipline traps
recorded in `feedback_linter_mutation_test_discipline` (commit before mutating;
align mutation-command casing to the linter).

---

## 9. Explicit non-goals / boundaries

- **Does NOT touch** `academic-paper/agents/socratic_mentor_agent.md` (a separate
  file with no Layer structure — `plan_mode_protocol.md:69` flags the distinction).
  plan mode inherits this change automatically because its Socratic questioning is
  delegated to `deep-research`'s `socratic_mentor_agent`.
- **No new agent, no new mode, no new schema** — prose-layer only, env-gated, same
  shape as the Reading Probe.
- **Does NOT generate ideas** — surface-and-ask only, hard-bounded by the §5 verb
  test. If the user cannot or will not engage a surfaced facet, the open state is
  recorded; the Mentor never fills it.
- **Does NOT serve experienced / task-oriented researchers** by design; they bypass
  via intent detection and mode choice.
- **Does NOT constrain majority-favour at generation time** — accepted as a tradeoff
  for the novice target (§6b), visible post-hoc via the §6d audit tag, fully
  addressable only by the §7 external anchor (not in this scope).
