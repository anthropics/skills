---
name: creative-divergence
description: A structured pre-step that forces genuinely diverse solution paths before committing to any answer. Use this skill whenever the user asks for creative ideas, novel solutions, brainstorming, alternatives, "non-obvious" approaches, ways to solve a hard or stuck problem, or when they explicitly invoke "divergence" or this skill by name. Also use it when the user seems dissatisfied with conventional answers ("everyone says that", "something different", "think outside the box"), when a design/architecture/strategy decision has many viable options, or for diagnostic mysteries (an intermittent fault, a surprising observation, a bug nobody can reproduce) where the cause is unknown and competing hypotheses must be generated before testing. Do NOT use for simple factual questions or tasks whose single correct answer can simply be looked up — the line is not "one correct answer exists" but "the answer must be found vs. retrieved".
---

# Creative Divergence

A pre-step protocol that counteracts LLM completion bias and statistical inertia. Stochasticity in LLMs is spent on token choice, not conceptual strategy. This protocol relocates variation to the level of frames and mechanisms, applying strict selection pressure BEFORE solving. Never mix divergence and convergence in the same breath.

---

## Operational Execution Rules

1. **Adaptive Execution Depth:**
   - *Low Complexity / Reversible:* Compress to 3 assumptions + 6 approaches + 2 survivors (see Quick Mode).
   - *Standard / Complex:* Full execution across all 4 phases.
   - *High-Stakes / Irreversible Strategy:* Full execution, with a pause offered after Phase 2 so the user can prune or redirect before scoring. Phrase it as a natural checkpoint, never as a procedural stage; if the user doesn't engage, continue normally.

   *Assess complexity by: decision reversibility, number of stakeholders, magnitude of investment. If uncertain, default to full execution.*

2. **Backtracking:** The pipeline is forward-moving but not one-way. If new constraints, evidence, or assumptions surface mid-run that substantially change the search space, say so plainly ("New information surfaced: [X] — revisiting the framing...") and re-open Phases 1 and 2 for the new territory rather than forcing convergence on an obsolete framing. Discovering that the frame was wrong is a success of the process, not a deviation from it.

3. **Process Exposure & Honesty:**
   - **Default execution:** Render deliverables using content-descriptive headings ("Assumptions in the problem", "Approaches", "Selection", "Survivors"). Signal transitions through content ("With assumptions surfaced, here are candidate approaches...") rather than procedural labels. Never name this skill, its phases, or its modes in the user-facing response; no meta-narration about following a process ("Phase 1 complete" is leakage).
   - **Hide the procedure, but keep its rules:** without procedural headings restating constraints inline, re-check them yourself — one-line approaches stay ONE line, modal ideas still get labeled, scores stay on two separate axes, tags stay visible.
   - **Direct query exception:** If the user explicitly asks how the answer was generated or how the method works, explain the underlying protocol fully, accurately, and transparently — no evasion, no decorative analogies.

---

## Phase 1 — Attack the Frame

List every assumption embedded in the problem as stated. For each, ask: if this were false, would the solution space change entirely? Apply the **Empirical Reality Test**:

- **Hard invariants:** constrained by physical law, formal logic, or arithmetic. (Changing it breaks reality.)
- **Soft conventions:** constrained by human habits, traditions, regulations, budgets, or industry norms. (You can imagine a world where it differs without breaking physical law.)

*Rule:* Focus negations exclusively on soft conventions. Before labeling anything hard, ask who enforces it and what changing it would cost — regulations, budgets, and "technical impossibilities" are usually expensive, not impossible, and labeling them hard is the cheapest way to dodge the frame attack.

**Output:**
- 5–10 assumptions, one line each, classified hard/soft.
- Mark the 2–3 highest-leverage assumptions with **`[HIGH LEVERAGE]`**.
- Restate the problem 2–3 alternative ways, at least one under a negated `[HIGH LEVERAGE]` assumption.

Do not solve anything yet. The breakthrough may live in re-posing the question, not answering it as posed.

---

## Phase 2 — Generate Approaches, Not Answers

Produce single-line approaches focused on discovering distinct causal mechanisms rather than generating volume. Target 15–20 for complex problems; you may stop early only if mechanism families are genuinely exhausted, and stopping early requires explicitly stating the families already covered and why further approaches would duplicate them.

**Strict constraints:**

- **Single line limit.** Exactly one line per approach: name the mechanism, include the tag, save all elaboration for Phase 4. If you're writing a second sentence, you're converging too early. Stop.
- **Modal baseline (~5) — `[MODAL]`:** generate these first — the obvious answers any competent person would give, explicitly labeled. Modal is a category, not a position in the list; they exist only to be surpassed.
- **Distant-domain imports (≥5) — `[domain / dynamic]`:** first name the problem's core dynamic (resource scarcity, incentive misalignment, information asymmetry, coordination at scale, delayed feedback...), then select a field that has evolved specialized mechanisms for that exact dynamic — if none comes to mind, ask: *"what field has survived or optimized this dynamic under extreme pressure?"* — and tag inline — e.g. `[tax law / arbitrage]`. The tag is accountability for the import, not vocabulary decoration; an unnamed import can't be audited. Import the underlying mechanism, never the surface vocabulary. Never reuse a domain within the same conversation, and vary domains across problems — settling into pet domains (whether your own favorites or examples you've seen listed) re-creates the modal path one level up.
- **Negated assumptions (≥3) — `[FLIPPED]`:** approaches that exist only under flipped `[HIGH LEVERAGE]` assumptions from Phase 1.
- **Tail sampling (≥2) — `[EDGE]`:** approaches that feel uncomfortable or counter-intuitive. If nothing in the list makes you hesitate, the tail wasn't sampled.

---

## Phase 3 — Deduplicate and Select Separately

1. **Two-pass causal mechanism clustering** (same-mechanism duplicates are usually NOT paraphrases — "gamify participation" and "add leaderboards" read differently but are one mechanism):
   - **Pass 1 — shared mechanism:** group by root lever. Ask: *"stripped of surface details, is the core lever identical?"* If yes, combine into the strongest representative.
   - **Pass 2 — coexistence test:** for remaining candidates, ask: *"could these coexist as independent components in the same solution?"* If no (they compete for the same resource or execution slot), combine; if yes, keep both.
   Score the merged list, not the raw one.

2. **Independent two-axis scoring** (1–5 each; never combine or average — a single score lets conventional ideas win every time):
   - **Novelty:** 1 = standard industry playbook; 3 = unconventional in this sector; 5 = counter-intuitive or unheard of in the target domain.
   - **Feasibility:** 1 = requires major regulatory, technical, or capital breakthroughs; 3 = plausible with moderate effort; 5 = executable tomorrow with the existing team and tools. Anchor to the user's context; state explicit budget/timeline assumptions if unknown.

3. **Selection rule:** advance 2–3 candidates with **novelty ≥3 AND feasibility ≥3**. Kill low-novelty / high-feasibility candidates without mercy — the user can get those anywhere.

4. **Wild card:** keep one novelty-5 / feasibility-2 candidate as `[WILD CARD]` if present.

Be honest about the ceiling: this critic shares context with the generator, so it is self-review, not independent selection. Flag this when stakes are high, and suggest an external verifier (run the code, check the math, test with real users) whenever the domain allows one.

---

## Phase 4 — Converge

Develop survivors (and `[WILD CARD]` if present) in a structured comparison matrix:

| Candidate | Mechanism & Advantage | Novelty | Feasibility | Pre-Mortem | Kill Condition |
| :--- | :--- | :---: | :---: | :--- | :--- |
| [Name] | Plain-language mechanism & why it beats the `[MODAL]` baseline | X/5 | Y/5 | *"Failed in 6 months because..."* | Concrete, observable threshold |

- **Pre-mortem:** *"It's 6 months from now and this failed badly — what was the hidden blind spot?"*
- **Kill condition:** a quantitative, observable threshold derived directly from the pre-mortem ("if X stays below Y after Z, drop it"). A kill condition invented without the pre-mortem tends to be one designed to pass; a test you can't fail is theater.
- **Main risk (one line per survivor):** the most likely way execution goes wrong — distinct from the pre-mortem, which is an imagined failure used to derive the kill threshold.
- **Cheapest test (one line per survivor):** the fastest, cheapest external probe that could validate or kill the candidate before any real commitment.
- **`[WILD CARD]` handling:** replace the standard row question with *"what would have to be true for this to become feasible?"* — frame it as a research hypothesis, not an execution plan.
- **Candidate fusion:** if two surviving mechanisms could operate in parallel or in sequence for a combined effect greater than either alone, include their hybrid as one additional candidate row.

Conclude by outlining trade-offs and stating your personal preference, clearly labeled as such, leaving the final selection to the user — a single silent recommendation re-introduces the convergence bias this whole protocol exists to fight. Offer natural next steps in plain language (develop one further, prune by a constraint, push deeper in one domain, flip another assumption, fuse two survivors, or re-pose the problem).

---

## Anti-Patterns to Avoid

- **Premature convergence:** elaborating an idea during Phase 2. One line means one line.
- **Fake diversity:** same-mechanism ideas counted as different approaches. Apply the two-pass clustering strictly; paraphrase is the easy case, shared mechanism behind different words is the one that slips through.
- **Novelty theater:** exotic vocabulary that reduces to the modal baseline once developed. Imports must bring structural mechanisms.
- **Critic capture:** over-scoring feasibility on preferred ideas. Score as an adversarial auditor.
- **False hardness:** labeling regulations, budgets, or technical difficulties as hard invariants. They are expensive, not impossible — treat them as soft.

---

## Quick Mode (Compressed)

When time is limited or complexity is low:

- **Phase 1:** 3 assumptions (with `[HIGH LEVERAGE]`)
- **Phase 2:** 6 approaches — 3 `[MODAL]`, 2 `[domain / dynamic]` imports, 1 `[FLIPPED]` — the tagging minimum survives compression
- **Phases 3 & 4:** 2 survivors with pre-mortems and kill conditions

Don't name the mode (that's process leakage). If the query is clearly small, note in one clause that you kept the exploration focused and can expand any direction on request.
