---
rubric_version: "1.0"
paper_citation: "Wang, S., & Zhang, H. (2026). Pedagogical partnerships with generative AI in higher education: how dual cognitive pathways paradoxically enable transformative learning. International Journal of Educational Technology in Higher Education, 23:11. DOI: 10.1186/s41239-026-00585-x"
license: CC-BY-NC 4.0
---

# Collaboration Depth Rubric

**Status**: v1.0 (introduced ARS v3.5, 2026-04-21)
**Source**: Wang, S., & Zhang, H. (2026). *IJETHE* 23:11. DOI [10.1186/s41239-026-00585-x](https://doi.org/10.1186/s41239-026-00585-x). Open Access, CC BY 4.0.
**Canonical location**: `shared/collaboration_depth_rubric.md` in `Imbad0202/academic-research-skills`. External consumers should reference by stable URL; do not vendor (bump the `rubric_version` field on any modification).

---

## Why this rubric exists

Wang & Zhang (2026) empirically show that student-GenAI collaboration on pedagogical partnership terms simultaneously activates two cognitive pathways — **vigilance** (critical evaluation of AI output) and **offloading** (strategic delegation of cognitive work) — and that **both** independently predict transformative learning. Counterintuitively, cognitive offloading is **positively** associated with deep learning (β = 0.333, p < 0.001), with U-shaped dynamics: shallow scattered use (Zone 2) produces worse outcomes than no AI use (Zone 1); substantial committed delegation (Zone 3) unlocks higher-order reflection (β-quadratic = 0.102, p < 0.001).

This rubric operationalizes their framework as a post-hoc observer signal for Claude Code agents. It is used by `academic-pipeline/agents/collaboration_depth_agent.md` to score dialogue logs and produce **advisory, non-blocking** feedback to the user on how their collaboration pattern is shaping learning depth.

The rubric is **descriptive, not prescriptive**. It does not gate user progression. It does not celebrate high scores. It does not suggest low scores are failures. Its purpose is to make collaboration mode visible, so the user can decide whether to change it.

---

## The four dimensions

### Delegation Intensity

**Paper construct**: Cognitive Offloading (CO). 6-item Likert scale; sample items: *"I delegate complex problem-solving tasks to generative AI"*, *"I transfer cognitive effort to generative AI to reduce mental workload"* (Wang & Zhang 2026, Table 1).

**What to score for**: whole-category handoffs versus scattered micro-asks. Count committed delegation of task *categories* (e.g., "AI, draft the entire literature review" or "AI, do the outline"), not individual prompts. Zone 2's "fixing sentences, checking facts, tidying paragraphs" pattern is **low** intensity even if prompt count is high.

**High-intensity signals**:
- User assigns a whole subtask to the agent and moves on (e.g., "draft literature review", "build argument skeleton", "generate first outline")
- User articulates a division-of-labor plan at intake
- User says "you handle X while I focus on Y"

**Low-intensity signals**:
- Many small single-prompt interactions, each touching a fragment
- No task-level commitment language; user holds full cognitive load and just nudges output
- User edits AI micro-outputs line-by-line rather than regenerating at task level

**Empirical anchor**: U-shape (β-quadratic = 0.102, p < 0.001). Low-to-moderate offloading has minimal learning impact; only above threshold does offloading accelerate transformative learning.

---

### Cognitive Vigilance

**Paper construct**: Cognitive Vigilance (CV). 6-item Likert scale; sample items: *"I critically evaluate the accuracy of AI-generated content"*, *"I verify AI-generated information through independent sources"*, *"I scrutinize AI outputs for potential errors"* (Wang & Zhang 2026, Table 1).

**What to score for**: whether the user actively challenges, verifies, and pushes back on AI output — or accepts it uncritically.

**High-vigilance signals**:
- User asks AI to justify a claim, cite a source, or defend a framing
- User catches an AI error and says so explicitly
- User refuses to accept a draft and asks for a different approach
- User requests source verification or cross-checks with another tool
- User counter-argues before accepting

**Low-vigilance signals**:
- User accepts all drafts without critique
- User never asks "where does this claim come from?"
- User forwards AI output unchanged
- No explicit challenges to AI reasoning in the dialogue

**Empirical anchor**: H2a β = 0.437, p < 0.001, f² = 0.243 — **the single highest-impact path** in Wang & Zhang's model. Also the dimension with highest IPMA importance (0.438) *and* lowest IPMA performance (56.7/100), identifying it as the top priority for pedagogical intervention. If a user scores low here, that is the signal the paper most strongly implicates as correctable.

---

### Cognitive Reallocation

**Paper construct**: Human-GenAI Pedagogical Partnership (HGP) → Transformative Learning Experience (TLE), mediated by cognitive offloading (H3b indirect path β = 0.117, p < 0.001). Paper's characterisation: "strategic offloading liberates mental resources for higher-order reflection"; Risko & Gilbert (2016) cognitive offloading framework extended to show delegation is only learning-productive when freed capacity is *reinvested* in higher-order work.

**What to score for**: when the user hands work to the agent, what does the user do with the freed capacity? Is it invested in reframing research questions, questioning assumptions, constructing original arguments, making judgment calls — or is it idle?

**High-reallocation signals**:
- After AI completes a subtask, user revisits higher-level framing (e.g., "looking at your draft, I now think the RQ should be X not Y")
- User produces original synthesis not present in AI output
- User introduces counter-arguments, frameworks, or perspectives the AI did not raise
- User makes judgment calls that require context only the human has (stakeholder intent, institutional history, personal aesthetic)

**Low-reallocation signals**:
- User accepts AI work and moves to next prompt without higher-order engagement
- No original synthesis; user's contribution is routing and aggregation only
- Time saved by offloading does not translate to any visible higher-order contribution

**Empirical anchor**: Paper's post-hoc quadratic: the offloading→TLE path only materialises above a threshold (β-quadratic = 0.102, p < 0.001). Delegation without reallocation is Zone 2; delegation *with* reallocation is Zone 3.

---

### Zone Classification

**Paper construct**: three-zone framework (Wang & Zhang 2026's primary conceptual contribution, synthesised from the dual-pathway SEM + fsQCA configurations + post-hoc U-shape analysis). Popularised in Hardman (2026-04-16) and Means (2026-04-20).

**Synthesis rule** (derived from the three dimensions above):

| Zone | Delegation Intensity | Cognitive Vigilance | Cognitive Reallocation | Description |
|---|---|---|---|---|
| **Zone 1 — No AI use** | Near 0 | N/A | N/A | User carries full cognitive load manually. Learning occurs but capacity-constrained. |
| **Zone 2 — Shallow / Scattered** | Low–Mid | Low | Low–Mid | "Half-measures worse than no AI at all." Coordination overhead without meaningful cognitive savings. Empirically the worst outcome zone. |
| **Zone 3 — Deep Partnership** | High | High | High | Committed strategic delegation **with** critical evaluation **and** reinvested higher-order reflection. The zone in which transformative learning empirically occurs. |

**Scoring rule**: Zone 3 requires **all three** sub-dimensions to be high. Zone 2 is the default when at least one of Delegation Intensity or Cognitive Vigilance is low while AI is being used. Zone 1 is the default when AI is essentially unused in the dialogue window.

**Honest calibration** (anti-sycophancy): Zone 3 is empirically **rare**. Wang & Zhang's IPMA performance scores for CV (56.7) and HGP (54.2) — the two Zone 3 prerequisites — sit in the 55–60 range out of 100. A consumer agent should not default to Zone 3; if an aggregate score trends toward Zone 3, re-audit the dialogue for counter-evidence before finalizing.

---

## Scoring

Each of the first three dimensions is scored **0–10** (integer). Zone Classification is a label derived from the three dimension scores.

**Threshold guidance** (consumer agents may adapt these bands):

| Score band | Label |
|---|---|
| 0–3 | Low |
| 4–6 | Mid |
| 7–10 | High |

**Zone synthesis**:
- All three dimension scores ≥ 7 → Zone 3
- Delegation Intensity or Cognitive Vigilance < 4, AI actively used in dialogue → Zone 2
- Delegation Intensity < 2 AND Cognitive Reallocation N/A (AI essentially unused) → Zone 1
- All other combinations → Zone 2 with narrative qualifier

---

## Anti-sycophancy discipline for consumer agents

Any agent consuming this rubric **must** enforce:

1. **Evidence requirement**: no dimension score ≥ 7 ("High") without at least one specific dialogue-turn citation from the scored session.
2. **Forced counter-enumeration**: before finalizing scores, the agent lists ≥ 2 moments where the user could have gone deeper (even in high-scoring sessions).
3. **Re-audit trigger**: if the aggregate Zone label comes out Zone 3, re-audit the dialogue for counter-evidence. Zone 3 is empirically rare; a fast Zone 3 call is usually wrong.
4. **Descriptive language only**: no "great job!", no "needs improvement!". Report observed pattern + specific citable evidence.
5. **Cross-model divergence flag**: if the consumer agent runs cross-model (e.g., via `ARS_CROSS_MODEL`), any dimension score disagreement > 2 points between models must be flagged in the output.

## Explicitly out of scope

This rubric does **not**:

- Gate user progression. Consumer agents must declare `blocking: false` in their frontmatter.
- Replace AI self-reflection protocols (e.g., `academic-pipeline` Stage 6's six-dimension Collaboration Quality Evaluation, which is AI-about-itself; this rubric is AI-about-user-collaboration).
- Detect user "orientation" (efficiency vs depth). Wang & Zhang (2026)'s H4 on efficiency orientation as amplifier is not operationalised here.
- Prescribe which tasks to delegate. That is a pedagogical decision the user owns; this rubric only describes what delegation pattern occurred.

---

## Versioning

`rubric_version` follows semver. Changes to dimension count, synthesis rule, or operationalisation language require a **minor** bump and a note in `CHANGELOG.md`. Example-refinement or phrasing changes are **patch** bumps.

If a future paper supersedes or materially revises Wang & Zhang (2026)'s constructs, a **major** bump is required and the `paper_citation` field must be updated accordingly.
