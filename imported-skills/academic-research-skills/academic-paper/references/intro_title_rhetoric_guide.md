# Introduction & Title Rhetoric Guide

Used by `draft_writer_agent` (Step 1 pre-writing setup; Step 2 Introduction drafting; Step 3 title page assembly). Complements `references/paper_structure_patterns.md` (section architecture) and `references/abstract_writing_guide.md` (abstract composition). This guide covers the rhetorical work inside the Introduction and the title, not their placement.

---

## Part 1: Introduction Rhetoric (CARS Model)

The Introduction is a persuasion problem, not a summary problem. The reader must finish it convinced that (a) the territory matters, (b) something specific is missing or unresolved, and (c) this paper supplies it. Swales' Create A Research Space (CARS) model names these as three moves. Draft the Introduction move by move, in order.

### Move 1 — Establish the territory

Show that the topic is real, active, and consequential for this journal's readers.

**Steps** (use one or more):
- Claim centrality: why the field cares now (policy pressure, empirical anomaly, methodological turn)
- Make topic generalizations: what is broadly known or practiced
- Review prior work: the specific findings this paper builds on, synthesized rather than listed

**Discipline calibration**: empirical social science leans on centrality + prior findings; humanities may open with a text, case, or tension; engineering often opens with an application constraint.

**Anchor to materials**: every Move 1 claim about the field must trace to the Literature Search Report. Centrality claims without a citation are decoration and will be flagged at the integrity gate.

### Move 2 — Establish the niche

Show what is missing, unresolved, or contested. This is the pivot of the whole Introduction.

**Steps** (pick the one that matches the evidence):
- Indicate a gap: a population, setting, mechanism, or method prior work has not covered
- Counter-claim: prior findings conflict, and the conflict is unresolved
- Raise a question: known facts do not yet explain an observed pattern
- Continue a tradition: an established line of work licenses a next step

**The gap must be licensed by the review.** A gap statement is only as credible as the Move 1 synthesis that precedes it. If the annotated bibliography does not support "X has not been examined in Y," soften to what it does support ("evidence in Y remains limited to Z designs") or return to literature_strategist_agent for a targeted search. Never manufacture a gap.

**Avoid the universal-negative trap.** "No study has examined X" is an unverifiable claim and a common desk-reject irritant. Prefer scoped negatives tied to a documented search — "our search of [named databases], covering [period and design scope], identified no..." — or positive framings of the limit of current evidence.

### Move 3 — Occupy the niche

State what this paper does, in terms that mirror the niche just established.

**Steps** (in typical order):
- Announce purpose: one sentence, active, specific ("This study estimates..." not "This study aims to explore...")
- State RQs or hypotheses: verbatim the same RQs as the Paper Configuration Record, not paraphrases
- Preview contribution: what the reader will know afterward that they do not know now
- Outline structure: optional; many venues now cut it. Include only if the paper type template calls for it.

**Purpose-sentence discipline**: the purpose sentence is the most-quoted sentence in peer review. Draft it before drafting the rest of the Introduction, and check it answers the niche exactly. A Move 2 gap about "mechanism" answered by a Move 3 purpose about "prevalence" is a structural mismatch reviewers catch immediately.

### Proportions and length

- Introduction budget: typically 10-15% of body word count (respect the outline allocation from structure_architect_agent)
- Move 1 is the widest, Move 2 the shortest and sharpest, Move 3 concrete and unhedged about what was done (hedge findings, not actions)
- One move per paragraph is a safe default; Move 1 may take two

### Common failures

| Failure | Symptom | Fix |
|---------|---------|-----|
| Funnel too wide | Opens with "Since ancient times" scope | Start at the narrowest context that still shows stakes |
| Literature dump | Move 1 is a list of "A found X. B found Y." | Synthesize by theme or tension; cite in support of claims |
| Unlicensed gap | Move 2 asserts a gap the review never scoped | Rescope the gap or extend the search |
| Universal negative | "No study has ever..." | Scope it: database, period, design |
| Buried purpose | Move 3 purpose sentence hidden mid-paragraph | Lead the paragraph with it |
| Niche-purpose mismatch | Gap says mechanism, purpose says description | Rewrite the purpose to answer the stated gap |
| Findings leak | Full results narrated in the Introduction | Preview contribution type, keep numbers for Results (unless the discipline expects announced findings) |

---

## Part 2: Title Crafting

A title does three jobs: retrieval (search engines and databases), screening (a reader deciding whether to open the paper), and framing (setting the claim's ambition level). Draft 3-5 candidates at Step 3 assembly and select against the checklist below.

### Title anatomy

Most strong empirical titles carry: **key concept** (front-loaded) + **specifics** (population, setting, or mechanism) + optional **design signal** (e.g., "a longitudinal study," "evidence from X"). Word budget: aim for 15 words or fewer unless the venue's norms run longer.

### Title types

| Type | Shape | Norms and risks |
|------|-------|-----------------|
| Descriptive | "X and Y in Z context" | Safe default across disciplines; risk is blandness |
| Declarative | "X increases Y under Z" | Growing in high-impact science venues; the title becomes a claim, so it must carry the same hedging discipline as the abstract. Do not declare what the design cannot support |
| Interrogative | "Does X change Y?" | Accepted in social sciences and commentary; rare in engineering; some editors read it as hedging |
| Compound (colon) | "Catchy phrase: specific subtitle" | Common in humanities and social sciences; keep the pre-colon phrase informative, not merely cute |

### Checklist

- [ ] Front-loads the most important concept (first 3-4 words carry the topic)
- [ ] Contains the terms a searcher in this field would actually type (align with the abstract's keyword list; see `references/abstract_writing_guide.md`)
- [ ] 15 words or fewer, or a documented venue norm otherwise
- [ ] No abbreviations unless universally known in the field (DNA yes, HEI depends on venue)
- [ ] No throwaway openers: "A study of," "An investigation of," "Toward an understanding of"
- [ ] Claim level matches the design (no causal verbs on cross-sectional data)
- [ ] Specific enough to exclude papers it is not (a title that fits fifty papers screens none)
- [ ] Metaphor or wordplay, if any, is decoded by the subtitle

**Cross-check with the wording-pattern advisory**: several AI-typical RQ shells double as weak title shells, notably "A study of X and Y" (WP06), "A comparative study of X and Y" (WP17), and "Toward a framework for X" (WP18) from the Socratic mentor's reference table. If a candidate title matches one of those surface forms, treat it as a prompt to name the specific mechanism, site, or tension instead.

### Worked examples

| Weak | Stronger | Why |
|------|----------|-----|
| "A Study of AI and Higher Education" | "Generative AI in Programme-Level Quality Assurance: Evidence from 42 Taiwanese Universities" | Names the mechanism, population, and evidence base; survives the fifty-papers test |
| "Exploring the Impact of Feedback on Learning" | "Rubric-Anchored Peer Feedback and Revision Depth in First-Year Writing" | Replaces shell verbs with the actual instrument and outcome |
| "Toward a Framework for Teacher Wellbeing" | "Workload Rhythm, Not Workload Volume, Predicts Teacher Burnout: A Nine-Month Diary Study" | Declarative form carried by a design that can support it |

Examples are illustrative shapes, not field-verified claims; never reuse their content in a real paper.

---

## Provenance

Added for #500. The coverage gap (introduction rhetoric and title guidance) was surfaced by PR #485 (@lorenzo392), which proposed these topics inside a broader new-skill shape the suite declined. Content here was written fresh for this repo. Model source: the CARS model as introduced in Swales, J. M. (1990), *Genre Analysis: English in Academic and Research Settings*; a revised model appears in Swales, J. M. (2004), *Research Genres: Explorations and Applications*. This guide keeps the 1990 three-move structure and move labels but adapts the step inventory for this pipeline (e.g., Move 3 adds RQ/hypothesis restatement and contribution preview, and treats announcing full findings as a failure mode rather than a step).
