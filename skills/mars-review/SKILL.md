---
name: mars-review
description: >
  Run a multi-perspective peer review of a research paper using a structured panel protocol
  (independent persona reviewers → grounded specialist checks → deliberation → meta-review),
  distilled from the MARS multi-agent review system. The success criterion is HOLISM: every
  section, every claim, and every review dimension gets covered, and claims are traced to
  evidence across sections. Use this whenever the user asks to review a paper or draft, act
  as a peer reviewer or reviewer panel, do a pre-submission check, predict "what reviewers
  would say", assess a paper against a venue or CFP, or critique a manuscript — even if they
  just say "look over my paper" or attach a PDF/LaTeX project and ask what's weak.
---

# Holistic Paper Review (MARS-style panel protocol)

Simulate a review panel the way MARS does — independent persona reviewers, grounded
specialist agents, and a meta-reviewer — but organized so nothing escapes review. The
protocol exists because single-pass LLM reviews anchor on whatever they notice first and
skim the rest. Independence-then-deliberation, plus explicit coverage accounting, is what
buys holism.

Non-negotiable principle: **the unit of review is the whole paper.** Sections get attention
individually, but every judgment (novelty, soundness, decision) is made with the full paper
in view. A methods section cannot be judged sound without seeing the results it produces.

## Phase 0 — Intake and desk check (gate)

Read the entire paper before writing anything. Accept PDF, LaTeX project, Markdown, or
plain text; for LaTeX, read every `.tex` and `.bib` file.

If the user names a target venue or gives a CFP URL, fetch the CFP and extract its topics.
Then make a desk decision: is the paper plausibly in scope? Report it as
`{decision: in-scope | out-of-scope, reasoning}`. If out-of-scope, say so, explain, ask
whether to continue anyway — and stop unless told otherwise. (A desk check that gates
nothing is theater.) If no venue is given, skip the scope question but still record the
paper's apparent audience and contribution type.

## Phase 1 — Holistic map (the backbone)

Before any opinions, build two artifacts. Everything downstream refers back to them.

**Section inventory:** every section, with a one-line summary and its role
(motivation / method / evidence / discussion / boilerplate).

**Claims–evidence table:** every substantive claim the paper makes (contributions,
performance numbers, comparisons, generality statements), formatted as:

| # | Claim | Stated in | Evidence in | Status |
|---|-------|-----------|-------------|--------|
| 1 | "2.3× speedup over baseline X" | Abstract, §1 | §5.2, Table 3 | supported / partial / unsupported / contradicted |

This table is the holism instrument: abstract promises that no section cashes out, results
that no claim references, and cross-section contradictions all become visible here. Flag
every claim whose status is not "supported."

**Internal-consistency audit.** While building the table, actively hunt for the paper
contradicting *itself* — this catches problems no external search can: the same quantity
reported with different values in two places (an n, a percentage, a table cell vs. prose),
the abstract claiming more than the body demonstrates ("at any volume" when only one
volume was tested), scope or mechanism claims that a later section explicitly walks back,
and conditions defined in the setup that never appear in the results. Record each mismatch
in the table with both locations and status `contradicted`. These are the findings human
reviewers use to reject papers, so err toward checking every number that appears twice.

## Phase 2 — Independent panel (three reviewers)

Three reviewers with **fixed, function-matched personas** — not random attributes. Each
persona exists to catch a different class of problem:

- **R1 — Domain expert** (deep knowledge of the paper's subfield; critical tone).
  Focus: technical soundness, novelty relative to the state of the art, whether the
  approach is well-motivated.
- **R2 — Methodologist** (statistics/experimental-design skeptic; neutral tone).
  Focus: evaluation validity, baselines, ablations, statistical rigor, reproducibility,
  threats to validity.
- **R3 — Informed outsider** (adjacent-field reader; supportive tone).
  Focus: clarity, positioning, significance beyond the subfield, whether the paper is
  understandable and its impact case convincing.

Write the three reviews **independently**: draft each as if the others do not exist, and do
not reuse phrasing or observations across them — if the same weakness occurs to you for two
reviewers, that is fine (convergence is signal), but each must arrive at it through its own
persona's lens and cite its own evidence. Each reviewer reads the whole paper and the
Phase 1 map.

Each review uses exactly this structure:

```json
{
  "decision": "Accept | WeakAccept | WeakReject | Reject",
  "scores": {"quality": 1-10, "novelty": 1-10, "soundness": 1-10, "clarity": 1-10},
  "summary": "2-3 sentences on what the paper does and claims",
  "strengths": ["..."],
  "weaknesses": ["... — each must cite specific sections/tables/lines"],
  "questions_for_authors": ["..."]
}
```

Weaknesses without a location reference are not allowed; vague criticism is how reviews
lose holism.

## Phase 3 — Grounded specialist passes

These run alongside the panel and feed the deliberation. Ground them in real retrieval —
ungrounded novelty opinions are worthless.

**Novelty scout.** Formulate 2–3 search queries from the paper's actual contribution
statements (not term frequency — write the queries the way a knowledgeable reviewer would).
Retrieve related work with the bundled script (arXiv + Semantic Scholar, no API keys,
returns JSON with citation counts):

```bash
python scripts/paper_search.py "your query" --max 5
```

If the script hits a network restriction (403/timeout), fall back to WebSearch — the goal
is grounding, not a particular tool. Compare the paper against the closest 3–5 works found:
for each, one line on what it does and how this paper differs. Verdict: `novel |
incremental | overlapping`, with the retrieved titles cited. If no retrieval works at all,
say so explicitly and mark the novelty verdict as ungrounded — never fake grounding.

**Citation fact-check.** Identify the *load-bearing* cited claims — the ones the argument
depends on (typically 3–8, not every citation). For LaTeX input, resolve `\cite` keys to
titles/authors with the bundled parser (brace-counting, so titles containing commas
survive); then confirm each cited work exists via Crossref:

```bash
python scripts/bib_resolve.py parse refs.bib key1 key2   # keys → {title, author, year}
python scripts/bib_resolve.py verify "Resolved Title" --author "Surname"
```

For non-LaTeX input, work from the reference list; if the network blocks Crossref, fall
back to WebSearch. Spot-check each claim: does the cited work plausibly say what the paper
says it says? Report per claim: `verified | plausible | questionable | misattributed`.
Claims that carry weight but have *no* citation belong in the claims–evidence table as
unsupported — do not skip them just because there is nothing to look up.

**Clarity and writing pass.** Note grammar, structure, and presentation issues as
**revision notes only**. Writing quality never contributes to the accept/reject decision —
prose problems mean revisions, not rejection. (This corrects a MARS miscalibration where a
grammar agent voted on acceptance.)

## Phase 4 — Question–answer probe

This is the sharpest holism instrument, adapted from MARS's questioner/RAG-answer loop:

1. Generate 6–10 open-ended, non-leading questions a careful reviewer would ask, spread
   across dimensions (motivation, method, evidence, limitations, generality).
2. Attempt to answer **every question strictly from the paper's own text**, quoting or
   citing the section that answers it.
3. Any question the paper cannot answer is a finding: attach it to the relevant reviewer's
   weaknesses or questions_for_authors.

A paper that answers all fair questions from its own pages is complete; the residue is
exactly what the authors need to fix.

## Phase 5 — Board room deliberation

Now, and only now, the reviews meet.

1. Present all three reviews plus the specialist findings and the Q&A residue.
2. Give each reviewer one revision opportunity: in light of the others' points and the
   grounded evidence, does R1/R2/R3 change any score or the decision? Record changes with
   reasons ("R2 lowered soundness 6→4 after the novelty scout surfaced [paper X]").
   No change is a valid outcome.
3. Meta-reviewer writes **minutes**: points of agreement, points of disagreement and how
   they resolve, and the key takeaways — in prose, as if recording a real PC discussion.
4. Compute the panel decision **explicitly** (never "majority vote" by vibes):
   map Accept=3, WeakAccept=2, WeakReject=1, Reject=0; average the three post-deliberation
   decisions; ≥2.5 → Accept, ≥1.5 → WeakAccept, ≥0.75 → WeakReject, else Reject. Report
   the arithmetic. Specialist passes inform reviewers but do not get votes: the desk check
   gates, novelty and fact-check are evidence, clarity is advisory.

## Phase 6 — Final report with coverage audit

Deliver a single document in exactly this order:

```
# Review: [paper title]
## Panel decision        (decision + score arithmetic + one-paragraph rationale)
## Summary of the paper  (neutral, 1 paragraph)
## Meta-review minutes   (from Phase 5)
## Individual reviews    (R1, R2, R3 — post-deliberation, with changes noted)
## Grounded findings     (novelty scout table, citation fact-check table)
## Claims–evidence table (from Phase 1, final statuses)
## Unanswered questions  (Phase 4 residue — framed as questions for the authors)
## Revision notes        (clarity/writing, prioritized, non-blocking)
## Coverage audit
```

The **coverage audit** is the skill's self-check and must be honest:

| Section | R1 | R2 | R3 | Claims traced | Q&A touched |
|---------|----|----|----|---------------|-------------|

Every content section must be addressed by at least one reviewer and appear in at least one
claim trace or Q&A answer. If the audit reveals a gap, go back and close it before
delivering — an empty cell in this table means the review is not done, because the whole
point of this protocol is that nothing gets skimmed.

Length calibration: a full paper warrants roughly 1,500–3,000 words of report. For a short
draft or single chapter, keep the same structure but compress; never drop the claims table,
the Q&A probe, or the coverage audit — those three are the holism guarantee.
