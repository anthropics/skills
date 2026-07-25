# RFP Anti-Patterns — Failure Modes the Skill Refuses to Enable

Eight RFP-response failure modes documented across Shipley failure-mode analyses, APMP case studies, Strategic Proposals research, federal loss reviews, MIT Sloan B2B research, Bain commercial-discipline studies, and Gartner. Each anti-pattern names what goes wrong, why teams fall into it, and how the skill prevents it.

## 1. Inventing claims to fill GAP requirements

**Failure mode:** A MANDATORY requirement has no matching proof point. Under deadline pressure, the proposal team writes prose that implies coverage without naming a verifiable source.

**Why it happens:** The team confuses "we could probably do this" with "we have done this and can prove it." Sales pressure to bid combines with no-one-wants-to-be-the-one-who-said-no dynamics.

**Why it loses:** Evaluators verify. When references, certifications, or technical attestations don't substantiate the claim, the response loses on credibility AND on the original requirement. APMP case-study data: invented claims are detected in 60-80% of evaluations and cause loss-of-trust effects that cascade across other sections.

**How the skill prevents it:** `response_drafter.py` surfaces GAP requirements explicitly. Leadership decides: close the gap pre-submission, partner-bid, or no-bid. The skill refuses to generate proof-point language for GAP rows. **Hard rule.**

## 2. No bid/no-bid review — respond to every RFP

**Failure mode:** Every RFP gets a response. Win-rate collapses to 5-12%; sales-engineering capacity burns on pursuits with no relationship, no fit, no champion.

**Why it happens:** Sales teams optimize for activity metrics, not win-rate. Marketing measures responses-sent, not responses-won.

**Why it loses:** Bain research: disciplined bid/no-bid gates lift win-rate from ~15% to ~35%. Without a gate, the team is structurally outperformed by competitors who qualified out and concentrated resources on winnable pursuits.

**How the skill prevents it:** `winrate_predictor.py` produces an explicit BID / PARTNER-BID / NO-BID verdict. <20% estimate triggers automatic NO-BID. The skill names this in writing — leadership cannot override silently.

## 3. Missing mandatory disqualifiers until Day 12

**Failure mode:** FedRAMP, HIPAA, ISO 27001, SOC 2, on-shore data residency — a MANDATORY certification or compliance requirement is buried on page 47 of the RFP and discovered after 10 days of proposal work.

**Why it happens:** No parse-pass on Day 1. The team reads the RFP as prose, not as a structured requirement set.

**Why it loses:** The pursuit is unrecoverable. All work product to date is wasted. Worse, the team loses 2 weeks of capacity that could have been spent on winnable pursuits.

**How the skill prevents it:** `rfp_parser.py` runs on Day 1, tags every MANDATORY requirement, and produces a compliance-matrix view. MANDATORY GAPs surface immediately, not on Day 12.

## 4. No win-theme — generic response

**Failure mode:** The response could be sent verbatim by any competitor. Capabilities are listed; differentiation is implicit; the "why us" answer is decorative ("we're the leader in X").

**Why it happens:** Win-themes are hard. They require buyer-side framing ("your team reduces X by Y") rather than seller-side feature lists. Teams default to feature lists because they're easy to write.

**Why it loses:** Shipley failure-mode analysis: generic responses lose 70%+ of evaluations where any competitor produced a buyer-anchored win-theme. Evaluators ladder themes back to evaluation criteria; generic responses can't do this.

**How the skill prevents it:** `response_drafter.py` threads each declared win-theme through the requirements list. Themes appearing in <2 requirements are flagged **DECORATIVE**. The skill forces theme-discipline.

## 5. Answering the question you wanted asked, not the question they asked

**Failure mode:** The team reframes buyer questions to match their proposal narrative. Section structure is re-ordered for "flow." Buyer-specific terminology is replaced with seller-preferred vocabulary.

**Why it happens:** Habit. Proposal teams trained on free-form proposals carry that discipline into RFP responses. Marketing prefers branded vocabulary.

**Why it loses:** Strategic Proposals research: evaluators score on traceability. A response that doesn't visibly answer the buyer's question in the buyer's order loses 20-30 points of available score before content quality is assessed.

**How the skill prevents it:** `rfp_parser.py` extracts requirements in the buyer's order with the buyer's text preserved. `response_drafter.py` builds the compliance matrix on the buyer's requirement IDs. Reframing is not supported.

## 6. No compliance matrix — no traceability

**Failure mode:** The response is a long prose document. No table shows which requirement is answered on which page. Evaluators scoring against a 60-row rubric give up after 15 minutes of search and default-score.

**Why it happens:** Compliance matrices are tedious to maintain when content changes. Teams skip them under deadline pressure.

**Why it loses:** APMP BoK: response traceability is one of the top-3 evaluator-cited differentiators. Without a matrix, the evaluator scores on what they can find — which is less than what you wrote.

**How the skill prevents it:** `response_drafter.py` outputs a markdown compliance matrix as its primary artifact. Every requirement → match level → proof point → verifiable source. The matrix IS the response architecture.

## 7. Late-entry without acknowledging the relationship deficit

**Failure mode:** The team enters the RFP cold. No prior engagement, no champion, no executive sponsor at the buyer. The proposal is written as if entry timing didn't matter.

**Why it happens:** Optimism bias. The team believes content quality can overcome structural disadvantage.

**Why it loses:** Forrester: late-entry vendors win 8-12% of RFPs vs 25-35% for capture-engaged vendors. Federal RFP loss reviews show late-entry as the #1 named factor in 40%+ of post-mortems.

**How the skill prevents it:** `winrate_predictor.py` requires `late_entry` as input. Setting it to `true` applies a −15% penalty. The estimate honestly reflects the structural deficit; leadership decides whether to spend pursuit budget anyway.

## 8. Treating WEIGHTED requirements like MANDATORY

**Failure mode:** The team gives equal effort to every WEIGHTED requirement. A 25-point requirement and a 5-point requirement get the same proof-depth, the same page count, the same proof-point recruitment effort.

**Why it happens:** No effort-weighting against the scoring rubric. Either the rubric wasn't disclosed and the team didn't ask, or the rubric was disclosed and the team ignored it.

**Why it loses:** Shipley capture math: WEIGHTED scores compound. Optimizing the top-3 weighted requirements (typically 60-70% of available points) wins more often than uniform-mediocrity across all weighted requirements. McKinsey B2B research: rubric-weighted-effort respondents win 1.6x more than equal-effort respondents.

**How the skill prevents it:** `rfp_parser.py` extracts disclosed scoring weights into the requirement evidence. `response_drafter.py` shows weights in the compliance matrix. Forcing-question #7 ("What does the buyer's evaluation team actually score on?") interrogates whether the weighting was even requested.

## Sources

1. **Shipley Associates failure-mode analyses** — internal post-loss reviews published in *Proposal Guide v6* appendix and in *Capture Guide* case studies. Source for anti-patterns 1, 4, 5.

2. **APMP (Association of Proposal Management Professionals) case studies** — APMP BoK appendix and APMP Journal case studies. Source for anti-pattern 1 (invented-claim detection rates) and anti-pattern 6 (traceability as top-3 differentiator).

3. **Strategic Proposals (strategicproposals.com) research and benchmarks** — published rubric-replication-gap data; source for anti-pattern 5 (evaluator-traceability scoring).

4. **Federal RFP loss reviews** — debrief reports available through FOIA and GSA's procurement transparency programs. Source for anti-pattern 7 (late-entry as #1 named loss factor in 40%+ of post-mortems).

5. **MIT Sloan B2B sales research**, MIT Sloan Management Review archives. Source for anti-pattern 8 (rubric-weighted-effort win-rate multiplier).

6. **Bain & Company commercial-discipline studies** — Bain B2B sales practice publications and conference presentations. Source for anti-pattern 2 (disciplined-pursuit win-rate of ~35% vs respond-to-everything ~12%).

7. **Gartner, RFP Best Practices and IT Buyer Studies**. Source for anti-pattern 6 (compliance-matrix presence as evaluator-cited differentiator) and the general industry-vertical evaluation-cycle benchmarks.

8. **Patrick Lencioni, *Getting Naked* (Jossey-Bass, 2010)**. Source for the "tell the kind truth" principle that operationalizes the skill's GAP-honesty hard rule (anti-pattern 1).
