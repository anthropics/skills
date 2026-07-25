# Psychometric Terminology Glossary

**Spec:** v3.6.7 §7.1 — pattern protection reference for `research_architect_agent` (survey designer mode), Pattern B2.

**Audience:** Agents drafting Likert / rating-scale items in survey instruments. Human authors reviewing instrument drafts before pilot testing.

**Why this exists:** Live ARS pipeline runs surfaced two recurring failures in instrument design: (a) items labelled "reverse-coded" that were actually contrast items measuring a different construct, and (b) acquiescence- and recall-bias mitigations that look in place but do not operate. Both failures pass casual peer review and surface only at scale validation, by which point the instrument has already been deployed. This reference defines the operational distinctions the survey designer must respect.

---

## True reverse-coded item vs. contrast item

These are distinct instrument-design tools that look identical to a casual reader. Conflating them invalidates the construct.

### True reverse-coded item

**Operational definition:** A negatively-keyed statement of the **same construct** along the **same Likert dimension**. After numeric reversal of the response value, it contributes to the same scale score as positively-keyed items.

**Necessary conditions:**
- Same construct: if the positive item probes "perceived institutional support," the reverse item probes the absence of perceived institutional support, not a different construct.
- Same dimension: agreement-disagreement remains the response axis; frequency or intensity does not get substituted in.
- Reverse-scoring is mechanically valid: a respondent with high construct standing should give high agreement on positive items and low agreement on the reverse item, such that the reverse item's reversed score aligns with the positive items.

**Correct example pair (construct: perceived institutional support):**
- Positive: "My institution provides the resources I need to do my work well." (1=strongly disagree → 5=strongly agree)
- True reverse: "My institution leaves me without the resources I need to do my work." (same scale; respondents high in perceived support disagree with this)

**Why this works:** Both items load on a single latent factor. Confirmatory factor analysis on a piloted dataset will show comparable factor loadings (after sign reversal) and similar item-total correlations.

### Contrast item

**Operational definition:** A statement that probes a **different construct** (or a different dimension of the same construct) and is included to measure something else — discriminant validity, related-but-distinct construct, social-desirability check.

**Why it is not reverse-coding:**
- A contrast item's score should NOT be combined with the focal scale's score. It belongs on its own scale or its own analysis.
- Reverse-scoring a contrast item produces a meaningless number.
- Treating a contrast item as a reverse-coded item dilutes the focal scale's reliability (Cronbach's alpha drops; factor loadings become incoherent).

**Example contrast (NOT a reverse-coded support item):**
- "I find my work intrinsically meaningful." — This probes intrinsic motivation, not perceived institutional support. It is contrast / divergent-validity, not a reverse item.

### Decision rule for the survey designer

For every item labelled "reverse-coded," the agent must produce a one-line construct-equivalence justification:

> "Item X is true reverse-coded relative to focal items Y because it probes the same construct (perceived institutional support) on the same Likert dimension (agreement). It is not a contrast item probing a related construct."

If that justification cannot be written without slipping into a different construct, the item is **not** reverse-coded — it is a contrast item, and it must either move to its own scale or be removed.

---

## Acquiescence-bias mitigation

**The bias:** Respondents systematically agree with statements regardless of content. Pure-positive scales over-estimate construct standing.

**The standard mitigation:** Mix positive and true-reverse-coded items so that an acquiescing respondent cannot maximise scale score by agreeing throughout.

**The failure mode flagged in v3.6.7 patterns:** "Pseudo-reverse" items that look reverse-coded but are actually contrast items, leaving the scale effectively pure-positive. The pseudo-mitigation is worse than no mitigation because it gives the appearance of having addressed acquiescence while leaving it operative.

**Designer requirement:** Apply the construct-equivalence justification rule (above) to every reverse-coded item. If any "reverse-coded" item fails the justification, that item is mislabelled — it is a contrast item and must either move to its own scale or be removed. A scale that ends up with no surviving reverse-coded item after this filter has not mitigated acquiescence bias and needs redesign before pilot.

---

## Recall-bias mitigation

**The bias:** Respondents misremember the timing or details of past events. Two failure modes are common:

1. **Calendar drift:** Asking "in the last 12 months" without anchoring to a salient event produces noisy recall — respondents reconstruct an approximate window, not a true 12-month boundary.
2. **Telescoping:** Memorable events get pulled forward in time ("that happened last year" when it happened 18 months ago), inflating recent-period rates.

**The standard mitigation:** Event-anchored phrasing — anchor the recall window to a salient, datable event the respondent's unit shares.

**Correct phrasing (event-anchored, generic):**
> "Thinking about the period immediately before [the unit-specific event] happened to your unit, how often did X occur?"

**Correct phrasing (event-anchored, project-specific):**
> "Thinking about the period before your institution announced the merger in [month-year], how often did you experience X?"

**Calendar-anchored phrasing — only acceptable when the entire sample shares a common event date:**
> "In the 6 months following the [common event] of [specific date], how often did you experience X?"

**Wrong phrasing (calendar-only, no event anchor):**
> "In the last 12 months, how often did X occur?" — This invites calendar drift and telescoping; the respondent has no shared anchor.

**Designer requirement:** Default retrospective items to event-anchored phrasing. Only use calendar-anchored phrasing when the sample provably shares a common event date and that date is named in the item. When the event-anchor is absent, the item is not recall-bias-mitigated, even if it superficially looks like a retrospective survey item.

---

## Quick decision table

| Designer choice | Operational test | Failure flag |
|---|---|---|
| Item is reverse-coded | One-line construct-equivalence justification holds | Pseudo-reverse (contrast item mislabeled) |
| Acquiescence mitigated | At least one true reverse-coded item per scale AND every item labelled reverse-coded passes the construct-equivalence test | Pure-positive scale or pseudo-reverse mitigation |
| Recall-bias mitigated | Item anchors recall to a salient event the unit shares | Calendar-anchored without shared event date |

---

## Where this glossary is enforced

The `research_architect_agent` survey designer mode prompt enforces construct-equivalence justification, acquiescence-bias counting, and event-anchored phrasing. The authoritative protection clause lives in `deep-research/agents/research_architect_agent.md` under `PATTERN PROTECTION (v3.6.7)`. This file defines the construct-equivalence test, the acquiescence-mitigation rule, and the event-anchoring decision rule; the agent prompt cites this file by path.

---

## References

- DeVellis, R. F. (2017). *Scale Development: Theory and Applications* (4th ed.). Sage. — reverse-coding and acquiescence bias.
- Tourangeau, R., Rips, L. J., & Rasinski, K. (2000). *The Psychology of Survey Response*. Cambridge. — recall bias and event anchoring.
- Loftus, E. F., & Marburger, W. (1983). Since the eruption of Mt. St. Helens, has anyone beaten you up? Improving the accuracy of retrospective reports with landmark events. *Memory & Cognition*, 11(2), 114–120. — primary empirical source for event-anchoring effect.
