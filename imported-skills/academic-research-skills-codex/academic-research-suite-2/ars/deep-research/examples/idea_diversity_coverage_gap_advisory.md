# Idea Diversity / Coverage Gap Advisory Example

This example shows the two #257 advisory surfaces. Both are warnings for scholar attention, not blockers.

## 1. Socratic wording-pattern advisory

User draft:

> I want to study "exploring the impact of AI feedback on student motivation."

Socratic mentor response excerpt:

```markdown
[WORDING_PATTERN_ADVISORY]
Your phrasing "exploring the impact of AI feedback on student motivation" resembles a common AI-typical research-question shell: WP01 impact/effect frame. I am not judging the idea; I am only flagging the wording. What term, mechanism, site, or tension would a specialist in your field use instead?

What is the specific feedback situation you care about: automated scoring, formative comments, timing of feedback, or how students decide whether feedback is worth acting on?
```

Acceptable user choice:

- Keep the original phrasing because it matches a target journal's framing.
- Rephrase in domain-native terms, e.g. "How do first-year engineering students decide whether AI-generated formative comments are actionable during lab-report revision?"
- Ask the mentor to help stress-test scope without rewriting the RQ.

Boundary: the advisory does not say the idea is generic or bad. It flags only the wording shell.

## 2. Lit-review distributional skew advisory

Search context:

- RQ: "How do AI feedback systems shape student revision behavior in higher education?"
- Final included sources: 25
- Topic coverage: all major RQ subtopics covered
- Known venue/method metadata:
  - 23/25 sources are post-2023 NLP or learning-analytics venues
  - 21/24 known-method entries are quantitative log-data studies
  - 18/20 known-geography entries are North America or Western Europe

Search Strategy Report excerpt:

```markdown
### Coverage Distribution Advisory

DISTRIBUTIONAL_SKEW_ADVISORY:
- Dimension: time distribution
- Concentration: 2023-2026 = 23/25 (92%)
- Advisory: This is a coverage-distribution signal, not a defect. Consider whether the RQ warrants earlier foundational work on feedback uptake, revision behavior, or formative assessment.
- Search response: add backward citation chaining from foundational feedback-literacy and formative-assessment works.

DISTRIBUTIONAL_SKEW_ADVISORY:
- Dimension: methodological distribution
- Concentration: quantitative log-data studies = 21/24 (87.5%)
- Advisory: This is a coverage-distribution signal, not a defect. Consider whether the question warrants qualitative or mixed-method evidence about how students interpret feedback.
- Search response: add search string ("AI feedback" OR "automated feedback") AND ("student interpretation" OR "feedback literacy" OR interview OR qualitative).

DISTRIBUTIONAL_SKEW_ADVISORY:
- Dimension: geographic distribution
- Concentration: North America / Western Europe = 18/20 (90%)
- Advisory: This is a coverage-distribution signal, not a defect. Consider whether institutional context changes feedback uptake.
- Search response: add regional database search for Taiwan, East Asia, and bilingual higher-education studies.
```

Boundary: the bibliography is still valid. The advisory asks whether the corpus distribution matches the RQ; it does not reject the search or force expansion.
