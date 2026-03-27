---
name: synthesis-fact-checking
description: "Systematic fact-checking process for verifying claims in articles and blog posts, particularly those synthesized from multiple AI deep-research outputs. Use when asked to: fact-check, verify claims, verify sources, check accuracy, citation verification, review factual accuracy, validate references."
license: "CC0-1.0"
depends_on: ["synthesis-content-quality"]
metadata:
  author: "Rajiv Pant"
  version: "1.0.0"
  source_repo: "github.com/rajivpant/synthesis-skills"
  source_type: "public"
---

# Fact-Check Process for Blog Post Writing

## Purpose

This skill provides a repeatable process for verifying the factual accuracy of blog posts and thought-leadership articles before publication. It is designed for content that synthesizes findings from multiple research sources, including AI deep-research outputs, where errors tend to be subtle rather than obvious.

The companion skill, the synthesis-content-quality skill, addresses stylistic and structural quality. This skill addresses factual correctness.

---

## Process Overview

1. Claim Extraction
2. Multi-Source Confidence Assessment
3. Verification by Source Hierarchy
4. Common Error Pattern Detection
5. Quote Verification
6. Study Verification
7. Temporal Verification (if backdated)
8. Documentation
9. Pre-Publish Checklist

---

## 1. Claim Extraction

Before verifying anything, extract every verifiable claim from the draft into a structured checklist. This prevents the common failure mode of reading through a draft and "feeling" like it is correct without actually checking anything.

### Claim Categories

Go through the draft and flag every instance of:

| Category | What to look for | Example |
|----------|-----------------|---------|
| **Statistics / Numbers** | Percentages, dollar amounts, headcounts, growth rates | "67% of workers reported reduced burnout" |
| **Study Names** | Named research papers, reports, surveys | "The Stanford HAI 2024 AI Index Report" |
| **Author Names** | Researchers, executives, experts quoted or cited | "Erik Brynjolfsson and colleagues" |
| **Dates** | Publication years, event dates, timeframes | "A 2023 study found..." |
| **Direct Quotes** | Any text in quotation marks attributed to a person | "As Jensen Huang noted, '...'" |
| **Organization Names** | Companies, unions, agencies, universities | "The Bureau of Labor Statistics" |
| **Causal Claims** | Assertions that X caused Y, or X leads to Y | "Automation led to a 40% increase in output" |
| **Comparative Claims** | Rankings, "first," "largest," "fastest-growing" | "The largest study of its kind" |

### Extraction Process

1. Read the draft paragraph by paragraph.
2. For each paragraph, identify every claim that could be verified or falsified by checking a source.
3. Record each claim in a checklist (see the Documentation Template below).
4. Do not skip claims that "sound right" -- those are often the ones that are subtly wrong.

### What Counts as a "Claim"

A claim is any statement that asserts a fact about the external world. Opinions, arguments, and analysis are not claims (though they may contain embedded claims). The sentence "AI will transform healthcare" is an opinion. The sentence "A 2024 McKinsey report estimated that AI could generate $4.4 trillion in economic value annually" contains three verifiable claims: the report exists, it is from McKinsey, and the figure is $4.4 trillion in economic value.

---

## 2. Multi-Source Confidence Framework

When synthesizing from multiple research sources (e.g., several AI deep-research outputs on the same topic), the degree of agreement between sources provides a useful -- but not sufficient -- signal for accuracy.

### Confidence Levels

| Source Agreement | Confidence | Required Action |
|-----------------|------------|-----------------|
| **3-4 sources cite the same claim** | Very high | Still verify against a primary source. Cross-corroboration among LLM outputs can reflect shared training data, not independent confirmation. |
| **2 sources cite the same claim** | High | Verify numbers, names, and framing against a primary source. Direction is likely correct; specifics may differ. |
| **1 source cites the claim** | Moderate | Must verify before including. Single-source claims from AI research outputs have a meaningful hallucination risk. |
| **Sources conflict on the same claim** | Low | Go to the primary source. Do not average, do not pick the "most credible" AI output -- find the original. |

### Why Cross-Corroboration Among AI Outputs Is Not Independent Verification

Multiple LLM research outputs may agree on a claim because they draw from the same underlying training data or the same secondary sources, not because they independently verified it. Three AI outputs all saying "the McKinsey study found X" may trace back to the same blog post that misquoted the McKinsey study. Agreement among AI outputs raises confidence, but it does not replace primary-source verification.

---

## 3. Verification Hierarchy

Not all sources are equal. When verifying a claim, seek the highest-quality source available.

### Source Quality Ranking

1. **Primary sources** -- The original journal paper, official report, press release, or direct statement. This is the standard against which all claims should be verified.
2. **Authoritative secondary sources** -- Reporting by established news organizations that cite primary sources. Useful when the primary source is paywalled or difficult to locate.
3. **Tertiary sources** -- Other blog posts, summaries, encyclopedia entries. Helpful for locating primary sources but never the final verification.
4. **LLM training data / AI research outputs** -- The lowest tier. These are what you are fact-checking, not what you fact-check against.

### What to Verify by Claim Type

**For statistics:**
- The number itself
- The framing of what the number measures (this is where most errors occur -- see Common Error Patterns)
- The time period the number covers
- The entity that produced the number

**For academic studies:**
- See the full Study Verification Protocol below.

**For quotes:**
- See the full Quote Verification Protocol below.

**For organization names:**
- Verify the exact legal or commonly used name
- Check for parent/subsidiary confusion (e.g., a union local vs. its national affiliate)
- Verify the organization exists and is described accurately

**For causal claims:**
- Verify that the cited source actually asserts causation, not merely correlation
- Check whether the source uses hedged language ("may," "could," "associated with") that the draft has strengthened into definitive claims

---

## 4. Common Error Patterns

These are the most frequent error types found during fact-checking of articles synthesized from AI research outputs, listed in rough order of frequency.

### 4a. Wrong Framing of Correct Numbers

The number is right, but the description of what it measures is wrong.

**Example:**
- Draft says: "$4.4 trillion in productivity growth potential"
- Source actually says: "$4.4 trillion in economic value added"
- The number is correct. The characterization is not.

**Why this happens:** AI research outputs sometimes paraphrase the framing around a number, and each paraphrase drifts slightly from the original.

**How to catch it:** When verifying a statistic, do not just confirm the number -- read the sentence in the primary source and compare the full framing.

### 4b. Conflating Related but Distinct Findings

Two findings from the same source get merged into one.

**Example:**
- Draft says: "96% of companies are reinvesting productivity gains from AI"
- Source actually says: "96% of companies experienced productivity gains" (one finding) and "companies are reinvesting gains" (a separate, qualitative finding without a percentage)

**How to catch it:** When a claim attributes both a number and a qualitative description to the same source, verify that they belong to the same finding -- not two adjacent findings.

### 4c. Wrong Specifics from Correct General Findings

The direction of the finding is right, but a specific number is wrong.

**Example:**
- Draft says: "67% of workers reported reduced burnout"
- Source actually says: 71% reported reduced burnout. The 67% came from a different metric.

**How to catch it:** When verifying a specific number, confirm that it belongs to the exact finding described, not a neighboring one.

### 4d. Incorrect Organization or Entity Names

The wrong name is used for an organization, often substituting a parent for a subsidiary or affiliate.

**How to catch it:** Verify organization names against their own official materials, not against secondary coverage.

### 4e. Misattributing Quotes or Examples to Wrong Entities

Two examples from different entities in the same source article get attributed to one entity.

**How to catch it:** For any claim that combines a concrete example with a quote, verify that both originate from the same entity.

### 4f. Hallucinated Citations

Studies, papers, reports, or quotes that do not exist. The citation sounds plausible -- correct-sounding author names, a reasonable journal, a believable title -- but no such work can be found.

**How to catch it:** Search for the paper by title, by authors, and by DOI if provided. If none of these searches return the paper, it likely does not exist. See the Study Verification Protocol.

### 4g. Outdated or Superseded Data

Using older figures when newer data is available, or citing preliminary findings that were revised in the final publication.

**How to catch it:** When verifying a statistic from a recurring report (annual indexes, quarterly surveys), check whether a more recent edition exists. When citing working papers, check if a final version has been published.

---

## 5. Quote Verification Protocol

Direct quotes carry high credibility with readers. A fabricated or misattributed quote damages trust disproportionately. Verify every direct quote in the draft.

### Verification Steps

1. **Verify the quote exists.** Search for the exact quote (or a distinctive phrase within it) using quotation marks to force exact-match results. If no results appear, the quote may be fabricated.
2. **Verify exact wording.** Compare the quote word-for-word against the primary source. Even small changes ("can" vs. "could," "will" vs. "may") can alter meaning.
3. **Verify correct attribution.** Confirm that the person named actually said or wrote the quote. Famous quotes are frequently misattributed.
4. **Verify the context.** Read the surrounding text in the original source to confirm the quote means what the draft implies.
5. **Identify the source type.** Note whether the quote comes from a published work, a media interview, a speech, a social media post, or a press release.

### Red Flags

- A quote that is too perfectly aligned with the article's thesis -- real quotes are often messier
- A quote that cannot be found anywhere on the web
- A quote attributed to a famous person that sounds like something they would say but has no verifiable origin
- A quote that appears in AI research outputs but not in any primary source

---

## 6. Study Verification Protocol

Academic studies and research reports are among the most commonly hallucinated or misrepresented elements in AI-synthesized content.

### Verification Steps

1. **Verify the study exists.** Search by title, by authors, or by the institution that produced it. Use Google Scholar, the publisher's website, or the institution's publications page.
2. **Verify the working paper or publication number.** If a specific paper number is cited, confirm it matches the actual paper.
3. **Verify ALL author names.** Check first and last names of every listed author. AI outputs sometimes add, remove, or swap authors.
4. **Verify the journal or publisher.** Confirm the paper was published where the draft says it was.
5. **Verify sample size and methodology.** If the draft describes the study's methodology, confirm these details against the paper.
6. **Verify the specific findings cited.** Read the relevant section and confirm:
   - The direction of the finding (positive/negative effect)
   - The magnitude (exact numbers, confidence intervals)
   - The framing (what was measured, what population)
   - Any caveats or limitations the authors stated
7. **Check for retraction, correction, or supersession.** Search Retraction Watch or the journal's errata page. Check if a newer version or follow-up has been published.

### When the Study Cannot Be Found

If you cannot locate a cited study after a thorough search:
- It may be hallucinated. Remove the citation.
- If the underlying claim is important, find a different, verifiable source for the same point.
- If no verifiable source exists, either remove the claim or hedge it explicitly ("some researchers have suggested...").

---

## 7. Temporal Verification (for Backdated Articles)

When writing or revising an article with a publication date in the past, temporal integrity must be maintained.

### Rules

1. **All cited sources must predate the article's stated publication date.** If the article is dated October 2024, every source cited should have been published before October 2024.
2. **External sources that postdate the article date require an explicit "Updated on" note.**
3. **Time-relative language must be accurate relative to the article date.** Words like "recently," "this year," "last month," and "emerging" must make sense from the perspective of the article's stated publication date, not the actual writing date.
4. **Do not cite preliminary data if final data was available by the article date.**

### Common Temporal Errors

- Calling a 2022 report "recent" in an article dated 2025
- Citing a December 2024 source in an article dated November 2024
- Using phrases like "the emerging field of..." for something well-established by the article date
- Describing future events as future when they have already occurred by the article date

---

## 8. Documentation Template

Create a `review-log.md` file alongside the draft to document the fact-checking process. This serves as an audit trail and protects against future challenges to the article's accuracy.

### Template

```markdown
# Fact-Check Review Log

**Article:** [Title of article]
**Article Date:** [Publication date]
**Reviewer:** [Name]
**Review Date:** [Date of review]
**Sources Used for Synthesis:** [List research sources that informed the draft]

---

## Claims Reviewed

### Claim 1: [Brief description of the claim]
- **Draft text:** "[Exact text from draft]"
- **Status:** Verified / Needs Correction / Cannot Verify / Removed
- **Source:** [Primary source used for verification, with URL or citation]
- **Finding:** [What the verification revealed]
- **Correction applied:** [What was changed, if anything]

### Claim 2: [Brief description]
- **Draft text:** "..."
- **Status:** ...
- **Source:** ...
- **Finding:** ...
- **Correction applied:** ...

[Continue for all claims]

---

## Editorial Decisions

- [Decision 1: e.g., "Removed claim about X because no primary source could be located"]
- [Decision 2: e.g., "Used 2024 figure instead of 2023 figure because the report is updated annually"]
- [Decision 3: e.g., "Hedged claim Y with 'approximately' because sources gave slightly different numbers"]

---

## Summary

- **Total claims reviewed:** [N]
- **Verified as stated:** [N]
- **Corrected:** [N]
- **Removed:** [N]
- **Cannot verify (hedged):** [N]
```

### Usage Notes

- Create one review log per article.
- Store it alongside the draft or in a dedicated review directory, depending on the workflow.
- The review log is an internal document. It does not need to be published, but it should be retained.

---

## 9. Pre-Publish Checklist

Run through this checklist after completing the fact-check review and before publishing. Every item should be checked.

### Factual Accuracy

- [ ] All statistics verified against primary sources (not just the number -- the framing of what the number measures)
- [ ] All study names verified (title, authors, publisher, paper number)
- [ ] All study findings verified (direction, magnitude, and framing match the source)
- [ ] All direct quotes verified for exact wording against a primary source
- [ ] All direct quotes verified for correct attribution (right person, right context)
- [ ] All organization names verified against official sources (not parent/subsidiary confusion)
- [ ] No conflated findings -- each claim maps to a single finding in a single source
- [ ] No hallucinated citations -- every cited source exists and says what the draft claims

### Temporal Integrity (if article is backdated or date-sensitive)

- [ ] All cited sources predate the article's publication date
- [ ] Any post-date sources are marked with "Updated on" notes
- [ ] Time-relative language ("recently," "this year," "emerging") is accurate relative to the article date
- [ ] No references to events or data that postdate the article without explicit notation

### Documentation

- [ ] Review log documents every claim checked
- [ ] Corrections are recorded in the review log
- [ ] Editorial decisions are documented
- [ ] Claims that cannot be verified have been removed or hedged with appropriate language

### Cross-Check with Quality Skill

- [ ] Article has been reviewed against the synthesis-content-quality skill for stylistic issues
- [ ] No vague attributions remain ("experts say," "studies show") -- all attributions are specific
- [ ] No placeholder text (`[source needed]`, `TODO`, `VERIFY`) remains in the draft

---

## Quick Decision Tree

When encountering a claim during fact-checking:

```
Is the claim verifiable?
+-- No -> It is an opinion or argument. No verification needed (but check for embedded claims).
+-- Yes ->
    Can you find a primary source?
    +-- Yes ->
    |   Does the primary source confirm the claim exactly?
    |   +-- Yes -> Mark as Verified.
    |   +-- No ->
    |       Is the discrepancy in the number, the framing, or both?
    |       +-- Number -> Correct the number.
    |       +-- Framing -> Correct the framing to match the source.
    |       +-- Both -> Rewrite the claim from the primary source.
    +-- No ->
        Can you find a credible secondary source?
        +-- Yes -> Verify against the secondary source and note the limitation.
        +-- No ->
            Is the claim essential to the article?
            +-- Yes -> Find an alternative source for the same point, or hedge explicitly.
            +-- No -> Remove the claim.
```
