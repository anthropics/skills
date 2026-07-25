# Plagiarism Detection Protocol — Phase D Originality Verification Protocol

This document defines the complete execution protocol for `integrity_verification_agent`'s Phase D (originality verification), including paragraph-level comparison, self-plagiarism check, AI-generated text characteristic detection, severity grading, and tool limitation disclaimers.

---

## Phase D Overview: Originality Verification

Phase D's purpose is to perform originality screening on body text content before paper submission for review and after revision completion. Unlike Phases A-C which focus on "whether citations and data are correct," Phase D focuses on "whether the body text itself is originally written."

**Core principle: Heuristic screening, not final determination.** This protocol uses WebSearch for publicly available literature comparison. Results are preliminary screening signals and do not equate to conclusions from professional plagiarism detection software.

---

## D1: Paragraph-Level Originality Check

### D1.1 Characteristic Sentence Extraction

```
For each paragraph in the paper body text:
1. Identify the paragraph's topic and core argument
2. Extract 1-2 "characteristic sentences"
   - Priority selection: Sentences containing specific data, proper nouns, or unique arguments
   - Avoid: Generic academic boilerplate (e.g., "This study aims to...")
3. Record the characteristic sentence's paragraph location (section + paragraph number)
```

### D1.2 WebSearch Comparison

```
For each extracted characteristic sentence:
1. Use the characteristic sentence (or key fragment) as a WebSearch query
   - Search term: Enclose 8-12 consecutive words in quotation marks
   - Supplementary search: Remove quotes to check for paraphrased versions
2. Review the top 5-10 search results
3. Compare text similarity between original and search results
```

### D1.3 Comparison Result Grading

| Grade | Code | Definition | Determination Criteria |
|-------|------|-----------|----------------------|
| Original | `ORIGINAL` | No similar expression found in public literature | WebSearch returns no related matches |
| Common Knowledge | `COMMON_KNOWLEDGE` | The knowledge is a widely accepted fact in the field | Multiple sources express the same fact in different ways |
| Paraphrase | `PARAPHRASE` | Expresses same viewpoint as a source but with clearly different wording | Semantically similar but significantly different sentence structure and word choice, with citation |
| Close Match | `CLOSE_MATCH` | Highly similar wording to a source, with only a few words substituted | Nearly identical sentence structure, with only synonym substitutions or word order changes |
| Verbatim | `VERBATIM` | Identical or nearly identical text to a source | 20+ consecutive identical words without quotation marks |

### D1.4 Sampling Rate Requirements

| Operating Mode | Minimum Sampling Rate | Description |
|---------------|----------------------|------------|
| Mode 1 (pre-review) | **30%** | At least 30% of all body text paragraphs checked |
| Mode 2 (final-check) | **50%** | At least 50% of all body text paragraphs checked |

**Sampling strategy**:
- Priority check: Literature Review, Background, Discussion and other high-risk sections
- Must cover: At least 1 paragraph sampled from each major chapter
- Random supplement: Beyond priority paragraphs, randomly sample paragraphs to reach minimum sampling rate
- Revised paragraphs: In Mode 2, all paragraphs newly added or substantially modified during revision must be checked 100%

---

## D2: Self-Plagiarism Check

### D2.1 Author's Existing Publications Search

```
Prerequisite: User provides author name(s)

For each author (or primary author):
1. WebSearch: "author name" + research area keywords
2. Identify author's existing publication list (Google Scholar profile preferred)
3. Record existing publications related to the current paper's topic
```

### D2.2 Comparison Items

```
Compare current paper with author's existing publications (focus on these areas):
1. Methodology descriptions:
   - Is the research design description verbatim identical to prior work?
   - Are data collection and analysis method descriptions directly copied?
2. Results narratives:
   - Are textual descriptions of results reused?
   - Are table/figure description texts identical?
3. Theoretical framework:
   - Are literature review paragraphs transferred wholesale?
```

### D2.3 Legitimate Self-Citation vs. Self-Plagiarism Determination Criteria

| Scenario | Determination | Description |
|----------|--------------|------------|
| Cites prior work and restates in new language | **Legitimate self-citation** | Normal academic practice — has citation and paraphrasing |
| Cites prior work but verbatim copies original text | **Self-plagiarism** | Even with citation, extensive verbatim copying is unacceptable |
| Content highly similar to prior work without citing it | **Self-plagiarism** | Conceals relationship with prior work |
| Uses prior work's data but re-analyzes | **Legitimate** | Secondary analysis is a legitimate research method — must clearly state this |
| Methodology reuses prior work's standardized description | **Gray area** | Standardized experimental procedure descriptions allow high similarity, but citing prior work is recommended |

---

## D3: AI-Generated Text Characteristic Detection

**Important disclaimer: This section is a checklist, not a determination tool.** AI text detection technology is not yet mature, and any judgment based on text characteristics has a high false-positive risk. The following indicators are for reference only and should not serve as the basis for final determination.

### D3.1 Typical AI Writing Pattern Indicators

| # | Indicator | Description | Observation Method |
|---|-----------|------------|-------------------|
| 1 | Excessive smoothness | Abnormally uniform sentence fluency throughout, lacking natural writing rhythm variation | Compare whether writing style across chapters is overly consistent |
| 2 | Lack of specificity | Arguments remain at conceptual level, lacking specific numbers, cases, or personal research experience | Check for "for example" followed by vague content |
| 3 | Formulaic transitions | Heavy use of "Furthermore," "Moreover," "It is worth noting that" and similar transitions | Count the variety and frequency of transition phrases |
| 4 | Excessive parallelism | Highly symmetric paragraph structures (e.g., every paragraph follows: claim -> evidence -> summary) | Observe whether paragraph structure mechanically repeats |
| 5 | Hedging overload | Excessive use of "may," "could," "might," "it is possible that" to avoid definitive positions | Check whether author over-hedges even on their own research results |
| 6 | Citation-argument gap | Literature is cited but the cited content is not organically integrated with the author's arguments | Remove citations — does the paragraph's argument still hold? |

### D3.2 Handling Approach

```
If the paper triggers 2 or more AI writing indicators:
1. Flag in the verification report as "AI writing characteristic alert"
2. List the specific indicators triggered and corresponding paragraphs
3. Do NOT make a "whether it is AI-generated" determination
4. Recommend the user review the flagged paragraphs and consider adjusting writing style
```

---

## Severity Grading

| Level | Code | Definition | Trigger Conditions |
|-------|------|-----------|-------------------|
| **Critical** | `CRITICAL` | Severe academic misconduct, sufficient for retraction | Verbatim plagiarism (>20 consecutive identical words without citation); fabricated citations (citing nonexistent sources to support plagiarized content) |
| **Serious** | `SERIOUS` | Significant originality problems, requiring major revisions | Multiple close paraphrases without citing sources; extensive undisclosed self-plagiarism |
| **Moderate** | `MODERATE` | Individual paragraphs need rewriting | Individual paragraphs inadequately paraphrased (1-2 instances of `CLOSE_MATCH`); methodology description overly similar to prior work |
| **Minor** | `MINOR` | Does not affect academic integrity but improvement recommended | Excessive generic academic boilerplate; AI writing characteristic alerts (informational only, does not affect verdict) |

### Severity-to-Verdict Mapping

| Severity | Impact on Verdict |
|---------|-----------------|
| CRITICAL | Immediate FAIL, listed as highest priority correction item |
| SERIOUS | FAIL, must fix and re-verify |
| MODERATE | FAIL, must fix |
| MINOR | Does not affect PASS/FAIL verdict, noted in report |

---

## Tool Limitation Disclaimer

This protocol's originality verification has the following inherent limitations that users must be aware of:

| # | Limitation | Description |
|---|-----------|------------|
| 1 | **Not professional plagiarism detection software** | This protocol uses WebSearch for heuristic comparison, not Turnitin, iThenticate, or other professional tools — cannot calculate precise text overlap rates |
| 2 | **Limited coverage** | Can only compare publicly searchable literature (open access, preprints, web pages) — cannot search full-text databases behind paywalls |
| 3 | **Language limitation** | Cross-language plagiarism (e.g., plagiarism via translation) is difficult to detect |
| 4 | **Sampling, not exhaustive** | Limited by efficiency, only 30%-50% of paragraphs are sampled — missed detection risk exists |
| 5 | **Time sensitivity** | Search results change over time; newly published literature may not be in search scope |
| 6 | **AI detection unreliable** | D3's AI writing indicators are heuristic alerts with high false-positive rates and should not serve as determination basis |

**Recommendation**: This protocol's results serve as preliminary screening. It is recommended to use professional plagiarism detection tools (such as Turnitin / iThenticate) for complete duplicate checking before formal submission.

---

## Output Format Template

```markdown
## Phase D: Originality Verification Results

### Verification Parameters
- Operating mode: [Mode 1 pre-review / Mode 2 final-check]
- Total body text paragraphs: X
- Paragraphs sampled: Y (sampling rate: Z%)
- Author self-plagiarism check: [Executed / Not executed (author information not provided)]

### D1 Paragraph-Level Comparison Results Summary

| Grade | Paragraph Count | Proportion |
|-------|----------------|-----------|
| ORIGINAL | X | X% |
| COMMON_KNOWLEDGE | X | X% |
| PARAPHRASE | X | X% |
| CLOSE_MATCH | X | X% |
| VERBATIM | X | X% |

### D2 Self-Plagiarism Check Results

| # | Current Paper Paragraph | Existing Publication | Similarity Type | Determination |
|---|------------------------|---------------------|----------------|--------------|
| 1 | §X.X, paragraph Y | Author (Year), Title | Methodology description similar | Legitimate self-citation / Self-plagiarism |

### D3 AI Writing Characteristic Alerts

| # | Indicator | Triggered Paragraph | Description |
|---|-----------|---------------------|------------|
| 1 | [Indicator name] | §X.X | [Specific observation] |

Indicators triggered: X / 6 ([Below threshold, not flagged / Threshold reached, user review recommended])

### Phase D Issue List

| # | Severity | Type | Location | Issue Description | Matching Source | Recommended Action |
|---|----------|------|----------|------------------|----------------|-------------------|
| 1 | CRITICAL | VERBATIM | §X.X, paragraph Y | N consecutive words identical to source | [URL] | Rewrite or add quotation marks for direct quote |
| 2 | SERIOUS | CLOSE_MATCH | §X.X, paragraph Y | Highly similar wording, only a few words substituted | [URL] | Rewrite and add citation |
| 3 | MODERATE | Self-plagiarism | §X.X, paragraph Y | Methodology description verbatim identical to prior work | Author (Year) | Rewrite and cite prior work |

### Tool Limitation Disclaimer

> This originality verification uses WebSearch for heuristic comparison and is not professional plagiarism detection software (such as Turnitin / iThenticate). Coverage is limited to publicly searchable literature, with a sampling rate of [Z]%, and there is a risk of missed detection. These results serve as preliminary screening; it is recommended to use professional plagiarism detection tools for complete duplicate checking before formal submission.
```

---

## Relationship with Other Phases

| Phase | Focus | Relationship with Phase D |
|-------|-------|--------------------------|
| Phase A: Reference Verification | Whether references exist and are correct | A verifies sources, D verifies body text; if D finds VERBATIM without citation, it may also reveal A3 dangling citation issues |
| Phase B: Citation Context Verification | Whether citations accurately reflect original text | B checks "whether cited content is correct," D checks "whether uncited content is original" |
| Phase C: Data Verification | Whether statistical data is correct | C and D are complementary: C verifies data, D verifies text |

---

## Reproducibility Requirements

To ensure the originality verification process is reproducible:

1. **Standardized search strategy**: Use the same search template for each characteristic sentence
   - Search term 1: `"key fragment" (8-12 words, in quotes)`
   - Search term 2: `keyword combination (without quotes, to match paraphrases)`

2. **Explicit determination criteria**: Each grade (ORIGINAL through VERBATIM) has clear determination criteria, not relying on subjective feeling

3. **Complete records**: Search terms, search results, and determination rationale for each sampled paragraph are recorded in the Audit Trail

4. **Timestamps**: Report includes execution time, as search results change over time
