---
scenario: Stage 2.5 integrity check fails, corrections made, re-verification passes
mode: full pipeline (mid-entry at Stage 2.5)
stages_shown: Stage 2.5 (FAIL -> corrections -> PASS)
demonstrates: How the pipeline handles integrity failures and guides recovery
---

# Integrity Failure Recovery Example

This example shows what happens when Stage 2.5 (Pre-Review Integrity Check) finds serious issues, how they are corrected, and how re-verification works. It demonstrates the pipeline's zero-tolerance integrity gate and the systematic correction workflow defined in `agents/integrity_verification_agent.md`.

## Scenario

A researcher submits a paper titled "Digital Transformation in European Higher Education: A Mixed-Methods Analysis of Institutional Readiness and Student Outcomes" for integrity verification. The paper has 45 references, makes 18 quantitative claims, and is entering the pipeline at Stage 2.5 after completing Stage 2 (WRITE).

**Paper details:**
- Word count: 7,200
- Structure: IMRaD
- Citation format: APA 7.0
- References: 45 entries (32 journal articles, 6 reports, 4 books, 3 working papers)

---

## Orchestrator: Stage 2 --> 2.5 Transition

```
━━━ Stage 2 (WRITE) Complete ━━━

Metrics:
- Word count: 7,200 (target: 7,000 +/-10%)    [OK]
- References: 45 (min: 30)                     [OK]
- Coverage: 6/6 sections drafted                [COMPLETE]

Deliverables:
- Paper Draft (7,200 words, IMRaD)
- Bilingual Abstract (EN 248 words + zh-TW 380 characters)
- Reference List (45 entries, APA 7.0)

Flagged: None

Next: Stage 2.5 (INTEGRITY) — Mandatory checkpoint.
This stage cannot be skipped. All references and data claims
will be verified before the paper proceeds to peer review.

Proceeding to Stage 2.5...
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## Stage 2.5: Pre-Review Integrity Check (Round 1)

```
Entering Stage 2.5 (INTEGRITY) -- Mode 1 (Pre-Review)

Loading integrity_verification_agent...
Executing: Phase A (Reference Verification) + Phase B (Citation Context, 31% spot-check)
         + Phase C (Data Verification) + Phase D (Originality, 33% spot-check)
         + Phase E (Claim Verification, 30% spot-check)
```

### integrity_verification_agent Output

**Mode**: Pre-review (Mode 1)
**Paper**: "Digital Transformation in European Higher Education: A Mixed-Methods Analysis of Institutional Readiness and Student Outcomes"

---

#### Phase A: Reference Existence Verification (45/45 checked)

| # | Reference | Status | Issue |
|---|-----------|--------|-------|
| 12 | Martinez, R. (2023). Artificial intelligence adoption in European universities: A cross-national survey. *Journal of Digital Education*, 15(2), 45-62. https://doi.org/10.1016/j.jde.2023.02.009 | FAIL | DOI resolves to a different article ("Machine Learning in K-12 Assessment" by Patel & Ross). No article with this exact title found in *Journal of Digital Education* or any indexed database. **GHOST REFERENCE** |
| 19 | Selwyn, N. (2022). Digital technologies and the automation of education. *Learning, Media and Technology*, 47(1), 1-5. | ISSUE | Article exists but published in 2023 (Vol. 48, No. 1), not 2022 (Vol. 47, No. 1). Correct DOI: https://doi.org/10.1080/17439884.2023.2141509 |
| 28 | European Commission. (2022). Digital Education Action Plan 2021-2027. Brussels: Publications Office of the European Union. | ISSUE | Title is "Digital Education Action Plan 2021-2027" but the official title is "Digital Education Action Plan (2021-2027)." Originally published September 2020, not 2022. The 2022 date may refer to a progress report, which is a different document. |
| 33 | Wong, K., & Liu, S. (2024). Blockchain-based micro-credentials in Asian higher education: A multi-site case study. *Higher Education Policy*, 37(1), 89-104. https://doi.org/10.1057/s41307-023-00318-5 | FAIL | Article exists but authors are Wong, K., & Liu, **S. K.** (not S.). Published in 2023 (online first), print edition 2024, Vol. **36**(4), pp. 612-629. DOI resolves to the correct article with the corrected metadata. |
| 41 | Organisation for Economic Co-operation and Development. (2021). *OECD Digital Education Outlook 2021*. OECD Publishing. | ISSUE | Correct title is *OECD Digital Education Outlook 2021: Pushing the Frontiers with Artificial Intelligence, Blockchain and Robots*. Subtitle is required per APA 7.0 for books. |
| -- | Remaining 41/45 references | PASS | All verified against DOI records, publisher databases, or Google Scholar. Bibliographic details match. |

**Phase A Summary**: 45 checked, 41 PASS, 2 FAIL (1 ghost reference, 1 wrong metadata), 2 ISSUE (wrong year/title)

---

#### Phase B: Citation Context Spot-Check (14/45 sampled = 31%)

| # | Citation | Location | Verdict | Detail |
|---|----------|----------|---------|--------|
| B1 | Ref 3 — Bond et al. (2020) | Section 2.1, para 2: "Bond et al. (2020) found that student engagement increased by 12-18% when blended learning was implemented with structured digital scaffolding." | PASS | Source (p. 847) reports "engagement scores improved between 12% and 18% across four cohorts," consistent with the paper's claim. |
| B2 | Ref 12 — Martinez (2023) | Section 2.3, para 1: "Martinez (2023) surveyed 1,200 faculty members across 15 EU countries and found that 68% reported using at least one AI tool in their teaching." | FAIL | **Cannot verify** — Ref 12 is a ghost reference (flagged in Phase A). The claim has no verifiable source. |
| B3 | Ref 22 — Castaneda & Selwyn (2018) | Section 2.2, para 3: "Critical scholars have argued that digital transformation in education is often driven by commercial interests rather than pedagogical evidence (Castaneda & Selwyn, 2018)." | PASS | Source discusses commercialization of EdTech; the paraphrase is a fair representation of the authors' argument (Chapter 3, pp. 45-52). |
| B4 | Ref 28 — European Commission (2022) | Section 1, para 2: "The European Commission committed EUR 2.1 billion to digital infrastructure in higher education between 2021 and 2025 (European Commission, 2022)." | ISSUE | Cannot confirm this exact figure in the Digital Education Action Plan. The EC Erasmus+ Digital allocation for 2021-2027 is approximately EUR 2.0 billion across all education sectors, not exclusively higher education. |
| B5 | Ref 33 — Wong & Liu (2024) | Section 2.4, para 1: "Wong and Liu (2024) demonstrated that blockchain micro-credentials improved employer trust in non-traditional qualifications by 41%." | ISSUE | Source reports 41% improvement in a specific employer survey (Table 3, p. 621 in the correct pagination), but the figure applies to "initial employer screening decisions," not general "employer trust." The paraphrase overgeneralizes. |
| -- | 9 additional citations sampled | Various | PASS | Context accurately reflects source content. |

**Phase B Summary**: 14 sampled, 11 PASS, 1 FAIL (ghost ref context), 2 ISSUE (data precision)

---

#### Phase C: Data Verification (18 quantitative claims checked)

| # | Claim in Paper | Cited Source | Verdict | Detail |
|---|---------------|-------------|---------|--------|
| C1 | "73% of EU universities have adopted a learning management system" (Section 1, para 3) | Ref 8 — Eurostat (2023), *Digital Economy and Society Index* | VERIFIED | DESI 2023 report (Table 4.2) states 73.1% of HEIs in EU-27 reported LMS adoption. |
| C2 | "Student satisfaction with digital learning increased by 34% between 2019 and 2022" (Section 4.1, para 2) | Ref 15 — Garcia, M. (2022). Student perceptions of emergency remote teaching. *Studies in Higher Education*, 47(8), 1620-1638. | MAJOR_DISTORTION | Source (p. 1631, Table 5) reports a **24% increase** in satisfaction with "specific digital tools," not a 34% overall increase. The 34% figure appears in a different column measuring "willingness to continue online learning," which is a distinct construct. |
| C3 | "The EU invested EUR 2.1 billion in digital infrastructure for higher education" (Section 1, para 2) | Ref 28 — European Commission (2022) | MINOR_DISTORTION | As noted in Phase B, the figure is approximately EUR 2.0 billion across all education sectors. "EUR 2.1 billion" and "higher education" both overstate the source. |
| C4 | "Faculty digital competency scores improved by 0.8 standard deviations after institutional training programs" (Section 4.2, para 3) | Ref 31 — Fernandez-Batanero et al. (2022) | VERIFIED | Source (p. 12, meta-analytic result) reports pooled effect size d = 0.79, rounded to 0.8 is acceptable. |
| C5 | "47% of interviewed faculty reported 'significant resistance' to mandatory digital tool adoption" (Section 4.3, para 1) | Paper's own interview data | VERIFIED | Internal consistency check: Table 6 shows 9 of 19 interviewees (47.4%) coded under "significant resistance" theme. Consistent. |
| C6 | "Only 12% of European universities have a dedicated Chief Digital Officer" (Section 5, para 2) | Ref 37 — Rampelt et al. (2019). *Digital Higher Education: A Dividing or Connecting Element?* EURASHE. | MINOR_DISTORTION | Source (p. 28) states "approximately 11% of surveyed institutions reported having a CDO or equivalent role." The paper says 12%, which is a minor rounding difference, but the source is from 2019 — the paper presents this as a current statistic without noting the 4-year gap. |
| -- | 12 additional claims | Various | VERIFIED | All match their cited sources within acceptable tolerance. |

**Phase C Summary**: 18 checked, 15 VERIFIED, 1 MAJOR_DISTORTION, 2 MINOR_DISTORTION

---

#### Phase D: Originality Check (33% paragraph sample)

| Grade | Paragraph Count | Proportion |
|-------|----------------|-----------|
| ORIGINAL | 12 | 63.2% |
| COMMON_KNOWLEDGE | 4 | 21.1% |
| PARAPHRASE | 3 | 15.8% |
| CLOSE_MATCH | 0 | 0% |
| VERBATIM | 0 | 0% |

**Phase D Summary**: 19/58 paragraphs sampled. No originality concerns detected. All paraphrased passages have proper citations.

---

#### Phase E: Claim Verification (30% spot-check, 6/18 claims)

Claims C1-C6 above were selected for the 30% spot-check. Results are reported in Phase C.

**Phase E Summary**: 6 claims checked, 3 VERIFIED, 1 MAJOR_DISTORTION, 2 MINOR_DISTORTION

---

### Verdict: FAIL

**Reason**: 2 SERIOUS issues + 2 MEDIUM issues detected. PASS requires zero SERIOUS and zero MEDIUM.

**Issues requiring correction (sorted by severity):**

| # | Issue | Severity | Phase | Description |
|---|-------|----------|-------|-------------|
| 1 | Ref 12: Ghost reference (fabricated) | SERIOUS | A | "Martinez, R. (2023)" does not exist. DOI resolves to a different article. No record found in any indexed database. All claims citing this reference are unsupported. |
| 2 | C2: "34% increase" claim distortion | SERIOUS | C/E | Source (Garcia, 2022) says 24% increase in tool-specific satisfaction, not 34% overall satisfaction increase. The 34% refers to a different construct in the source. |
| 3 | Ref 28: Wrong year, incomplete title | MEDIUM | A | European Commission document published 2020, not 2022. Title missing parentheses around date range. |
| 4 | Ref 33: Wrong author initials, year, and pagination | MEDIUM | A | Author is Liu, S. K. (not S.); year should be 2023; volume 36(4), pp. 612-629. |
| 5 | C3: "EUR 2.1 billion" slight overstatement | MINOR | C | Source says ~EUR 2.0 billion across all education sectors, not exclusively higher education. |
| 6 | Ref 19: Wrong year and volume | MINOR | A | Published 2023 (Vol. 48, No. 1), not 2022 (Vol. 47, No. 1). |
| 7 | Ref 41: Missing subtitle | MINOR | A | APA 7.0 requires the book's full subtitle. |
| 8 | B5: Wong & Liu paraphrase overgeneralization | MINOR | B | "Employer trust" is too broad; source specifically measures "initial employer screening decisions." |
| 9 | C6: Outdated statistic presented as current | MINOR | C | 2019 data (11%) presented as current fact (12%) without temporal qualifier. |

---

## Correction Process

### Pipeline Orchestrator Response

```
━━━ MANDATORY CHECKPOINT: Stage 2.5 INTEGRITY ━━━

Verdict: ❌ FAIL

Issues found:
  SERIOUS:  2 (must fix to proceed)
  MEDIUM:   2 (must fix to proceed)
  MINOR:    5 (recommended fix)

SERIOUS issues:
  1. Ghost reference — Ref 12 (Martinez, 2023) does not exist
  2. Data distortion — "34% increase" should be "24% increase"

MEDIUM issues:
  3. Ref 28 — wrong publication year (2020, not 2022)
  4. Ref 33 — wrong author initials, year, and pagination

The pipeline CANNOT proceed to Stage 3 (REVIEW) until
all SERIOUS and MEDIUM issues are resolved.

Options:
  a) "Fix all issues" — I will correct all 9 issues
  b) "Fix critical only" — I will fix the 4 SERIOUS/MEDIUM issues
  c) Review issues one by one — discuss each before fixing
  d) "Pause" — save state and return later
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### User Response

"Fix all issues."

---

### Corrections Applied

#### Issue 1 (SERIOUS): Ghost Reference — Ref 12 Replacement

**Problem**: "Martinez, R. (2023). Artificial intelligence adoption in European universities: A cross-national survey. *Journal of Digital Education*, 15(2), 45-62." does not exist. The DOI resolves to a completely different article.

**Resolution**: The ghost reference supported two claims in Section 2.3 about faculty AI tool adoption rates. A verified replacement source was identified via WebSearch:

| Aspect | Before | After |
|--------|--------|-------|
| Reference | Martinez, R. (2023). Artificial intelligence adoption in European universities: A cross-national survey. *Journal of Digital Education*, 15(2), 45-62. https://doi.org/10.1016/j.jde.2023.02.009 | Zawacki-Richter, O., Marin, V. I., Bond, M., & Gouverneur, F. (2019). Systematic review of research on artificial intelligence applications in higher education: Where are the educators? *International Journal of Educational Technology in Higher Education*, 16(1), Article 39. https://doi.org/10.1186/s41239-019-0171-0 |
| In-text (Section 2.3, para 1) | "Martinez (2023) surveyed 1,200 faculty members across 15 EU countries and found that 68% reported using at least one AI tool in their teaching." | "Zawacki-Richter et al. (2019) conducted a systematic review of 146 AI-in-education studies and found that the vast majority focused on student-facing applications, with faculty adoption and training remaining significantly understudied (p. 27)." |
| In-text (Section 2.3, para 4) | "The cross-national variation in AI adoption (Martinez, 2023) suggests that institutional culture plays a moderating role." | "The gap in research on faculty perspectives (Zawacki-Richter et al., 2019) suggests that institutional culture and educator readiness may be critical moderating factors that remain under-investigated." |
| Verification | DOI invalid, article non-existent | DOI verified (resolves to Springer), 4,800+ citations on Google Scholar |
| Status | -- | **FIXED** |

#### Issue 2 (SERIOUS): Data Distortion — 34% vs 24%

**Problem**: Section 4.1 claims "student satisfaction with digital learning increased by 34%," but the cited source (Garcia, 2022, Table 5) reports a 24% increase in tool-specific satisfaction. The 34% figure refers to "willingness to continue online learning," a distinct construct.

| Aspect | Before | After |
|--------|--------|-------|
| Text (Section 4.1, para 2) | "Student satisfaction with digital learning increased by 34% between 2019 and 2022 (Garcia, 2022)." | "Student satisfaction with specific digital learning tools increased by 24% between 2019 and 2022 (Garcia, 2022, p. 1631, Table 5). Notably, willingness to continue online learning showed a larger increase of 34%, suggesting that familiarity may drive acceptance more than satisfaction per se." |
| Rationale | Single number misattributed to wrong construct | Both figures now correctly attributed to their respective constructs with page reference |
| Status | -- | **FIXED** |

#### Issue 3 (MEDIUM): Ref 28 — European Commission Year and Title

| Aspect | Before | After |
|--------|--------|-------|
| Reference | European Commission. (2022). Digital Education Action Plan 2021-2027. Brussels: Publications Office of the European Union. | European Commission. (2020). *Digital Education Action Plan (2021-2027)*. Publications Office of the European Union. https://ec.europa.eu/education/education-in-the-eu/digital-education-action-plan_en |
| In-text citations | (European Commission, 2022) [3 instances] | (European Commission, 2020) [3 instances] |
| Status | -- | **FIXED** |

#### Issue 4 (MEDIUM): Ref 33 — Wong & Liu Metadata

| Aspect | Before | After |
|--------|--------|-------|
| Reference | Wong, K., & Liu, S. (2024). Blockchain-based micro-credentials in Asian higher education: A multi-site case study. *Higher Education Policy*, 37(1), 89-104. https://doi.org/10.1057/s41307-023-00318-5 | Wong, K., & Liu, S. K. (2023). Blockchain-based micro-credentials in Asian higher education: A multi-site case study. *Higher Education Policy*, 36(4), 612-629. https://doi.org/10.1057/s41307-023-00318-5 |
| In-text citations | (Wong & Liu, 2024) [2 instances] | (Wong & Liu, 2023) [2 instances] |
| Status | -- | **FIXED** |

#### Issue 5 (MINOR): EUR 2.1 Billion Overstatement

| Aspect | Before | After |
|--------|--------|-------|
| Text (Section 1, para 2) | "The EU invested EUR 2.1 billion in digital infrastructure for higher education." | "The EU allocated approximately EUR 2.0 billion to digital education initiatives across all sectors through the Erasmus+ programme for 2021-2027 (European Commission, 2020)." |
| Rationale | Corrected amount, removed "higher education" exclusivity claim, added programme name for precision |
| Status | -- | **FIXED** |

#### Issue 6 (MINOR): Ref 19 — Selwyn Year and Volume

| Aspect | Before | After |
|--------|--------|-------|
| Reference | Selwyn, N. (2022). Digital technologies and the automation of education. *Learning, Media and Technology*, 47(1), 1-5. | Selwyn, N. (2023). Digital technologies and the automation of education. *Learning, Media and Technology*, 48(1), 1-5. https://doi.org/10.1080/17439884.2023.2141509 |
| In-text citations | (Selwyn, 2022) [1 instance] | (Selwyn, 2023) [1 instance] |
| Status | -- | **FIXED** |

#### Issue 7 (MINOR): Ref 41 — Missing Subtitle

| Aspect | Before | After |
|--------|--------|-------|
| Reference | Organisation for Economic Co-operation and Development. (2021). *OECD Digital Education Outlook 2021*. OECD Publishing. | Organisation for Economic Co-operation and Development. (2021). *OECD Digital Education Outlook 2021: Pushing the frontiers with artificial intelligence, blockchain and robots*. OECD Publishing. https://doi.org/10.1787/589b283f-en |
| Status | -- | **FIXED** |

#### Issue 8 (MINOR): Wong & Liu Paraphrase Overgeneralization

| Aspect | Before | After |
|--------|--------|-------|
| Text (Section 2.4, para 1) | "Wong and Liu (2024) demonstrated that blockchain micro-credentials improved employer trust in non-traditional qualifications by 41%." | "Wong and Liu (2023) found that blockchain-verified micro-credentials increased the likelihood of favorable initial employer screening decisions by 41% compared to unverified digital badges (p. 621, Table 3)." |
| Rationale | "Employer trust" was overly broad; corrected to the specific construct measured in the source |
| Status | -- | **FIXED** |

#### Issue 9 (MINOR): Outdated CDO Statistic

| Aspect | Before | After |
|--------|--------|-------|
| Text (Section 5, para 2) | "Only 12% of European universities have a dedicated Chief Digital Officer." | "As of 2019, approximately 11% of surveyed European institutions reported having a Chief Digital Officer or equivalent role (Rampelt et al., 2019), a figure that may have since changed given accelerated digital transformation efforts." |
| Rationale | Added temporal qualifier and acknowledged potential data staleness |
| Status | -- | **FIXED** |

---

## Stage 2.5: Re-Verification (Round 2)

```
Stage 2.5 Re-verification -- Round 2 (focused on 9 corrected items)

integrity_verification_agent re-checking corrected items only...
```

### integrity_verification_agent Re-Verification Output

| # | Original Issue | Correction Applied | Re-verification | Status |
|---|---------------|-------------------|-----------------|--------|
| 1 | Ghost reference (Ref 12: Martinez, 2023) | Replaced with Zawacki-Richter et al. (2019). Both in-text citations rewritten to match new source content. | DOI verified (Springer). Article confirmed: 146 studies reviewed, educator-focused gap identified. In-text paraphrases accurately reflect source. | PASS |
| 2 | "34% increase" data distortion | Corrected to "24% increase" for tool satisfaction; added 34% for willingness construct with proper attribution and page reference. | Garcia (2022), Table 5, p. 1631 confirmed: 24% tool satisfaction, 34% willingness. Paper now correctly attributes both figures. | PASS |
| 3 | EC wrong year/title (Ref 28) | Changed year to 2020, added parentheses to title, added URL. | EC official page confirms September 2020 publication date. Title matches official listing. | PASS |
| 4 | Wong & Liu wrong metadata (Ref 33) | Changed to Liu, S. K.; year 2023; Vol. 36(4), pp. 612-629. | DOI resolves to correct metadata. Publisher page confirms all fields. | PASS |
| 5 | EUR 2.1B overstatement | Changed to "approximately EUR 2.0 billion" with sector and programme qualifier. | Erasmus+ allocation documents confirm ~EUR 2.0B for digital education across all sectors. | PASS |
| 6 | Selwyn wrong year (Ref 19) | Changed to 2023, Vol. 48(1). Added DOI. | DOI resolves correctly. Publisher confirms 2023 publication. | PASS |
| 7 | OECD missing subtitle (Ref 41) | Added full subtitle and DOI. | DOI resolves to OECD iLibrary. Full title matches. | PASS |
| 8 | Wong & Liu overgeneralization | Narrowed to "initial employer screening decisions" with page/table reference. | Matches source Table 3, p. 621. Paraphrase is now faithful. | PASS |
| 9 | Outdated CDO statistic | Added temporal qualifier ("As of 2019") and acknowledged potential staleness. | Rampelt et al. (2019), p. 28 confirms "approximately 11%." Temporal framing is appropriate. | PASS |

### Re-Verification Verdict: PASS

```
Integrity Verification Report — Round 2

Verification Mode: Pre-Review (Mode 1), Re-verification of corrected items
Verdict: ✅ PASS

Verification Summary:
| Category               | Total | Passed | Issues |
|------------------------|-------|--------|--------|
| Reference Existence    | 45    | 45     | 0      |
| Bibliographic Accuracy | 45    | 45     | 0      |
| Ghost Citations        | --    | --     | 0 orphan / 0 dangling |
| Citation Context       | 14    | 14     | 0      |
| Data Accuracy          | 18    | 18     | 0      |
| Internal Consistency   | --    | Pass   | 0      |
| Originality (D1)       | 19    | 19     | 0 CLOSE_MATCH / 0 VERBATIM |
| Self-Plagiarism (D2)   | N/A   | N/A    | Author name not provided |

Issue Summary:
  SERIOUS:  0 (was 2, both resolved)
  MEDIUM:   0 (was 2, both resolved)
  MINOR:    0 (was 5, all resolved)

All 9 issues from Round 1 have been verified as resolved.
Paper is cleared for peer review.
```

---

## Pipeline Continues: Stage 2.5 --> Stage 3

```
━━━ MANDATORY CHECKPOINT: Stage 2.5 INTEGRITY ━━━

Verdict: ✅ PASS (Round 2, after corrections)

Integrity verification complete:
  - Round 1: FAIL (2 SERIOUS, 2 MEDIUM, 5 MINOR)
  - Corrections applied: 9/9
  - Round 2: PASS (all issues resolved)

Corrections summary:
  - 1 ghost reference removed and replaced with verified source
  - 1 data distortion corrected (34% → 24% with proper attribution)
  - 3 bibliographic metadata errors fixed
  - 4 precision/recency improvements applied

The paper is now cleared for peer review.

Next: Stage 3 (REVIEW) — Full 5-reviewer review
  (EIC + R1 Methodology + R2 Domain + R3 Perspective + Devil's Advocate)

Continue?

Progress: [v]Research -> [v]Writing -> [v]Integrity -> [..]Review -> [ ]Revision -> [ ]Finalization
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

**User**: Continue!

---

## Key Takeaways

### 1. Ghost References Are the Most Dangerous Integrity Failure

Reference 12 (Martinez, 2023) looked entirely plausible — a believable author name, a real-sounding journal, a formatted DOI. But the DOI resolved to a completely different article, and no record of this publication existed in any database. This is the hallmark of a fabricated reference, and it is the primary reason Stage 2.5 exists. Without integrity verification, this ghost reference would have entered peer review and potentially publication.

### 2. Data Distortions Can Be Subtle and Consequential

The "34% vs 24%" error (Issue 2) was not a careless typo — the 34% figure genuinely appeared in the cited source, but in a different column measuring a different construct. This type of construct confusion is common in academic writing and can survive multiple rounds of human review. The integrity verification agent caught it by cross-referencing the exact table and column in the source.

### 3. Corrections Must Be Verifiable, Not Just Plausible

Each correction includes a verification trail: DOI resolution, page numbers, table references, and publisher confirmations. The replacement reference for the ghost citation (Zawacki-Richter et al., 2019) was selected not just because it covered a similar topic, but because it has 4,800+ citations and is published by Springer with a valid DOI — maximizing verifiability.

### 4. Re-Verification Is Focused, Not Redundant

Round 2 only re-checks the 9 corrected items, not the entire paper. The 41 references that passed in Round 1 are not re-verified. This keeps the re-verification efficient while ensuring that corrections actually resolve the original issues (and do not introduce new ones).

### 5. The Integrity Gate Is Non-Negotiable

The pipeline cannot proceed to Stage 3 (REVIEW) until the integrity check returns PASS. This is a MANDATORY checkpoint — the user cannot skip it, override it, or request an exception. The maximum retry is 3 rounds; after that, unverifiable items are listed and the user must make an explicit decision about whether to proceed with acknowledged limitations.

### 6. MINOR Issues Are Worth Fixing Too

While only SERIOUS and MEDIUM issues block the pipeline, fixing MINOR issues (like the missing subtitle in Ref 41 or the temporal qualifier for the CDO statistic) strengthens the paper before it reaches reviewers. Reviewers will notice these small inaccuracies, and fixing them preemptively removes easy targets for criticism.
