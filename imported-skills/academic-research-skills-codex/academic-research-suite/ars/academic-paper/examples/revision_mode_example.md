---
scenario: Revising a paper after receiving peer review comments
mode: revision
agents_used:
  - formatter_agent
  - citation_compliance_agent
  - peer_reviewer_agent
input: Original peer review comments (3 major + 4 minor)
output: Revision comparison table + Response to Reviewers letter
---

# Revision Mode Example: Responding to Peer Review Comments

## Scenario

The user has a completed paper titled "The Impact of Micro-Credential Certification on Employability of Vocational Education Students in Taiwan," which has received peer review comments from a journal (3 major + 4 minor). The user employs academic-paper's revision mode for systematic revision. This example demonstrates the complete workflow from comment parsing, citation correction, review verification, to the Response to Reviewers letter.

---

## Original Peer Review Comments

### Reviewer 1

**Major Comments:**

**M1.** There are serious concerns about the research methodology. The paper uses questionnaire surveys to collect students' self-assessed employability but does not employ any objective indicators (such as actual employment rates, starting salaries, or employer satisfaction) for triangulation. Relying solely on self-assessment to measure "employability" has insufficient validity. It is recommended to supplement with at least one objective indicator or explicitly discuss this methodological limitation.

**M2.** The literature review lacks systematicity. Of the 23 references cited in Chapter 2, more than half are publications from before 2018, and the review does not cover important recent international studies on micro-credentials from the past two years (2024-2025), particularly the latest reports from UNESCO (2024) and the European Commission (2024). It is recommended to supplement with literature from the past three years and update the literature matrix.

**M3.** The statistical analysis is incomplete. The regression model in Table 4 reports only R-squared and beta coefficients, lacking collinearity diagnostics (VIF), residual analysis, and effect sizes. Additionally, the rationale for selecting control variables is unclear — why was "family income" controlled but not "prior work experience"?

**Minor Comments:**

**m1.** The third sentence of the Chinese abstract — "This study found that micro-credential certification has a significant positive impact on student employability" — is too vague and does not mention the magnitude of the effect size.

**m2.** Reference formatting is inconsistent: some Chinese references use full-width parentheses while others use half-width parentheses. Citation #15 is missing its DOI.

**m3.** The axis labels in Figure 2 have font sizes that are too small; it is recommended to enlarge them to 10pt or above. Figure 3 is missing a caption.

**m4.** The last paragraph on page 47 contains "as shown in Table X," which appears to be a typesetting omission.

---

### Reviewer 2

**Major Comments:**

(No additional major comments, but the reviewer agrees with Reviewer 1's M1 and M2.)

**Minor Comments:**

(Agrees with Reviewer 1's minor comments, and adds:)

**m5 (R2).** It is recommended to add a clearer research gap statement in the Introduction. The transition from problem description to research purpose is currently too abrupt.

**m6 (R2).** The "policy recommendations" paragraph in the Discussion chapter is too brief — it lists only three recommendations without supporting arguments. It is recommended to expand or downgrade this section to "future research directions."

**m7 (R2).** It is recommended to add a research ethics statement explaining the IRB review status and informed consent procedures.

---

## formatter_agent Parses Revision Comments

### Revision Comment Classification

**Parsing Result:** 3 Major + 7 Minor, totaling 10 revision items.

| No. | Type | Affected Section | Revision Scope | Estimated Workload |
|-----|------|-----------------|----------------|-------------------|
| M1 | Major | Methodology, Discussion | Methodological limitation discussion + possible data supplement | High |
| M2 | Major | Literature Review | Supplement literature + update literature matrix | Medium-High |
| M3 | Major | Results | Add statistical diagnostics + effect sizes | Medium |
| m1 | Minor | Abstract | Revise abstract wording | Low |
| m2 | Minor | References | Unify formatting + add DOI | Low |
| m3 | Minor | Figures | Fix figures and tables | Low |
| m4 | Minor | Body text | Fix typesetting | Low |
| m5 | Minor | Introduction | Add research gap statement | Low-Medium |
| m6 | Minor | Discussion | Expand policy recommendations discussion | Medium |
| m7 | Minor | Methodology | Add ethics statement | Low |

### Recommended Revision Strategy

The formatter_agent recommends the following revision order:

1. Address M1 (methodology) first, as it affects the revision direction of Discussion and Limitations
2. Then address M3 (statistical analysis), as the supplementary statistical results may affect the limitation discussion in M1
3. Then address M2 (literature review), as supplemented literature may require cascading updates to the Discussion
4. Finally, batch-process all minor comments

---

## citation_compliance_agent Corrects Citation Issues

### Citation Audit Report

**Audit Scope:** Full-text citation formatting (APA 7.0 Chinese citation standards)

**Issues Found:**

| Issue | Count | Severity |
|-------|-------|----------|
| Inconsistent parenthesis format (full-width/half-width) | 7 instances | Medium |
| Missing DOI | 3 instances | High |
| Inconsistent year format | 2 instances | Low |
| In-text citation / reference list mismatch | 1 instance | High |
| Missing English translated titles for Chinese references | 4 instances | Medium |

### Specific Corrections

**Correction 1: Unify parenthesis format (addressing m2)**

Before correction:
```
(Wang & Chen, 2023) noted in their study...
Lin, M.-D. (2022)'s survey showed...
According to UNESCO (2024) report...
```

After correction:
```
Wang and Chen (2023) noted in their study...
Lin (2022)'s survey showed...
According to the UNESCO (2024) report...
```

Rule: Chinese papers uniformly use full-width parentheses; when the author is in the sentence, use "Author (Year)" format.

**Correction 2: Add missing DOIs (addressing m2)**

Before correction:
```
Huang, C.-W. (2021). Implications of micro-credit systems for technical and vocational
    education. Journal of Technical and Vocational Education, 15(2), 45-68.
```

After correction:
```
Huang, C.-W. (2021). Implications of micro-credit systems for technical and vocational
    education. Journal of Technical and Vocational Education, 15(2), 45-68.
    https://doi.org/10.6235/TVE.202106_15(2).0003
```

**Correction 3: In-text citation / reference list mismatch**

Found that the in-text citation on page 23 reads "Chen et al.（2023）," but the reference list entry is "Chen, Y.-L., & Wang, S.-T.（2023）," which has only two authors and should not use "et al."

Before correction:
```
Chen et al.（2023）found that micro-credential certification helps...
```

After correction:
```
Chen and Wang（2023）found that micro-credential certification helps...
```

**Correction 4: Add English translated titles for Chinese references**

Per APA 7.0 standards, non-English references should include an English translated title in the reference list.

Before correction:
```
Ministry of Education. (2024). Technical and vocational education policy guidelines.
    Ministry of Education.
```

After correction:
```
Ministry of Education. (2024). Technical and vocational education policy guidelines
    [Technical and vocational education policy guidelines]. Ministry of Education.
```

### New References Added (addressing M2)

In conjunction with M2's literature update requirement, the citation_compliance_agent verifies format compliance of newly added references:

```
UNESCO. (2024). Towards a common framework for micro-credentials:
    Global perspectives and challenges. UNESCO Publishing.
    https://doi.org/10.xxxx/xxxxx

European Commission. (2024). European approach to micro-credentials:
    Implementation report 2022-2024. Publications Office of the
    European Union. https://doi.org/10.xxxx/xxxxx

Kato, S., & Gallagher, S. (2024). The global rise of micro-credentials:
    Patterns, challenges, and policy implications. Higher Education
    Policy, 37(2), 215-238. https://doi.org/10.xxxx/xxxxx

Wheelahan, L., & Moodie, G. (2024). Micro-credentials: A critique
    of quality assurance and credentialism. Journal of Education
    and Work, 37(1), 45-62. https://doi.org/10.xxxx/xxxxx
```

Format audit result: All 4 newly added references comply with APA 7.0 standards.

---

## peer_reviewer_agent Reviews the Revised Version

### Revision Adequacy Assessment

| No. | Original Comment | Revision Adequate? | Remarks |
|-----|-----------------|:------------------:|---------|
| M1 | Methodological validity insufficient | Partially adequate | Methodological limitation discussion has been added, but could further explain the psychometric properties of the self-report scale |
| M2 | Literature outdated | Adequate | 8 new references from 2023-2025 added, literature matrix updated |
| M3 | Statistical analysis incomplete | Adequate | VIF (max 2.37), Cook's Distance, and Cohen's f-squared have been added |
| m1 | Abstract too vague | Adequate | Revised to include precise description with effect sizes |
| m2 | Citation formatting inconsistent | Adequate | Comprehensively unified, DOIs added |
| m3 | Figure issues | Adequate | Font sizes adjusted, captions added |
| m4 | "Table X" typesetting omission | Adequate | Corrected to "Table 6" |
| m5 | Research gap unclear | Adequate | 150-word research gap paragraph added |
| m6 | Policy recommendations too brief | Adequate | Expanded to 400 words with supporting arguments |
| m7 | Missing ethics statement | Adequate | IRB number and informed consent description added |

### Post-Revision Five-Dimension Scores

| Dimension | Before Revision | After Revision | Change |
|-----------|----------------|----------------|--------|
| Originality (20%) | 3.5 | 3.5 | No change |
| Methodological Rigor (25%) | 2.5 | 3.5 | +1.0 |
| Evidence Sufficiency (25%) | 3.0 | 3.8 | +0.8 |
| Argument Coherence (15%) | 3.5 | 4.0 | +0.5 |
| Writing Quality (15%) | 4.0 | 4.2 | +0.2 |
| **Weighted Total** | **3.24** | **3.78** | **+0.54** |

### Revision Verdict

**Verdict: ACCEPT with Minor Revision**

The paper moved from Major Revision (3.24) before revision to the Minor Revision/Accept boundary (3.78) after revision. The remaining 1 recommendation (psychometric properties explanation for M1) can be addressed during the proofing stage and does not affect the acceptance decision.

---

## Revision Results — Revision Comparison Table

### Major Revisions

| Reviewer Comment | Before Revision | After Revision | Pages |
|------------------|----------------|----------------|-------|
| M1: Methodological validity | No discussion of self-report scale limitations | Added a new "3.6 Methodological Limitations" section (approximately 350 words), discussing the validity limitations of self-report scales, social desirability bias risk, and citing Hora et al. (2024) to support the reasonableness of self-assessed employability scales under specific conditions. Added 200 words to the Limitations paragraph in the Discussion, stating that future research should incorporate objective employment data for triangulation. | pp. 18-19, 38 |
| M2: Literature outdated | 23 references, 12 from before 2018 | Added 8 references from 2023-2025 (including UNESCO 2024, European Commission 2024), removed 3 outdated non-core references. Total references increased to 28, with post-2020 references rising from 48% to 68%. Added an "International Trends" thematic row to the literature matrix table. | pp. 8-14 |
| M3: Statistical analysis | Only R-squared and beta reported | Added Table 4a (collinearity diagnostics: all VIF values between 1.12-2.37, all below the threshold of 5), Table 4b (residual analysis: Cook's Distance maximum 0.087, no influential outliers). Added Cohen's f-squared = 0.18 (medium effect size). Added a paragraph on page 17 explaining the control variable selection rationale: because all subjects were enrolled students, prior formal work experience had too little variance to serve as a control variable. | pp. 22-24 |

### Minor Revisions

| Reviewer Comment | Before Revision | After Revision | Pages |
|------------------|----------------|----------------|-------|
| m1: Abstract effect size | "This study found that micro-credential certification has a significant positive impact on student employability" | "This study found that micro-credential certification has a moderate positive impact on student self-assessed employability (beta = .34, p < .001, f-squared = .18), with the most significant effect observed in the 'workplace practical skills' dimension" | p. ii |
| m2: Citation formatting | Mixed full-width/half-width parentheses, 3 missing DOIs | Uniformly using full-width parentheses, all DOIs added, et al. misuse corrected | Throughout |
| m3: Figures | Axis label font 8pt, Figure 3 missing caption | All figure fonts adjusted to 11pt, Figure 3 caption added: "Figure 3. Comparison of predictive power of different micro-credential types across five employability dimensions" | pp. 25, 27 |
| m4: Typesetting omission | "as shown in Table X" | "as shown in Table 6" | p. 47 |
| m5: Research gap | Introduction jumped directly from problem description to research purpose | Added a research gap paragraph in Section 1.3: "Although international literature has accumulated preliminary evidence on micro-credential certification, the vast majority of studies focus on Western higher education contexts. The uniqueness of Taiwan's vocational education system — including industry-academia cooperation mechanisms, certification-oriented curriculum design, and the dual-track training structure — limits the transferability of international research findings. Currently, local Taiwanese research consists mostly of policy advocacy or theoretical discourse, lacking empirical studies that validate the actual effects of micro-credential certification with quantitative data." | p. 5 |
| m6: Policy recommendations | Three policy recommendations, each approximately 50 words | Expanded to three policy recommendations, each approximately 130 words, with specific supporting arguments. For example, Recommendation 1 was revised to: "It is recommended that the Ministry of Education amend the 'Regulations for Industry-Academia Cooperation at Postsecondary Institutions' to incorporate micro-credential certification into industry-academia cooperation performance indicators. This study found that the effect size of micro-credential certification on the 'workplace practical skills' dimension (f-squared = .22) is higher than for other dimensions, indicating that certification designed in connection with industry can more effectively enhance student employability. Therefore, encouraging vocational institutions to co-design micro-credential courses with industry partners will help strengthen the employment-oriented positioning of vocational education." | pp. 39-40 |
| m7: Ethics statement | None | Added a "Research Ethics" paragraph: "This study was approved by the Institutional Review Board of National OO University of Science and Technology (IRB No.: NTUST-REC-2024-037). All participants signed written informed consent forms prior to completing the survey, which specified the research purpose, data usage methods, anonymity safeguards, and the right to withdraw at any time." | p. 16 |

---

## Response to Reviewers

---

**Manuscript No.:** TVEJ-2025-0142

**Manuscript Title:** The Impact of Micro-Credential Certification on Employability of Vocational Education Students in Taiwan: A Case Study of Four Universities of Science and Technology in Northern Taiwan

**Revision Date:** 2026-02-26

---

Dear Editor and Reviewers:

Thank you both for your thorough and constructive review comments. We respond to each item below. All revisions are marked in blue in the revised manuscript.

---

### Response to Reviewer 1

**M1: Methodological Validity**

Thank you for raising this important issue. We fully agree that measuring employability solely through self-report scales has validity limitations. In response to this comment, we have made the following revisions:

1. Added a "Methodological Limitations" section (Section 3.6, approximately 350 words) that explicitly discusses the potential biases of self-report scales, including social desirability effects and cognitive discrepancies.
2. Cited Hora et al. (2024), who found that self-assessed employability scales, after controlling for social desirability bias, still maintain a moderate correlation with employer assessments (r = .52), supporting their reasonableness as a preliminary exploratory research tool.
3. Expanded the Limitations paragraph in the Discussion by 200 words, explicitly recommending that future research collect actual employment data from one year after graduation for triangulation.

Due to constraints in our research timeline and IRB approval scope, we were unable to supplement objective employment data in this study, but we have transparently disclosed this limitation.

> See revised manuscript pp. 18-19, 38

**M2: Literature Outdated**

Thank you for this reminder. We have substantially updated the literature review:

1. Added 8 references from 2023-2025, including the UNESCO (2024) report and European Commission (2024) implementation report as recommended by the reviewer.
2. Removed 3 pre-2017 references with lower relevance to the research questions.
3. Updated the literature matrix table (Table 2), adding an "International Trends" thematic row.
4. The literature recency indicator improved from 48% (post-2020) to 68%.

> See revised manuscript pp. 8-14, Table 2

**M3: Incomplete Statistical Analysis**

Thank you for requesting more complete statistical reporting. We have added:

1. Table 4a: Collinearity diagnostic results — all independent variable VIF values range from 1.12 to 2.37, all below the commonly used threshold of 5.0, indicating that collinearity is not a concern.
2. Table 4b: Residual analysis, including Cook's Distance (maximum 0.087) and standardized residual distribution, confirming no influential outliers.
3. Effect size: Cohen's f-squared = 0.18, a medium effect size.
4. An explanation of control variable selection rationale in Section 3.4. Regarding why "prior work experience" was not controlled: since our sample consists of enrolled students, only 11.3% of respondents had more than six months of formal work experience, resulting in too little variance to serve as a control variable.

> See revised manuscript pp. 17, 22-24

**m1-m4:** All minor comments have been addressed individually. See the revision comparison table for details.

---

### Response to Reviewer 2

**m5: Research Gap Statement**

Thank you for this suggestion. We have added an approximately 150-word research gap statement in Introduction Section 1.3, explicitly noting that the uniqueness of Taiwan's vocational education system limits the direct applicability of international research, and that local empirical studies remain insufficient.

> See revised manuscript p. 5

**m6: Expanded Policy Recommendations**

We have expanded the policy recommendations paragraph in the Discussion from approximately 150 words to approximately 400 words. Each recommendation now includes: (a) a specific policy revision recommendation, (b) supporting evidence from this study's data, and (c) expected effects and possible limitations.

> See revised manuscript pp. 39-40

**m7: Research Ethics Statement**

A research ethics paragraph has been added after Section 3.1, including the IRB approval number and a description of the informed consent procedure.

> See revised manuscript p. 16

---

We believe that the above revisions have fully addressed all comments from both reviewers. If further modifications are needed, we are happy to comply.

Sincerely,

Corresponding Author: [Author Name]
Contact Email: [email]
Revision Date: 2026-02-26
