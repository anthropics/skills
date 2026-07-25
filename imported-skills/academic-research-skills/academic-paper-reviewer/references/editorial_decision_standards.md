# Editorial Decision Standards — Criteria for Editorial Decision Making

This document defines the explicit criteria for Accept / Minor Revision / Major Revision / Reject decisions, for use by `eic_agent` and `editorial_synthesizer_agent`.

---

## 1. Decision Categories

### Accept

**Definition**: The paper can be published without further review.

**Criteria**:
- Average score across all universal dimensions >= 4.0
- No dimension scores below 3.0
- At least 3/4 reviewers recommend Accept or Minor Revision
- No unresolved major academic issues

**Conditions**:
- May include minor copyediting suggestions
- May require final formatting adjustments
- Does not need to be sent for review again

**Typical scenarios**:
- Paper has undergone multiple revision rounds, all issues resolved
- Rare first-pass acceptance (< 5% of submissions at top-tier journals)

---

### Minor Revision

**Definition**: The paper is fundamentally acceptable and can be published after limited modifications; typically does not need to be sent for review again after revision.

**Criteria**:
- Average score across all universal dimensions >= 3.5
- No dimension scores below 2.5
- At least 3/4 reviewers recommend Accept or Minor Revision
- Issues can be resolved within 2-4 weeks
- Modifications do not involve restructuring core arguments or methods

**Typical revision items**:
- Supplementing a small number of references
- Clarifying certain methodology description details
- Improving clarity of argumentation
- Correcting citation format
- Adding discussion of limitations
- Adjusting conclusion wording (avoiding overclaiming)

**Response requirements**:
- Authors must respond to reviewer comments item by item
- After revision, reviewed by EIC (usually not sent for external review again)
- Revision deadline: 2-4 weeks

---

### Major Revision

**Definition**: The paper has potential but has significant issues, requiring substantial revision followed by re-review.

**Criteria**:
- Universal dimension average score between 2.5-3.4
- Some dimensions may score below 2.5 (but not fatal)
- At least 2/4 reviewers recommend Major Revision or better
- Issues are serious but fixable (not fundamental design flaws)
- Revision requires 6-8 weeks of work

**Typical revision items**:
- Re-analyzing data (additional analysis or correcting errors)
- Substantially rewriting literature review (missing key references)
- Supplementing additional data collection
- Reorganizing paper structure
- Correcting significant methodological flaws
- Strengthening theoretical framework application
- Adding robustness checks

**Response requirements**:
- Authors must write a detailed point-by-point response letter
- After revision, sent for re-review (may go back to original reviewers or new reviewers)
- Revision deadline: 6-8 weeks
- Typically a maximum of 2 rounds of Major Revision allowed

---

### Reject

**Definition**: The paper is not suitable for publication in this journal, even with revision.

**Criteria (meeting any one may trigger Reject consideration)**:
- Universal dimension average score < 2.5
- Any core dimension (methodology, evidence) = 1
- At least 3/4 reviewers recommend Reject
- Fundamental unfixable issues exist

**Reject subtypes**:

| Subtype | Description | Suggestion |
|---------|-------------|-----------|
| **Reject — Out of Scope** | Topic not within journal scope | Recommend more suitable journals |
| **Reject — Fundamental Flaw** | Fatal flaw in research design | Suggest redesigning the research |
| **Reject — Insufficient Contribution** | Lacks originality or incremental contribution | Suggest how to strengthen contribution |
| **Reject — Premature** | Paper not yet mature enough | Suggest specific improvement directions |
| **Reject — Resubmit Encouraged** | Has potential but needs fundamental restructuring | Provide detailed restructuring suggestions |

**Even with Reject, must**:
- Affirm the paper's merits
- Provide specific improvement suggestions
- Recommend more suitable journals (if it's a scope issue)
- Maintain professional, respectful tone

---

## 2. Decision Matrix

### Decision Matrix Based on Reviewer Recommendations

| EIC | R1 | R2 | R3 | -> Recommended Decision |
|-----|----|----|-----|----------------------|
| Accept | Accept | Accept | Accept | **Accept** |
| Accept | Accept | Accept | Minor | **Accept** (with suggestions) |
| Accept | Accept | Minor | Minor | **Minor Revision** |
| Accept | Minor | Minor | Minor | **Minor Revision** |
| Minor | Minor | Minor | Minor | **Minor Revision** |
| Minor | Minor | Minor | Major | **Minor-to-Major** (depends on specific issues) |
| Minor | Minor | Major | Major | **Major Revision** |
| Minor | Major | Major | Major | **Major Revision** |
| Major | Major | Major | Major | **Major Revision** |
| Major | Major | Major | Reject | **Major Revision** (last chance) |
| Major | Major | Reject | Reject | **Reject** (resubmit encouraged) |
| Major | Reject | Reject | Reject | **Reject** |
| Reject | Reject | Reject | Reject | **Reject** |

### Special Situation Handling

**Split Decision (evenly divided)**:
- Example: Accept + Accept + Reject + Reject
- EIC (or synthesizer) needs to deeply analyze the cause of disagreement
- Lean toward conservative strategy: Major Revision, requiring the author to respond to the Reject side's comments
- May consider inviting a fifth reviewer

**One Outlier (one unusual opinion)**:
- Example: Minor + Minor + Minor + Reject
- Carefully examine the Reject rationale
- If the rationale is valid and others missed it, escalate to Major Revision
- If the rationale is insufficient, maintain Minor Revision but mention the opinion in the Decision Letter

---

## 3. Decision Confidence Calibration

### Impact of Reviewer Confidence Score

| Confidence | Impact on Decision |
|-----------|-------------------|
| 5 (Very High) | This reviewer's opinion carries the highest weight |
| 4 (High) | Standard weight |
| 3 (Medium) | Standard weight, but reduced in case of disagreement |
| 2 (Low) | For reference only, not used as a decisive opinion |
| 1 (Very Low) | Ignore this reviewer's recommendation (but retain specific comments) |

### Cross-Dimension Severity Assessment

| Situation | Severity | Handling |
|-----------|----------|---------|
| Methodology has fatal flaw (R1 score = 1) | Critical | Even if other dimensions are excellent, lean toward Reject |
| Major literature review omission (R2 score = 2) | Serious | Major Revision, require supplementation |
| Cross-disciplinary perspective overlooked (R3 score = 2) | Moderate | Minor/Major, depends on other dimensions |
| Poor writing quality (score = 2) | Minor | Does not affect academic decision, but require language revision |

---

## 4. Revision Round Policy

### Standard Policy

| Round | Expectation | Handling |
|-------|-------------|---------|
| R1 (First revision) | Respond to all reviewer comments | Send for re-review or EIC review |
| R2 (Second revision) | Respond to residual issues | Usually EIC makes final decision |
| R3 (Third revision) | Very rare, usually only handling formatting | EIC makes final decision |

### Upgrade/Downgrade Rules

- Minor Revision with incomplete revisions -> May escalate to Major Revision
- Major Revision with excellent revisions -> May downgrade to Minor Revision or Accept
- Major Revision with insufficient revisions -> May Reject (infinite revision cycles are not encouraged)
- Beyond 2 rounds of Major Revision -> Strongly recommend Accept or Reject, no further extension

---

## 5. Professional Ethics of Editorial Review

### Reviewer Ethics

1. **Confidentiality**: The review process and paper content are confidential
2. **Conflict of interest**: Recuse if there is a collaborative or competitive relationship with the author
3. **Timeliness**: Complete the review within the committed timeframe
4. **Constructiveness**: Even when recommending Reject, provide constructive feedback
5. **Impartiality**: No bias based on author's gender, race, institution, or nationality
6. **No plagiarism**: Do not use unpublished ideas seen during review
7. **Appropriate language**: Avoid personal attacks, sarcasm, or demeaning language

### Editor Ethics

1. **Fair decision**: Based on academic quality, not influenced by external pressure
2. **Transparent process**: Decision letter must clearly explain the rationale
3. **Reasonable deadlines**: Give authors sufficient revision time
4. **Appeal channel**: Authors have the right to respond to or challenge review comments
5. **Consistent standards**: Papers of similar quality should receive similar decisions

### Ethical Considerations for Special Situations

| Situation | Ethical Handling |
|-----------|-----------------|
| Author is your student/colleague | Must recuse or disclose the relationship |
| Paper's viewpoint is opposite to yours | Evaluate argument quality, not correctness of position |
| Paper uses your theory but misunderstands it | May point it out but cannot require citation of your own work |
| Suspected data fabrication | Report to EIC; journal initiates investigation procedure |
| Paper is similar to your ongoing research | Disclose potential conflict of interest |
