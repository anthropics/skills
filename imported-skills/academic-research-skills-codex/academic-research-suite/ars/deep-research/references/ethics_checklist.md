# Research Ethics Checklist — AI-Assisted Research

## Purpose
Comprehensive ethics checklist for AI-assisted academic research. Used by the ethics_review_agent.

## 1. AI Disclosure

### Mandatory Disclosure Elements
- [ ] AI tools used are named (e.g., "Claude," "GPT-4," "Gemini")
- [ ] Scope of AI involvement specified:
  - [ ] Literature search assistance
  - [ ] Source screening
  - [ ] Evidence synthesis
  - [ ] Draft writing
  - [ ] Editing/revision
  - [ ] Data analysis
  - [ ] Translation
- [ ] Human oversight described (who reviewed what, at which stages)
- [ ] AI limitations acknowledged (potential hallucination, knowledge cutoff, etc.)
- [ ] AI version/date noted (for reproducibility)

### Disclosure Statement Template
```
AI Disclosure: This research was conducted with assistance from [AI Tool Name]
(version/date). AI was used for [specific tasks]. All findings were verified
against cited sources by [human role]. The research team maintains full
responsibility for the accuracy and interpretation of all content.
```

### Where to Place Disclosure
- In the methodology section (detailed)
- In the abstract or author note (brief)
- In footnotes for specific AI-generated analyses

## 2. Attribution Integrity

### Citation Ethics
- [ ] Every factual claim has at least one supporting citation
- [ ] No fabricated or hallucinated references
  - Verification: Spot-check minimum 20% of references for existence
  - Cross-check DOIs, publication years, author names
- [ ] Paraphrasing is genuine (not just rearranging words)
- [ ] Direct quotes are exact and attributed
- [ ] Ideas are attributed to original authors, not intermediary sources
- [ ] Self-citation is proportionate (not excessive or exclusionary)

### AI-Specific Attribution Risks
| Risk | Description | Mitigation |
|------|-------------|-----------|
| Hallucinated references | AI generates plausible but non-existent citations | Verify every reference against database |
| Merged citations | AI combines details from multiple sources | Cross-check each citation element |
| Incorrect authors | AI assigns wrong authors to works | Verify author names against actual publications |
| Wrong year | AI uses incorrect publication year | Cross-check against database records |
| Ghost citations | References listed but never cited in text | Audit reference list against in-text citations |

## 3. Dual-Use Assessment

**Screen on concrete specifics, never on subject matter.** A sensitive, political, or institution-critical *topic* is not a dual-use trigger. Public-interest research — documenting institutional abuses, exposing surveillance practices, holding power to account — is expected to address harmful subject matter and must not be flagged for the topic alone. A finding triggers dual-use only when the work itself supplies **specific operational detail** that materially lowers the barrier to harm. Studying surveillance is fine; shipping a step-by-step deployment recipe is the trigger.

### Screening Questions
Each asks whether the **content of this work**, not its topic, supplies the specific:
1. Does the work provide concrete operational detail that would let a reader **carry out** harm against individuals or communities (beyond describing that the harm exists)?
2. Does it disclose a **specific, currently-exploitable** vulnerability together with enough detail to exploit it (vs. naming that vulnerabilities exist)?
3. Does it provide a **usable method** to build surveillance or control mechanisms (vs. analyzing or critiquing them)?
4. Does it contain **weaponizable specifics** — a recipe, design, or procedure — rather than discussion of weaponization risk?
5. Does it supply a **concrete means** to discriminate against a group (vs. documenting that discrimination occurs)?

If the answer rests on the topic being sensitive rather than on specific enabling detail in the text, the level is None.

### Risk Levels and Responses

This assessment is **advisory** — it routes to a Responsible Use Statement and never to a hard block. (Hard blocks are reserved for integrity violations; see `agents/ethics_review_agent.md` Blocking Conditions.) Escalation rests on concrete enabling specifics, not subject matter.

| Level | Action Required |
|-------|----------------|
| None | No additional action |
| Low | Brief note in limitations |
| Moderate | Responsible Use statement in report |
| High | Prominent warning + limited distribution recommendation |
| Critical | Responsible Use statement + recommend institutional ethics review before publication (advisory — does not auto-block; a human, not the agent, adjudicates a Critical flag) |

### Responsible Use Statement Template
```
Responsible Use: This research is intended for [stated purpose]. The authors
acknowledge that findings related to [sensitive area] could potentially be
applied in ways not intended by this research. Users of this research are
urged to consider the ethical implications of their applications and to
prioritize [specific ethical principle].
```

## 4. Fair Representation

### Balanced Treatment Checklist
- [ ] Multiple perspectives on contested issues are presented
- [ ] Minority/dissenting viewpoints are not dismissed without engagement
- [ ] Subjects and communities are described accurately
- [ ] Language is respectful and non-stigmatizing
- [ ] Cultural context is acknowledged where relevant
- [ ] Power dynamics are considered (who is studied vs. who studies)
- [ ] Geographic and cultural diversity in sources

### Sensitive Topics
- Indigenous knowledge: Respect OCAP principles (Ownership, Control, Access, Possession)
- Disability: Person-first language unless community prefers identity-first
- Gender/sexuality: Use inclusive, current terminology
- Race/ethnicity: Use preferred terminology of the communities discussed
- Socioeconomic status: Avoid deficit framing
- Mental health: Avoid stigmatizing language

### Representation Audit Questions
1. Whose voices are centered? Whose are missing?
2. Are communities described on their own terms?
3. Is there implicit bias in the framing?
4. Would the subjects/communities recognize themselves in this description?

## 5. Data Ethics

### Data Source Ethics
- [ ] All data sources are legal to use
- [ ] Public data: Confirm public domain or appropriate license
- [ ] Licensed data: Usage complies with license terms
- [ ] Scraped data: Complies with robots.txt and terms of service
- [ ] Personal data: GDPR/privacy law compliance (if applicable)
- [ ] Institutional data: Authorized access confirmed

### Privacy Protection
- [ ] No personally identifiable information (PII) without consent
- [ ] Aggregated data used where possible
- [ ] Small-N groups protected from identification
- [ ] Institutional identities protected when not public
- [ ] Data retention/deletion plan (if primary data collected)

### AI-Specific Data Concerns
- [ ] AI training data biases acknowledged
- [ ] AI knowledge cutoff date noted
- [ ] AI-generated data clearly labeled as such
- [ ] No circular citation (AI cites AI-generated content)

## 6. Conflict of Interest

### Types to Assess
- [ ] Financial: Funding source, consulting relationships
- [ ] Institutional: Author evaluating own institution
- [ ] Intellectual: Author defending own prior work
- [ ] Personal: Relationships with subjects/stakeholders
- [ ] Political: Government-funded research on government policy
- [ ] Commercial: Industry connections or product interests
- [ ] AI-specific: AI tool company influence on research design

### Disclosure Requirement
Any identified conflict must be disclosed in the report, with an assessment of whether it could have influenced the findings.

## 7. Reproducibility Ethics

### Documentation Requirements
- [ ] Search strategies documented (databases, terms, dates)
- [ ] Inclusion/exclusion criteria documented
- [ ] Analytical methods described in replicable detail
- [ ] AI prompts/instructions documented (if relevant)
- [ ] Data processing steps documented
- [ ] Code/scripts shared (if applicable)

### Reproducibility Statement Template
```
Reproducibility: The search strategy, inclusion criteria, and analytical
methods used in this research are documented in [section/appendix]. The
AI-assisted components used [specific prompts/parameters]. Researchers
wishing to replicate or extend this work should note [relevant limitations
or conditions].
```

## 8. Human Subjects Ethics

### 8.1 Human Subjects Determination

- [ ] Does the research collect, use, or analyze human-related data?
- [ ] If yes, is the data personally identifiable?
- [ ] If the data is publicly available and de-identified, has exempt review status been confirmed with the IRB?

### 8.2 IRB Review Levels

| Review Level | Applicable Conditions | Review Timeline |
|-------------|----------------------|-----------------|
| **Exempt Review** | Public data, de-identified data, anonymous surveys (no sensitive topics) | 1-2 weeks |
| **Expedited Review** | Minimal risk, non-vulnerable populations, general surveys/interviews | 2-4 weeks |
| **Full Board Review** | Greater than minimal risk, vulnerable populations, sensitive topics, deception | 4-8 weeks |

- [ ] Applicable IRB review level has been determined
- [ ] IRB review timeline has been incorporated into the research project schedule
- [ ] Researcher has completed research ethics training (CITI or equivalent course)

### 8.3 Informed Consent

- [ ] Informed consent form includes research title, purpose, procedures, risks, and benefits
- [ ] Clearly states voluntary nature of participation (may withdraw at any time, no penalties)
- [ ] Provides researcher and IRB contact information
- [ ] Special situations addressed:
  - [ ] Online survey: Electronic consent (clicking "I agree")
  - [ ] Audio/video recording: Separate checkbox item
  - [ ] Minors: Legal guardian consent + subject assent
  - [ ] Indigenous research: Community consent + individual informed consent

### 8.4 Data De-identification

- [ ] Remove direct identifiers (names, student IDs, national ID numbers)
- [ ] Assess indirect identifier risks (department + year + gender combinations)
- [ ] Small sample re-identification risk assessment (small departments may allow re-identification of individuals)
- [ ] Remove identifiable details from qualitative quotations
- [ ] Encrypt data storage with access controls
- [ ] Establish data retention and destruction timeline

### 8.5 Vulnerable Population Protection

| Population | Additional Protective Measures |
|-----------|-------------------------------|
| **Minors** | Legal guardian consent + age-appropriate assent form |
| **Persons with disabilities** | Assess consent capacity, provide accessible consent procedures |
| **Students (researcher is a teacher)** | Avoid power dynamics affecting voluntariness, use third-party recruitment |
| **Indigenous peoples** | Community consultation and consent, respect OCAP principles |
| **Economically disadvantaged** | Compensation must not constitute undue inducement |
| **Incarcerated persons** | Additional IRB review, ensure non-coercive participation |

- [ ] Vulnerable populations involved in the research have been identified
- [ ] Corresponding additional protective measures have been planned
- [ ] IRB review level accounts for vulnerable population considerations

> For detailed IRB decision tree and Taiwan-specific process: see `references/irb_decision_tree.md`

---

## Quick Audit Checklist (Pre-Delivery Self-Check)

Before delivery, confirm ALL items (this is a self-check, not a veto):

- [ ] AI disclosure present and accurate
- [ ] All references spot-checked (minimum 20%)
- [ ] No fabricated citations detected
- [ ] Dual-use assessment completed
- [ ] Fair representation reviewed
- [ ] Data sources legally and ethically used
- [ ] Conflicts of interest disclosed
- [ ] Reproducibility documentation provided
- [ ] Writing is inclusive and respectful
- [ ] Report benefits stated audience without causing foreseeable harm
- [ ] If the research involves human subjects, has IRB review been planned?
