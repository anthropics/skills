# IRB Terminology Glossary

**Spec:** v3.6.7 §7.1 — pattern protection reference for `research_architect_agent` (survey designer mode), Pattern B1.

**Audience:** Agents drafting consent / privacy language in survey instruments. Human authors reviewing instrument drafts.

**Why this exists:** In live ARS pipeline runs, survey instrument drafts repeatedly conflated four IRB terms that look adjacent in everyday English but carry distinct operational commitments. Conflation creates legal-effect drift in the consent script and can make the instrument unenforceable as informed consent. This reference is the canonical distinction the survey designer must pass through.

---

## The four terms

The four terms differ along two axes: (1) what is hidden — identity vs. content — and (2) whether re-identification is technically possible.

### Anonymity

**Operational definition:** The respondent's identity cannot be linked to their response by anyone, including the researcher. No identity key is created or stored.

**Necessary conditions:**
- No name, email, IP, device fingerprint, or directly-identifying field is collected.
- No code or token is created that could later be matched back to the respondent.
- Demographic combinations are coarse enough that no respondent is uniquely identifiable from the demographic combination alone (k-anonymity ≥ k for some agreed k, typically k ≥ 5).

**Example consent phrasing (correct):**
> "Your responses are anonymous. We do not collect your name, email, or any identifier that could link this survey to you. We cannot contact you about your responses, and we cannot remove your responses from the dataset after submission because we cannot identify which responses are yours."

**Common drift to flag:**
- Claiming "anonymous" while collecting email "for follow-up" — that is **confidential**, not anonymous.
- Claiming "anonymous" while assigning a respondent code that the researcher holds — that is **pseudonymous**, not anonymous.

### Confidentiality

**Operational definition:** The respondent's identity IS known to the researcher, but the researcher commits not to disclose it. Identity-response linkage exists in the research record.

**Necessary conditions:**
- A written commitment specifies who can see the identified data, for what purpose, and for how long.
- Storage and access controls match the commitment (encrypted at rest, access-logged, retention-bounded).
- Reporting layer aggregates or de-identifies before any external disclosure.

**Example consent phrasing (correct):**
> "Your responses are confidential. We will know your identity from the email you provide for follow-up. Your name will not appear in any report. Only the named research team will see identified data, and identified data will be deleted within 12 months of project close."

**Common drift to flag:**
- Promising "confidentiality" without specifying a retention boundary — IRB will reject; respondent cannot evaluate the commitment.
- Promising "confidentiality" while planning to publish identifiable case-study quotes — that is a contradiction; either the consent script needs an explicit case-study clause or the publication plan needs aggregation.

### De-identification

**Operational definition:** Direct identifiers have been removed from a dataset, and the link key created during data collection has been destroyed. The remaining record cannot be re-linked to the respondent.

**Necessary conditions:**
- Direct identifiers (HIPAA Safe Harbor's 18 fields or the project's equivalent list) are removed or transformed into non-reversible categories.
- Quasi-identifiers (zip + birth-date + gender, etc.) are evaluated for re-identification risk against plausible auxiliary datasets and reduced to acceptable risk threshold.
- The link key used during data collection is **destroyed**. Any retained re-link key — even one held by an independent custodian — falls under pseudonymization (next section), not de-identification, because re-identification remains technically possible.

**Example dataset description (correct):**
> "The released dataset is de-identified. Names, emails, exact dates, and institutional affiliation have been removed. Birth year is generalised to 5-year buckets. The collection-time link key was destroyed at the close of data collection."

**Common drift to flag:**
- Claiming "de-identified" while keeping the link key for "potential follow-up" — that is **pseudonymized**, not de-identified.
- Claiming "de-identified" without a quasi-identifier risk evaluation — k-anonymity unverified.

### Pseudonymization

**Operational definition:** Direct identifiers have been replaced by a pseudonym (code, token, hash). The pseudonym is reversible because the link key is preserved somewhere — typically by the data controller.

**Necessary conditions:**
- A documented pseudonymization scheme specifies the substitution method and the link-key custodian.
- The link key is held separately from the pseudonymized dataset, with separate access controls.
- Use cases (longitudinal follow-up, data subject access request, error correction) are pre-specified.

**Example dataset description (correct):**
> "The dataset is pseudonymized. Each participant is assigned an opaque code (e.g., P-0042). The mapping from code to participant identity is held by the principal investigator and is not shared with the analytic team. The mapping is retained for 24 months to support follow-up surveys, then destroyed."

**Common drift to flag:**
- Calling pseudonymized data "anonymized" — under GDPR, EU AI Act, and most modern IRB guidance, pseudonymized data remains personal data subject to the full data protection regime.

---

## Quick distinction table

| Term | Identity-response link exists? | Held by whom? | Reversible? |
|---|---|---|---|
| **Anonymity** | No | N/A | No |
| **Confidentiality** | Yes | Researcher | Yes (within research team) |
| **De-identification** | No (key destroyed) | N/A | No (assuming key destroyed and quasi-identifier risk acceptable) |
| **Pseudonymization** | Yes (via key) | Researcher / data controller | Yes |

---

## Where this glossary is enforced

The `research_architect_agent` survey designer mode prompt requires consent / privacy language to pass through this glossary before output. The authoritative protection clause lives in `deep-research/agents/research_architect_agent.md` under `PATTERN PROTECTION (v3.6.7)`. This file defines the four regimes and example phrasings; the agent prompt cites this file by path.

---

## References

- HHS HIPAA Safe Harbor de-identification (45 CFR 164.514(b)(2)) — primary source for direct-identifier list.
- GDPR Art. 4(5) — pseudonymization definition.
- EU AI Act Recital 27 + Art. 10(5) — pseudonymization vs. anonymization distinction in AI training contexts.
- ISO/IEC 27559:2022 — privacy-enhancing data de-identification framework.
