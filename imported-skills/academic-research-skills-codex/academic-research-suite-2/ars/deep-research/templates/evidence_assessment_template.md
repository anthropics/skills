# Evidence Assessment Template

## Purpose
Per-source quality assessment card. Used by the source_verification_agent to systematically evaluate each source entering the research pipeline.

## Assessment Card

```markdown
## Evidence Assessment Card

### Source Identification
- **Citation (APA 7.0)**: [full reference]
- **DOI/URL**: [link]
- **Type**: [journal article / book / report / web / conference paper / thesis / other]
- **Access Date**: [when verified]

---

### Quality Assessment

#### 1. Evidence Level
**Level**: [I / II / III / IV / V / VI / VII]
**Justification**: [why this level]

#### 2. Publication Venue
- **Journal/Publisher**: [name]
- **Indexed in**: [Scopus / WoS / PubMed / DOAJ / other / none]
- **Impact Factor/CiteScore**: [value or N/A]
- **COPE member**: [Yes / No / Unknown]
- **Predatory indicators**: [None / Flags: list]

**Venue Grade**: [Excellent / Good / Adequate / Questionable / Unacceptable]

#### 3. Author Credibility
- **Author(s)**: [names]
- **Affiliation(s)**: [institutions]
- **ORCID**: [if available]
- **Track record**: [publication history in field]
- **Expertise match**: [relevant to topic? Yes/Partial/No]

**Author Grade**: [Excellent / Good / Adequate / Unknown / Questionable]

#### 4. Methodological Quality
- **Design**: [description]
- **Sample**: [size, selection, representativeness]
- **Analysis**: [appropriate for design?]
- **Limitations acknowledged**: [Yes / Partially / No]
- **Replicable**: [Yes / Partially / No]

**Method Grade**: [Excellent / Good / Adequate / Weak / Flawed]

#### 5. Currency
- **Publication year**: [YYYY]
- **Data collection period**: [if stated]
- **Field velocity**: [Rapid / Moderate / Slow / Foundational]
- **Still current**: [Yes / Conditionally / No]

**Currency Grade**: [Current / Acceptable / Dated / Outdated / Foundational]

#### 6. Conflict of Interest
- **Declared COI**: [None / Listed: details]
- **Funding source**: [source or Not stated]
- **Potential undeclared COI**: [None detected / Possible: details]

**COI Grade**: [Clean / Minor / Moderate / Significant / Critical]

---

### Overall Assessment

| Dimension | Grade |
|-----------|-------|
| Evidence Level | [I-VII] |
| Venue | [Excellent-Unacceptable] |
| Author | [Excellent-Questionable] |
| Method | [Excellent-Flawed] |
| Currency | [Current-Outdated] |
| COI | [Clean-Critical] |
| **Overall** | **[A / B / C / D / F]** |

### Recommendation
- [ ] **Use as primary evidence** (Grade A-B)
- [ ] **Use as supporting evidence** (Grade B-C)
- [ ] **Use with explicit caveats** (Grade C-D)
- [ ] **Do not use** (Grade D-F) — Reason: [specific reason]

### Notes
[Any additional observations, caveats, or context]
```

## Batch Assessment Summary

```markdown
## Source Verification Summary

**Date**: [YYYY-MM-DD]
**Sources assessed**: [N]
**Assessor**: source_verification_agent

### Grade Distribution
| Grade | Count | % |
|-------|-------|---|
| A (Excellent) | X | X% |
| B (Good) | X | X% |
| C (Adequate) | X | X% |
| D (Weak) | X | X% |
| F (Unacceptable) | X | X% |

### Flagged Sources
| Source | Issue | Severity | Recommendation |
|--------|-------|----------|---------------|
| [ref] | [issue] | [High/Medium/Low] | [Include with caveat / Exclude] |

### Predatory Journal Alerts
[List any flagged journals]

### Overall Source Base Quality
**Assessment**: [Strong / Adequate / Mixed / Weak]
**Recommendation**: [Proceed / Supplement / Major revision of source base needed]
```

## Usage Notes
- Complete one card per source for full verification
- Batch summary should be produced after all cards are complete
- Minimum spot-check: 20% of sources get full card assessment
- All Grade D/F sources require documented justification
- Any predatory journal flag requires full verification
