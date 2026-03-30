# Fact-Checking Protocol

Every claim in the input report must be verified before it appears in the output. Chris's reputation and his clients' investment decisions depend on this.

## Extracting Claims

Read the pasted report sentence by sentence. A claim is any factual assertion:

- "Drug X treats disease Y"
- "Gene Z is mutated in 40% of cases"
- "Company A has N trials in Phase 3"
- "The market is worth $B billion"
- "Mechanism X drives resistance to therapy Y"
- "Natural product X inhibits target Y"

Opinion, speculation, and framing ("we believe", "it is likely", "the future may") are NOT claims. Note them separately as editorial content.

## Verification Protocol

For each claim:

1. **Identify the entity type** (gene, drug, disease, company, market figure, mechanism)
2. **Search the tool catalog** for databases that can verify this type of claim
3. **Query at least 2 independent sources** — never rely on a single database
4. **Compare the claim to what the databases say** — exact match, partial match, or contradiction?

## Classification

| Status | Definition | Evidence required | Output treatment |
|--------|-----------|------------------|-----------------|
| **Verified** | Claim matches T1/T2 sources | 2+ independent sources agree | State as fact with margin citations |
| **Corrected** | Claim is wrong or outdated | Source showing the correct information | Show correction with evidence |
| **Unverifiable** | No database evidence found | Searched 3+ relevant databases | Flag explicitly — do NOT present as fact |
| **Misleading** | Technically true but omits critical context | Source providing missing context | Include the context alongside the claim |

## Zero-Tolerance Rule

If a claim cannot be verified by at least one T1 (regulatory/curated) or T2 (peer-reviewed) source, it does NOT appear as fact in the final report. It can appear in a "Claims Under Review" section clearly marked as unverified. No exceptions.

This means:

- **No T3-only claims presented as fact** — preprints and web sources corroborate, they don't verify
- **No T4-only claims presented as fact** — computational predictions are hypotheses, not findings
- **No claim without a citation** — if you can't cite it, you can't include it
- **No rounding or paraphrasing that changes meaning** — "~40% response rate" is OK, "high response rate" is not (what is "high"?)

## Handling Edge Cases

| Situation | Action |
|-----------|--------|
| Claim uses a different number than the source | Report the source's number with citation; note the discrepancy |
| Claim is true but the cited study has been retracted | Flag as corrected — cite the retraction |
| Claim is an industry consensus but no single definitive source | Verify with 3+ T2 sources, note it's consensus |
| Claim mixes two true facts into a false implication | Separate the facts, correct the implication |
| Claim is about a future event ("will launch in Q3") | Flag as unverifiable — can note the company's stated plans with SEC citation |

## Append to Research Notes

After fact-checking, append to `research_notes.md`:

```markdown
## Claims Audit
- "GLP-1 agonists reduce body weight by 15-20%" → VERIFIED
  [T2: PubMed PMID:34567890, T1: FDA label for semaglutide]
- "Market expected to reach $50B by 2030" → UNVERIFIABLE
  No T1/T2 source found. Industry estimates vary $30-80B.
- "No cardiovascular risk with semaglutide" → CORRECTED
  SUSTAIN-6 trial showed CV BENEFIT, not just absence of risk.
  [T1: ClinicalTrials NCT01720446, T2: PMID:27633186]
```
