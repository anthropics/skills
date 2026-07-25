# Paper-Patent Audit (Corpus Pair)

Use this method when the user supplies both a paper and an existing patent,
or when comparing a drafted application with prior art.

## Inputs

- `paper.txt` — extracted text of the paper (via `extract_pdf_text.py`)
- `patent.txt` — extracted text of the patent claims + abstract
- (Optional) `patent_full.json` — structured representation

## Output schema (`corpus-pair-audit.json`)

```yaml
pairs:
  - feature_id: "F001"
    paper_locator: "P-P005"        # source ID
    patent_locator: "PAT-claim-1"  # source ID
    paper_wording: "短句原话"
    patent_wording: "短句原话"
    relationship:
      - "identical"
      - "paper-broader"
      - "patent-broader"
      - "paper-only"
      - "patent-only"
      - "divergent"
    notes: "..."
overlaps:
  shared_features: ["F001", "F002"]
  paper_only_features: ["F003"]
  patent_only_features: ["F004"]
summary:
  paper_supports_patent_claim_N: [1, 2]
  patent_claim_uniquely_covered_by_paper: [3]
  new_features_in_patent_not_in_paper: [4]
```

## Method

1. Run `audit_claims.py` on the patent claims to get patent locator IDs.
2. Build the paper source map with P/E/F/C IDs.
3. For each material feature in the paper's evidence ledger, search the
   patent claims and spec for matching language.
4. Label the relationship:
   - **identical** — same wording, same scope
   - **paper-broader** — paper discloses more variants than the patent
   - **patent-broader** — patent claims more variants than the paper supports
   - **paper-only** — paper discloses, patent omits
   - **patent-only** — patent claims, paper does not support
   - **divergent** — both contain a feature, but with different scope
5. Compile the overlap tables and a summary of implications.

## What the audit is NOT

The audit is not a patentability opinion, an infringement opinion, or a
prior-art analysis. It is a structured comparison suitable for review by a
patent professional.
