# Output Contract

A complete package contains:

1. `outputs/patent_claims.docx` — 权利要求书
2. `outputs/patent_specification.docx` — 说明书
3. `outputs/patent_abstract.docx` — 说明书摘要
4. `outputs/patent_abstract_figure.png` — 摘要附图
5. `outputs/patent_main_flowchart.svg` — 主流程图
6. `outputs/draft.json` — 结构化草稿
7. `outputs/validation_report.txt` — validate_patent_draft 报告
8. `outputs/claims_validation_report.txt` — validate_patent_claims 报告
9. `outputs/audit_report.json` — audit_claims 报告

## Quality Thresholds

| Dimension | Threshold | Description |
|---|---|---|
| evidence_support | 4 | Every essential feature maps to source |
| claim_architecture | 4 | Independent + dependent claim chain valid |
| terminology_consistency | 4 | No forbidden aliases in formal text |
| enablement_detail | 3 | Specification enables person skilled in art |
| technical_effect_reasoning | 3 | Cause-effect chain justified |
| formula_coverage | 4 | When source has core formulas, all retained |
| figure_alignment | 4 | Claim steps correspond to figure nodes |

If any threshold is missed, label the package `incomplete draft` and list
the gaps in the abstract or cover memo.

## Status Labels

- `review-draft` — meets all thresholds; ready for inventor review;
- `incomplete-draft` — fails one or more thresholds; not for filing.
