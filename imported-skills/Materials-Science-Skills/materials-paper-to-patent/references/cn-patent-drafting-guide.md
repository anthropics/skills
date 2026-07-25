# Chinese Invention Patent Drafting Guide

This guide summarises the conventions used by this skill when producing
Chinese invention patent text. It is not legal advice. Patent professionals
must review the output before filing.

## Document layout

A complete application package includes:

1. 权利要求书 (claims)
2. 说明书 (specification)
3. 说明书摘要 (abstract)
4. 摘要附图 (abstract figure)

Each document is delivered as a separate DOCX file. The structured JSON in
`draft.json` is the single source of truth for all four.

## Claims

- Use a single independent claim per category. Multi-independent claims are
  allowed only when each addresses a distinct technical solution.
- Independent claims must contain "其特征在于" or an equivalent transitional
  phrase. The technical features after the transitional phrase define the
  scope.
- Method claims describe ordered steps. Apparatus claims describe cooperating
  components. Product claims describe composition and microstructure.
- Dependent claims narrow the independent claim by adding further technical
  features. They may use "其特征在于" to introduce the additional features.
- Avoid:
  - Pure functional limitation ("用于 X 的装置")
  - Marketing-style words ("高性能", "耐久", "完美")
  - Undefined terms
  - Future work or aspirational goals

## Specification

The specification must satisfy the "本领域技术人员能够实现" requirement
(Art. 26(3)). It contains:

- 技术领域 — single sentence.
- 背景技术 — describe the technical problem, existing solutions, and their
  limitations. Cite prior art neutrally.
- 发明内容 — problem, solution, beneficial effects.
- 附图说明 — list figures and their roles.
- 具体实施方式 — provide at least one complete example that enables the
  claimed solution. Include process parameters, units, ranges, and
  measurement methods.
- 工业应用性 — short note on where the invention is industrially applied.

## Abstract

- ≤ 300 Chinese characters
- No commercial or advertising language
- The abstract figure should be a single figure (often the main method
  flowchart) referenced by 摘要附图

## Vocabulary

| Generic | Preferred Chinese |
|---|---|
| strength | 抗压强度 / 抗折强度 / 抗拉强度 |
| w/b | 水灰比 (w/b) |
| SCM | 矿物掺合料 |
| C-S-H | 水化硅酸钙 |
| XRD | X射线衍射 (XRD) |
| SEM | 扫描电子显微镜 (SEM) |
| FTIR | 傅里叶变换红外光谱 (FTIR) |

Use SI units, with unit consistency enforced by
`validate_patent_claims.py`.

## Ranges

- Use en-dash separator: "30-50 wt%".
- Always include a unit.
- A "range" with a single data point is not a range — disclose the actual
  point and use phrasing such as "约 30 wt%".

## Figures

- Use one main method flowchart as the abstract figure and a specification
  figure.
- Methodology figures are produced by the `materials-figure` skill. This
  skill only writes the figure description text and the figure number
  reference.
