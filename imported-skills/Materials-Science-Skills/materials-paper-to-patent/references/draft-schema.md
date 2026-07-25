# Draft Schema (draft.json)

A complete draft.json contains the following top-level keys. See
`examples/civil-concrete-strengthening/draft.json` for a working example.

```yaml
title: string            # 发明名称
metadata: object         # see below
source_analysis: object  # see below
source_map: array        # P/E/F/C tagged evidence
terminology_ledger: array
formula_inventory: array
figure_inventory: array
evidence_ledger: array
invention_concept: object
claims: array
claim_feature_map: array
figures: array
abstract_figure_number: integer
specification: object
abstract: string
quality_assessment: object
```

## metadata

```yaml
jurisdiction: "CNIPA"
invention_type: "process-material" | "apparatus-system" | "algorithm-software" | "mixed"
language_mode: "zh"
applicant: string        # [TO CONFIRM] if unknown
inventors: array
```

## evidence_ledger

Each entry:

```yaml
- id: "EV001"
  feature: "短句描述"
  source_ids: ["P001", "P002"]
  support_status: "explicit" | "inherent" | "needs-confirmation" | "unsupported"
  technical_role: "..."         # 必要技术特征 / 附加技术特征 / ...
  effect: "..."                 # 解决的技术问题 / 取得的技术效果
  proposed_destination: "claim-N" | "spec" | "background" | "remove"
```

## claims

```yaml
- number: 1
  type: "independent" | "dependent"
  depends_on: [1]              # required for dependent
  text: "..."
  feature_map: ["EV001", "EV002"]
```

## specification

```yaml
技术领域: "..."
背景技术: "..."
发明内容:
  problem: "..."
  solution: "..."
  beneficial_effects: "..."
具体实施方式: "..."
figure_descriptions:
  - number: 1
    caption: "图1 ..."
    description: "..."
    source: "F001"
    figure_type: "flowchart" | "schematic" | "microstructure" | "chart"
equations:
  - number: "公式1"
    latex: "f_c = A * x^2"
    description: "..."
    symbols:
      f_c: "抗压强度"
      A: "常数"
```

## quality_assessment

Populated at the end. Each dimension scored 1-5. Status is `review-draft`
or `incomplete-draft` per the contract.
