---
name: AI Advisor Workflow
version: 1.0.0
description: クライアントのHPから情報を収集・分析し、業種特性に応じたAI活用提案書とAgentSkills実装まで自動生成するワークフロー
author: AI Advisor System
tags: [workflow, ai-proposal, automation, business-analysis]
dependencies:
  - web-content-extractor
  - web-test-automation
  - data-report-generator
  - presentation-creator
  - project-planner
  - gantt-chart-generator
  - skill-creation-guide
  - workflow-kenken
---

# AI Advisor Workflow

## 概要
クライアントのWebサイトから情報を自動収集し、業種特性を分析した上で、最適なAI活用提案書を生成し、さらにAgentSkillsの実装コードまで自動生成する統合ワークフローシステムです。

## 主な機能

### 1. HP情報収集・解析
- Webサイトの自動クロール
- 会社概要・業務内容の抽出
- 業種・業態の自動判定

### 2. AI活用提案生成
- 業種別AIユースケースマッチング
- 優先順位付けとROI試算
- 実装ロードマップ作成

### 3. 提案書自動作成
- エグゼクティブサマリー
- 現状分析と課題抽出
- AI活用提案（カテゴリ別）
- 期待効果とKPI設定

### 4. AgentSkills自動実装
- 提案内容に基づくスキル設計
- 実装コードの自動生成
- テストコードの生成

## 使用方法

```python
from ai_advisor_workflow import AIAdvisorWorkflow

# ワークフローの初期化
workflow = AIAdvisorWorkflow()

# クライアントのHP URLを指定して実行
result = workflow.execute(
    client_url="https://example.com",
    output_dir="./proposals/client_name",
    generate_skills=True
)

# 結果の確認
print(f"提案書: {result['proposal_path']}")
print(f"生成されたスキル: {result['generated_skills']}")
```

## ワークフロー構成

```mermaid
graph TD
    A[HP URL入力] --> B[Web情報収集]
    B --> C[業種・業務分析]
    C --> D[AI活用案生成]
    D --> E[優先順位評価]
    E --> F[提案書作成]
    F --> G[AgentSkills生成]
    G --> H[統合パッケージ出力]
```

## 出力ファイル構成

```
output/
├── proposal/
│   ├── executive_summary.md
│   ├── ai_proposal.pdf
│   ├── ai_proposal.pptx
│   └── implementation_roadmap.xlsx
├── generated_skills/
│   ├── customer_support_ai/
│   ├── data_analysis_automation/
│   └── process_optimization/
└── reports/
    ├── website_analysis.json
    ├── industry_insights.md
    └── roi_calculation.xlsx
```

## カスタマイズ

### 業種別テンプレート追加
`references/industry_templates/`に新しい業種テンプレートを追加できます。

### AI提案カテゴリ拡張
`scripts/ai_proposal_engine.py`の`PROPOSAL_CATEGORIES`を編集します。

## 注意事項
- 大規模なWebサイトの場合、スクレイピングに時間がかかる場合があります
- 生成されたAgentSkillsは必ず動作確認を行ってください
- APIキー（OpenAI/Claude）の設定が必要です