# AI Advisor Workflow

クライアントのWebサイトから情報を収集・分析し、業種特性に応じたAI活用提案書とAgentSkillsを自動生成する統合ワークフローシステムです。

## 特徴

### 🎯 複数URL対応の深い分析
- 単一URLまたは複数URLのリンク集に対応
- メインサイト、サービス詳細、事例、会社概要など複数ページから包括的に情報収集
- 業種・業態をより正確に特定し、詳細なサービス内容を把握

### 🤖 スタメン＆プール方式のスキル生成
- **スタメンSkills**: 実績のある50以上の既存AgentSkillsをベースに活用
- **プールSkills**: 過去に生成したクライアント向けスキルを参考にカスタマイズ
- 優秀なスキルはスタメンに昇格可能な仕組み

### 📊 包括的な提案書生成
- エグゼクティブサマリー
- 詳細提案書（現状分析、AI活用案、実装計画）
- プレゼンテーション資料
- ROI分析レポート
- 実装ロードマップ

## インストール

```bash
# 依存関係のインストール
pip install -r requirements.txt

# または個別インストール
pip install requests beautifulsoup4 pyyaml pandas numpy
```

## 🎯 トリガーワード機能

自然な日本語でワークフローを実行できます！

### 基本的なトリガーワード
```bash
# 対話型CLIを起動
python -m workflow_cli

# または
python scripts/workflow_cli.py
```

実行例:
- 📊 **分析**: "https://example.com を分析して"
- 📝 **提案書**: "株式会社〇〇のAI活用提案書を作成"
- 🛠️ **スキル生成**: "在庫管理のスキルを作って"
- 🚀 **フル実行**: "分析から提案まで全部お願い"
- ⚡ **クイック**: "ざっくりサイトをチェック"

詳細は[トリガーワードガイド](docs/trigger_words_guide.md)を参照してください。

## 使用方法

### 1. Pythonスクリプトとして使用

```python
from ai_advisor_workflow import AIAdvisorWorkflow

# ワークフローの初期化
workflow = AIAdvisorWorkflow()

# 単一URLの場合
result = workflow.execute(
    client_urls="https://example.com",
    output_dir="./output/example_company"
)

# 複数URLの場合（推奨）
urls = [
    "https://example.com",
    "https://example.com/services",
    "https://example.com/products",
    "https://example.com/case-studies",
    "https://example.com/about"
]

result = workflow.execute(
    client_urls=urls,
    output_dir="./output/example_company",
    generate_skills=True
)
```

### 2. コマンドラインから使用

```bash
# 単一URL
python -m ai_advisor_workflow https://example.com

# 複数URL（推奨）
python -m ai_advisor_workflow \
    https://example.com \
    https://example.com/services \
    https://example.com/products \
    https://example.com/about

# オプション付き
python -m ai_advisor_workflow https://example.com \
    --output ./proposals/client_name \
    --config custom_config.json \
    --no-skills
```

### 3. テストスクリプトの実行

```bash
# サンプルデータでテスト
python test_workflow.py

# 実際のURLでテスト
python test_workflow.py --url https://example.com

# サンプル設定ファイルの作成
python test_workflow.py --create-config
```

## 出力ファイル構成

```
output/
├── proposal/                      # 提案書類
│   ├── executive_summary.md      # エグゼクティブサマリー
│   ├── ai_proposal_detailed.md   # 詳細提案書
│   ├── ai_proposal_slides.md     # プレゼンテーション
│   ├── implementation_roadmap.md # 実装ロードマップ
│   └── roi_analysis.md          # ROI分析レポート
├── generated_skills/             # 生成されたAgentSkills
│   ├── ai-customer-automation/
│   ├── ai-data-analyzer/
│   └── ...
└── reports/                      # 分析レポート
    └── workflow_results.json     # 実行結果サマリー
```

## 設定オプション

`config.json`で詳細な動作をカスタマイズできます：

```json
{
  "web_extractor": {
    "timeout": 30,
    "max_pages": 50,
    "follow_links": true
  },
  "analysis": {
    "industry_classification": true,
    "business_process_extraction": true,
    "competitor_analysis": false
  },
  "proposal": {
    "categories": ["業務効率化", "顧客体験向上", "データ分析"],
    "max_proposals_per_category": 3,
    "include_roi_calculation": true
  },
  "skill_generation": {
    "generate_tests": true,
    "include_documentation": true,
    "template_style": "standard"
  }
}
```

## URL選定のベストプラクティス

効果的な分析のため、以下のようなURLを含めることを推奨：

### 必須
- メインページ（トップページ）
- 会社概要・企業情報ページ
- 事業内容・サービスページ

### 推奨
- 導入事例・実績ページ
- 製品・ソリューション詳細ページ
- 採用情報ページ（組織文化の理解）
- ニュース・お知らせページ

### オプション
- IR情報ページ
- 技術情報・研究開発ページ
- サステナビリティ・CSRページ

## 生成されるAgentSkillsについて

### スタメンSkillsの活用
- 既存の実績あるスキルをベースに使用
- コード構造やベストプラクティスを継承
- 安定性と品質を確保

### プールシステム
- 生成されたスキルは`client-skills-pool/`に保存
- 類似業種のスキルを参考に最適化
- 使用実績に基づいてスタメン昇格を判定

### カスタマイズポイント
- 提案内容に基づく自動命名
- 業種・用途に応じた依存関係の設定
- ドキュメントとテストの自動生成

## トラブルシューティング

### Web情報が取得できない場合
- URLが正しくアクセス可能か確認
- `robots.txt`による制限を確認
- タイムアウト設定を調整

### スキル生成でエラーが発生する場合
- Pythonのバージョンを確認（3.8以上推奨）
- 依存関係が正しくインストールされているか確認
- 出力ディレクトリの書き込み権限を確認

### メモリ不足エラー
- `max_pages`設定を減らす
- 一度に処理するURLの数を減らす

## 開発者向け情報

### ディレクトリ構造
```
ai-advisor-workflow/
├── scripts/
│   ├── main.py              # メインワークフロー
│   ├── hp_analyzer.py       # Web情報抽出
│   ├── business_analyzer.py # 業種・業務分析
│   ├── ai_proposal_engine.py # AI提案生成
│   ├── document_generator.py # 提案書作成
│   └── skill_generator.py   # スキル自動生成
├── references/              # 参考資料
├── assets/                  # アセットファイル
├── SKILL.md                # スキル定義
├── README.md               # このファイル
└── test_workflow.py        # テストスクリプト
```

### 拡張方法
1. 新しい業種テンプレートの追加: `ai_proposal_engine.py`の`industry_templates`に追加
2. 新しいドキュメント形式の追加: `document_generator.py`に生成メソッドを追加
3. スキルテンプレートの追加: `skill_generator.py`の`skill_templates`を拡張

## ライセンス
[プロジェクトのライセンスに準拠]

## 貢献
バグ報告や機能提案は、GitHubのIssuesまでお願いします。

## 作成者
AI Advisor System - ken_AgentSkillsプロジェクトの一部として自動生成