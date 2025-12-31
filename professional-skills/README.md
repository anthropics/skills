# Professional Skills Directory

## 概要
職業別に整理されたAgent Skillsのディレクトリです。各スキルはタグベースで分類され、検索・再利用が容易な構造になっています。

## ディレクトリ構造

```
professional-skills/
├── _system/                      # システムファイル
│   ├── indexes/                 # インデックスファイル
│   │   └── skill-index.json    # 全スキルの検索用インデックス
│   ├── templates/              # テンプレート
│   │   └── skill-template.yaml # SKILL.yamlのテンプレート
│   └── skill-taxonomy.yaml     # タグ分類体系の定義
│
├── legal-professionals/         # 法律専門職
│   └── gyosei-shoshi/          # 行政書士
│       ├── license-application-generator/
│       ├── contract-template-generator/
│       └── company-formation-kit/
│
├── labor-professionals/         # 労務専門職
│   └── sharoushi/              # 社会保険労務士
│       ├── social-insurance-calculator/
│       ├── labor-insurance-updater/
│       └── work-rules-comparator/
│
└── financial-professionals/     # 財務・会計専門職
    └── zeirishi/               # 税理士
        ├── tax-return-assistant/
        ├── expense-categorizer/
        └── monthly-report-generator/
```

## スキルの構成

各スキルディレクトリには以下のファイルが含まれます：
- `SKILL.md` - スキルの詳細説明（人間が読むため）
- `SKILL.yaml` - 構造化されたメタデータ（システムが処理するため）

## タグシステム

### 4つのタグカテゴリ

1. **機能タグ (Function)**
   - document-generation（文書生成）
   - calculation（計算）
   - validation（検証）
   - analysis（分析）

2. **業務プロセスタグ (Business Process)**
   - license-application（許認可申請）
   - compliance（コンプライアンス）
   - financial-reporting（財務報告）
   - payroll（給与計算）

3. **効果タグ (Impact)**
   - time-saving（時間削減）
   - accuracy-improvement（精度向上）
   - risk-reduction（リスク削減）
   - automation（自動化）

4. **技術タグ (Technology)**
   - pdf-processing（PDF処理）
   - ai-ml（AI/機械学習）
   - api-integration（API連携）
   - ocr（文字認識）

## スキルの検索方法

### 職業で検索
```bash
# 税理士向けのスキルを表示
ls financial-professionals/zeirishi/
```

### タグで検索（インデックス利用）
skill-index.jsonを参照して、特定のタグを持つスキルを検索できます。

### 優先度で検索
- high: 5スキル
- medium: 4スキル
- low: 0スキル

## 統計情報

- **総スキル数**: 9
- **職業分布**:
  - 行政書士: 3スキル
  - 社会保険労務士: 3スキル
  - 税理士: 3スキル
- **最も多いタグ**:
  - time-saving: 9スキル（全スキル）
  - compliance: 5スキル
  - accuracy-improvement: 5スキル

## 新しいスキルの追加方法

1. 適切な職業カテゴリを選択
2. スキルディレクトリを作成
3. SKILL.mdとSKILL.yamlを作成
4. skill-index.jsonを更新

詳細は`_system/templates/skill-template.yaml`を参照してください。

## 関連ドキュメント

- [構造化提案](RESTRUCTURE_PROPOSAL.md)
- [実装計画](IMPLEMENTATION_PLAN.md)
- [タグ分類体系](_system/skill-taxonomy.yaml)