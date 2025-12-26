---
name: profession-skill-generator
description: |
  参加者の職業とペイン（課題）を分析し、シンデレラフィットする5つのAgent Skillsを生成。
  5軸特性分析→7業務カテゴリー動的生成→AI活用分析→スキル抽出→SKILL.md生成まで一貫実行。
  ワークショップデモでパラレル実行される個別生成エージェント。

  トリガー:
  - 「{職業}向けのスキルを5個生成」
  - 「{職業}で{ペイン}を解決するスキル」
---

# Profession Skill Generator

参加者の職業とペインに最適化された5つのAgent Skillsを生成するサブエージェント。

## Purpose

1人の参加者情報（職業・ペイン）を受け取り、その人にシンデレラフィットする
5つの実用的なAgent Skillsを分析・設計・生成する。

## Input Requirements

```
- 名前: {参加者名}
- 職業: {職業名}
- ペイン: {具体的な課題・悩み}
- 出力先: {ディレクトリパス}
```

## Workflow

### Phase 1: 職業特性メタ分析（5軸評価）

対象職業を以下の5軸で評価:

| 軸 | 評価オプション |
|---|---|
| **時間軸** | 過去志向（記録・分析）/ 現在志向（処理・管理）/ 未来志向（計画・創造）|
| **対象軸** | 内部特化（組織内）/ 外部特化（対外）/ 内外統合 |
| **処理軸** | ルーチン重視（定型）/ 判断重視（専門）/ 創造重視 |
| **価値軸** | コンプライアンス / オペレーション / イノベーション |
| **専門軸** | 汎用型 / 専門型 / 統合型 |

### Phase 2: 7業務カテゴリー動的生成

職業特性に基づき、MECE原則で7つの業務カテゴリーを設計:

- **コアカテゴリー**: 2〜3（職業の核心業務）
- **サポートカテゴリー**: 2〜3（支援業務）
- **成長カテゴリー**: 1〜2（スキルアップ・改善）

命名規則: 「○○・○○業務」形式

### Phase 3: ペイン重点AI活用分析

**CRITICAL**: 参加者のペインを最優先で分析

1. ペインが該当するカテゴリーを特定
2. そのカテゴリーに対して重点的にAI活用案を検討
3. 各カテゴリー5項目 × 7 = 35項目を分析

**分析スキーマ:**
```
| 業務フロー | AI活用案 | 活用例詳細 | 難易度 | 必要スキル | 評価 |
```

評価基準:
- **A（即採用）**: ペインに直結 or 効果絶大
- **B（検討）**: 有用だが優先度中
- **C（将来）**: 将来的に検討

### Phase 4: シンデレラフィットスキル抽出

評価A項目から、以下の優先度マトリクスで5つを選定:

| 繰り返し性 | 複雑性 | 優先度 |
|---|---|---|
| 高（週5回+） | 高 | 最優先 |
| 高 | 低 | 高 |
| 低 | 高 | 中 |
| 低 | 低 | 対象外 |

**シンデレラフィット条件:**
1. ペインに直接対応
2. 週5回以上の利用見込み
3. 入力→処理→出力が明確
4. 30分〜2時間で実装可能

### Phase 5: SKILL.md生成

選定した5スキルそれぞれについて、以下の形式でSKILL.mdを生成:

```markdown
---
name: {skill-name-kebab-case}
description: |
  {何をするスキルか - 1行}

  トリガー:
  - 「{フレーズ1}」
  - 「{フレーズ2}」
---

# {Skill Name}

## Purpose
{単一目的の明確な定義}

## Workflow
1. {ステップ1}
2. {ステップ2}
3. {ステップ3}

## Input Requirements
- {必要な入力とその形式}

## Output Specification
- 形式: {出力形式}
- 品質基準: {期待される品質}

## Examples
### Example 1
入力: {具体例}
出力: {結果例}

## Constraints
- DO: {すべきこと}
- DO NOT: {すべきでないこと}
```

## Output Specification

指定された出力先に以下の構造で生成:

```
{output_path}/
├── skill-1-{name}/
│   └── SKILL.md
├── skill-2-{name}/
│   └── SKILL.md
├── skill-3-{name}/
│   └── SKILL.md
├── skill-4-{name}/
│   └── SKILL.md
└── skill-5-{name}/
    └── SKILL.md
```

加えて、サマリーファイルを生成:
```
{output_path}/SUMMARY.md
```

## Summary Format

```markdown
# {参加者名}さん向け Agent Skills

## プロフィール
- 職業: {職業}
- ペイン: {ペイン}

## 5軸分析結果
| 軸 | 評価 |
|---|---|
| 時間軸 | {評価} |
| ... | ... |

## 生成スキル一覧

### 1. {skill-1-name}
- **目的**: {1行説明}
- **ペインとの関連**: {どう解決するか}
- **利用頻度**: 週{N}回想定

### 2. {skill-2-name}
...

## 導入推奨順序
1. {最初に導入すべきスキル} - 理由: {ペインに最も直結}
2. ...
```

## Example Execution

**入力:**
```
名前: 山田太郎
職業: ソフトウェアエンジニア
ペイン: コードレビューに時間がかかりすぎる
出力先: /home/user/skills/generated/山田太郎/
```

**分析プロセス:**

1. **5軸評価**:
   - 時間軸: 現在志向（処理・管理）
   - 対象軸: 内部特化
   - 処理軸: 判断重視
   - 価値軸: オペレーション
   - 専門軸: 専門型

2. **7カテゴリー生成**:
   - 要件定義・設計業務
   - 開発・実装業務
   - **コードレビュー・品質管理業務** ← ペイン該当
   - テスト・検証業務
   - 運用・保守業務
   - 技術調査・学習業務
   - チーム連携・ナレッジ共有業務

3. **ペイン重点分析**: コードレビュー関連を深掘り

4. **5スキル選定**:
   1. `code-review-summarizer` - PR差分を要約
   2. `review-checklist-generator` - レビュー観点自動生成
   3. `code-smell-detector` - 問題パターン検出
   4. `review-comment-drafter` - レビューコメント下書き
   5. `pr-description-enhancer` - PR説明文改善

**出力:**
```
/home/user/skills/generated/山田太郎/
├── skill-1-code-review-summarizer/
│   └── SKILL.md
├── skill-2-review-checklist-generator/
│   └── SKILL.md
├── skill-3-code-smell-detector/
│   └── SKILL.md
├── skill-4-review-comment-drafter/
│   └── SKILL.md
├── skill-5-pr-description-enhancer/
│   └── SKILL.md
└── SUMMARY.md
```

## Constraints

- **DO**: ペインに直結するスキルを最優先
- **DO**: 具体的で即使えるスキルを生成
- **DO**: kebab-case命名規則を厳守
- **DO NOT**: 汎用的すぎるスキルを生成しない
- **DO NOT**: 実装困難（★★★）なスキルを選ばない
- **DO NOT**: 既存の document-skills (docx/xlsx/pdf/pptx) と重複しない

## References

職業別テンプレートは `references/skill_templates/` を参照:
- `developer.md` - エンジニア系
- `marketer.md` - マーケティング系
- `designer.md` - デザイナー系
- `manager.md` - マネージャー系
- `analyst.md` - アナリスト系
- `sales.md` - 営業系
- `support.md` - サポート系
- `generic.md` - 汎用
