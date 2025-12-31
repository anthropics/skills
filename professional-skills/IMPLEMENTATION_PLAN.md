# 職業別・タグベース スキル管理システム 実装計画

## エグゼクティブサマリー
既存の9つのスキルを新しい職業別構造とタグシステムに移行し、検索性と再利用性を大幅に向上させます。

## 実装フェーズ

### Phase 0: 準備フェーズ（即時実行可能）
#### 0.1 ディレクトリ構造の作成
```bash
professional-skills/
├── legal-professionals/
│   ├── gyosei-shoshi/
│   ├── shiho-shoshi/
│   └── bengoshi/
├── labor-professionals/
│   ├── sharoushi/
│   └── roumu-consultant/
├── financial-professionals/
│   ├── zeirishi/
│   ├── kaikei-shi/
│   └── fp/
└── _system/
    ├── templates/
    ├── tools/
    └── indexes/
```

#### 0.2 システムファイルの配置
- `skill-taxonomy.yaml` → `_system/` へ移動
- `skill-template.yaml` → `_system/templates/` へ移動
- 各種ツールスクリプトを `_system/tools/` に配置

### Phase 1: 既存スキルの移行（1-2日）

#### 1.1 スキルの移動マッピング
| 現在の場所 | 移動先 |
|-----------|--------|
| license-application-generator | legal-professionals/gyosei-shoshi/ |
| contract-template-generator | legal-professionals/gyosei-shoshi/ |
| company-formation-kit | legal-professionals/gyosei-shoshi/ |
| social-insurance-calculator | labor-professionals/sharoushi/ |
| labor-insurance-updater | labor-professionals/sharoushi/ |
| work-rules-comparator | labor-professionals/sharoushi/ |
| tax-return-assistant | financial-professionals/zeirishi/ |
| expense-categorizer | financial-professionals/zeirishi/ |
| monthly-report-generator | financial-professionals/zeirishi/ |

#### 1.2 メタデータの追加
各スキルに`SKILL.yaml`を追加（既存の`SKILL.md`は保持）

### Phase 2: 自動化ツールの開発（3-5日）

#### 2.1 スキル移行ツール
```javascript
// migrate-skills.js
const migrationMap = {
  'license-application-generator': {
    category: 'legal-professionals',
    profession: 'gyosei-shoshi',
    tags: {
      function: ['document-generation', 'validation'],
      business_process: ['license-application'],
      impact: ['time-saving', 'error-reduction'],
      technology: ['pdf-processing', 'template-engine']
    }
  },
  // ... 他のスキル
};

function migrateSkill(skillId) {
  // 1. スキルを新しい場所に移動
  // 2. SKILL.yamlを生成
  // 3. インデックスを更新
}
```

#### 2.2 インデックス生成ツール
```javascript
// generate-index.js
function generateSkillIndex() {
  // 全スキルをスキャン
  // skill-index.jsonを生成
  // タグクラウドを更新
}
```

#### 2.3 検索ツール
```javascript
// search-skills.js
function searchSkills(query) {
  // 職業でフィルタリング
  // タグでフィルタリング
  // スコアリングして返却
}
```

### Phase 3: 検証とテスト（2-3日）

#### 3.1 移行検証チェックリスト
- [ ] すべてのスキルが正しい場所に移動されているか
- [ ] SKILL.yamlが適切に生成されているか
- [ ] 既存のSKILL.mdが保持されているか
- [ ] インデックスが正しく生成されているか
- [ ] 検索機能が期待通り動作するか

#### 3.2 品質保証
- タグの一貫性チェック
- メタデータの完全性確認
- リンク切れのチェック

### Phase 4: ドキュメントとトレーニング（1-2日）

#### 4.1 ユーザーガイドの作成
- 新しい構造の説明
- 検索方法のガイド
- タグ付けのベストプラクティス

#### 4.2 開発者ガイド
- 新しいスキルの追加方法
- タグの選び方
- メタデータの記入方法

## 移行スクリプト例

### 単一スキルの移行
```bash
#!/bin/bash
# migrate-single-skill.sh

SKILL_NAME=$1
OLD_PATH="professional-skills/${SKILL_NAME}"
NEW_PATH=$(determine_new_path ${SKILL_NAME})

# ディレクトリを移動
mkdir -p ${NEW_PATH}
mv ${OLD_PATH}/* ${NEW_PATH}/

# SKILL.yamlを生成
generate_skill_yaml ${SKILL_NAME} > ${NEW_PATH}/SKILL.yaml

# インデックスを更新
update_index ${SKILL_NAME} ${NEW_PATH}
```

### バッチ移行
```javascript
// batch-migrate.js
const skills = [
  'license-application-generator',
  'social-insurance-calculator',
  // ... 全スキル
];

async function migrateAll() {
  for (const skill of skills) {
    console.log(`Migrating ${skill}...`);
    await migrateSkill(skill);
    console.log(`✓ ${skill} migrated successfully`);
  }
  
  // インデックスを再生成
  await generateIndex();
  console.log('✓ Index regenerated');
}
```

## リスク管理

### 潜在的なリスクと対策
1. **データ損失リスク**
   - 対策: 移行前に完全バックアップを作成
   
2. **依存関係の破損**
   - 対策: リダイレクト設定を用意
   
3. **ダウンタイム**
   - 対策: 並行稼働期間を設ける

## 成功指標

### 定量的指標
- スキル検索時間: 5秒 → 1秒以下
- タグによる絞り込み精度: 90%以上
- システム管理時間: 50%削減

### 定性的指標
- ユーザーの検索体験向上
- 新規スキル追加の容易さ
- システムの拡張性確保

## タイムライン

```
Week 1:
月: Phase 0 - 準備
火-水: Phase 1 - 既存スキルの移行
木-金: Phase 2 - ツール開発開始

Week 2:
月-火: Phase 2 - ツール開発完了
水-木: Phase 3 - 検証とテスト
金: Phase 4 - ドキュメント作成

Week 3:
月: 本番移行
火-水: モニタリングと調整
```

## 次のアクション

### 即座に実行可能なタスク
1. ディレクトリ構造の作成
2. skill-taxonomy.yamlの最終確認
3. 最初のスキル（license-application-generator）の試験的移行

### 承認が必要な項目
1. 全体的な移行計画の承認
2. ツール開発のリソース割り当て
3. 移行スケジュールの確定

## 付録: コマンド例

### 新構造でスキルを作成
```bash
# 行政書士の新しいスキルを作成
claude-code "legal-professionals/gyosei-shoshi/に新しいスキル'visa-application-helper'を作成してください"
```

### タグで検索
```bash
# 時間削減効果のあるスキルを検索
claude-code "time-savingタグを持つスキルをリストアップしてください"
```

### 職業別レポート
```bash
# 税理士向けスキルの利用統計
claude-code "税理士向けスキルの効果測定レポートを生成してください"
```