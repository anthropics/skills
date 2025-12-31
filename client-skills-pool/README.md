# Client Skills Pool

このディレクトリは、AI Advisor Workflowによって生成されたクライアント向けカスタムAgentSkillsのプールです。

## 概要

- **目的**: クライアント固有の要件に基づいて生成されたスキルを保存・管理
- **活用方法**: 新規スキル生成時に類似業種・用途のスキルを参考にする
- **昇格システム**: 汎用性が高く優秀なスキルはスタメン（`/skills/`）に昇格

## ディレクトリ構造

```
client-skills-pool/
├── ai-retail-inventory-optimizer/     # 小売業向け在庫最適化
├── ai-manufacturing-quality-checker/  # 製造業向け品質検査
├── ai-healthcare-appointment-bot/     # 医療業向け予約管理
└── ...
```

各スキルディレクトリには以下が含まれます：
- `SKILL.md` - スキル定義
- `scripts/` - 実装コード
- `pool_metadata.json` - プール管理用メタデータ

## pool_metadata.json の構造

```json
{
  "added_date": "2024-01-15T10:30:00",
  "proposal_title": "在庫管理AIの導入",
  "base_skill": "data-analyzer",
  "skill_type": "optimization",
  "usage_count": 5,
  "rating": 4.5,
  "starter_candidate": true,
  "client_info": {
    "industry": "小売業",
    "company_size": "medium"
  }
}
```

## スタメン昇格基準

以下の条件を満たすスキルはスタメン候補となります：

1. **汎用性**: 3つ以上の異なるクライアントで活用可能
2. **実績**: usage_count が10以上
3. **評価**: rating が4.0以上
4. **メンテナンス性**: コードが整理され、ドキュメントが充実

## 管理コマンド

```bash
# プール内のスキル一覧
ls -la client-skills-pool/

# スタメン候補の確認
find client-skills-pool -name "pool_metadata.json" -exec grep -l '"starter_candidate": true' {} \;

# 特定業種のスキル検索
find client-skills-pool -name "pool_metadata.json" -exec grep -l '"industry": "製造業"' {} \;
```

## 注意事項

- クライアント固有の機密情報は含めないこと
- 汎用化できる部分は積極的に抽象化する
- 定期的にレビューして不要なスキルは整理する