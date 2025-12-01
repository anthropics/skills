# Mermaid Flow Generator

Mermaid記法を使用したフロー図・ダイアグラム自動生成Agent Skill

## 概要

テキスト説明や手順からプロフェッショナルなフロー図を自動生成します。

## 対応図表タイプ

| タイプ | 用途 | 例 |
|--------|------|-----|
| flowchart | 業務フロー、処理手順 | 申請→承認→完了 |
| sequence | システム連携、API呼び出し | ユーザー→API→DB |
| swimlane | 部門横断フロー | 営業→経理→物流 |
| state | 状態遷移、ステータス管理 | 下書き→申請中→承認済 |

## 使用方法

### テキストからフロー図生成

```bash
node scripts/generate_diagram.js \
  --type flowchart \
  --input "申請→承認→完了" \
  --output /mnt/user-data/outputs/flow.png
```

### Mermaidファイルから画像生成

```bash
node scripts/mermaid_to_image.js \
  --input /path/to/diagram.mmd \
  --output /path/to/diagram.png \
  --format png
```

### オプション

| オプション | 説明 | デフォルト |
|-----------|------|----------|
| `--type` | 図表タイプ | flowchart |
| `--input` | テキストまたはファイル | - |
| `--output` | 出力ファイル | diagram.png |
| `--format` | 出力形式（png/svg） | png |
| `--direction` | フロー方向（TD/LR） | TD |
| `--theme` | テーマ（default/jony-ive） | jony-ive |

## テンプレート

| ファイル | 内容 |
|---------|------|
| `templates/flowchart_basic.mmd` | 基本フローチャート |
| `templates/sequence_api.mmd` | API連携シーケンス図 |
| `templates/swimlane_approval.mmd` | 承認フロー（スイムレーン） |
| `templates/state_order.mmd` | 注文状態遷移図 |

## デザイン

Jony Iveデザインシステム準拠

- グレースケール基調
- アクセントカラー: #5B7B94
- フォント: メイリオ

## 変換方法

複数の変換方法をサポート（自動フォールバック）:

1. **mermaid-cli** - ローカル変換（高品質）
2. **Kroki API** - Web API（インストール不要）
3. **Puppeteer** - ブラウザレンダリング（最終手段）

## 依存関係

```bash
# mermaid-cli（推奨）
npm install -g @mermaid-js/mermaid-cli

# または Kroki API使用（インストール不要）
```

## 他スキルとの連携

- `manual-generator` - 業務フローマニュアルに図を埋め込み
- `meeting-to-tasksheet` - 会議からプロセス図を生成
- `hearing-sheet-generator` - 現状業務フロー（As-Is）生成

## バージョン履歴

- v1.0 (2025-12-01): 初版リリース
