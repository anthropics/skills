# Manual Generator

業務マニュアル・手順書の自動生成Agent Skill

## 概要

複数の入力形式（テキスト、スクリーンショット、既存マニュアル）から、プロフェッショナルなWord形式のマニュアルを自動生成します。

## 機能

### 対応マニュアルタイプ

| タイプ | コマンド | 用途 |
|--------|----------|------|
| システム操作 | `--type system` | 画面操作、入力手順、エラー対応 |
| 業務フロー | `--type workflow` | 業務手順、判断基準、承認フロー |
| 接客・窓口 | `--type service` | トークスクリプト、FAQ、対応事例 |

### 業種別オプション

| 業種 | コマンド | 特徴 |
|------|----------|------|
| 金融機関 | `--industry finance` | セキュリティ・コンプラ項目自動挿入 |
| 協同組合 | `--industry cooperative` | 平易化オプション対応 |
| 一般企業 | `--industry general` | 標準フォーマット |

### 対象者レベル

| レベル | コマンド | 特徴 |
|--------|----------|------|
| 新人向け | `--audience beginner` | 基礎から丁寧に解説 |
| 経験者向け | `--audience experienced` | 効率重視の解説 |
| 管理者向け | `--audience manager` | 運用管理・例外対応中心 |

## スクリプト構成

| スクリプト | 用途 |
|-----------|------|
| `manual_generator.js` | 新規マニュアル生成（メイン） |
| `content_extractor.js` | PDF/Wordからコンテンツ抽出 |
| `manual_rewriter.js` | 既存マニュアルのリライト |

## 使用方法

### 新規マニュアル生成

```bash
node scripts/manual_generator.js \
  --type <system|workflow|service> \
  --title "マニュアルタイトル" \
  --industry <finance|cooperative|general> \
  --audience <beginner|experienced|manager> \
  --version "1.0" \
  --output /path/to/output.docx
```

### 画像付きマニュアル生成

```bash
node scripts/manual_generator.js \
  --type system \
  --title "システム操作マニュアル" \
  --steps-json /path/to/steps.json \
  --output /path/to/output.docx
```

### 既存マニュアルのリライト

```bash
# PDF/Wordから直接リライト
node scripts/manual_rewriter.js \
  --input /path/to/old_manual.docx \
  --output /path/to/new_manual.docx \
  --industry cooperative \
  --version "2.0"

# 構造抽出のみ（デバッグ用）
node scripts/content_extractor.js \
  /path/to/old_manual.docx \
  /path/to/extracted.json
```

## 出力構成

### 共通構成

1. 表紙（タイトル、バージョン、作成者、機密区分）
2. 目次
3. はじめに（目的、対象者、適用範囲、関連文書）
4. メインコンテンツ（タイプ別）
5. 注意事項（セキュリティ、コンプラ、禁止事項）
6. FAQ / トラブルシューティング
7. 問い合わせ先
8. 改訂履歴

## デザイン

Jony Iveデザインシステム準拠

- フォント: メイリオ
- カラー: グレースケール基調 + アクセントブルー（#5B7B94）
- レイアウト: A4縦、余白25mm
- タイトル分割: 意味のある単位で自動改行

## 関連スキル

- `jony-ive-design-system` - デザインガイドライン
- `comparison-table-v2` - 新旧対比表生成（改訂時の差分表示）
- `docx` - Word生成の基本スキル

## バージョン履歴

- v1.2 (2025-12-01): 既存マニュアルリライト機能追加
- v1.1 (2025-12-01): 画像埋め込み機能追加、タイトル分割ルール追加
- v1.0 (2025-12-01): 初版リリース
