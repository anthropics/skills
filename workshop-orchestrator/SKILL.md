---
name: workshop-orchestrator
description: |
  ワークショップ参加者のGoogleスプレッドシート（CSV）を読み取り、
  各参加者の職業・ペインに応じたシンデレラフィットAgent Skillsを5個ずつパラレル生成する。
  ライブデモ用オーケストレーションスキル。

  トリガー:
  - 「ワークショップスキル生成を開始」
  - 「参加者スプレッドシートからスキルを作成」
  - 「CSVから参加者スキルを生成して」
---

# Workshop Orchestrator

ワークショップ参加者向けAgent Skillsを一括パラレル生成するオーケストレーター。

## Purpose

Googleスプレッドシートに記入された参加者情報（名前・職業・ペイン）を読み取り、
各参加者に最適化された5つのAgent Skillsを並列で自動生成する。

## Workflow

### Phase 1: スプレッドシート取得

**方法A: CSVファイル指定**
```
ユーザーからCSVファイルパスを受け取る
```

**方法B: GoogleスプレッドシートURL**
```
1. スプレッドシートの「共有」設定を「リンクを知っている全員」に変更
2. 以下の形式でCSVエクスポートURLを構築:
   https://docs.google.com/spreadsheets/d/{SPREADSHEET_ID}/export?format=csv
3. WebFetchでダウンロード
```

### Phase 2: 参加者データ解析

**期待するCSV形式:**
```csv
名前,職業,ペイン
山田太郎,ソフトウェアエンジニア,コードレビューに時間がかかりすぎる
佐藤花子,マーケター,レポート作成が毎週面倒
田中一郎,デザイナー,デザインシステムの管理が複雑
```

**解析処理:**
1. CSVをパース（`scripts/parse_spreadsheet.py`使用可）
2. 各行から参加者情報を抽出
3. 職業とペインの妥当性チェック

### Phase 3: パラレルスキル生成

**CRITICAL: Taskツールで並列実行**

各参加者に対して、以下の形式でTaskツールを**同時に複数起動**する:

```
参加者1, 参加者2, 参加者3... を同時にTask起動

各Taskのプロンプト:
「profession-skill-generatorスキルを使用して、
以下の参加者向けにシンデレラフィット Agent Skills を5個生成してください。

参加者情報:
- 名前: {name}
- 職業: {profession}
- ペイン: {pain}

出力先: /home/user/skills/generated/{name}/
」
```

**パラレル実行のポイント:**
- 1つのメッセージで複数のTaskツールを呼び出す
- 各Taskは独立して実行される
- 全員分が完了するまで待機

### Phase 4: 結果集約

1. 各参加者の生成されたスキルを確認
2. サマリーレポートを作成:

```markdown
# ワークショップスキル生成結果

## 参加者別生成スキル一覧

### 山田太郎 (ソフトウェアエンジニア)
1. code-review-assistant - コードレビュー自動化
2. pr-summary-generator - PR要約生成
3. ...

### 佐藤花子 (マーケター)
1. weekly-report-builder - 週次レポート自動生成
2. ...
```

## Input Requirements

- **CSVファイル** または **GoogleスプレッドシートURL**
- CSV列: `名前`, `職業`, `ペイン` (ヘッダー必須)
- 文字コード: UTF-8推奨

## Output Specification

各参加者ごとに以下を生成:
```
/home/user/skills/generated/{参加者名}/
├── skill-1/
│   └── SKILL.md
├── skill-2/
│   └── SKILL.md
├── skill-3/
│   └── SKILL.md
├── skill-4/
│   └── SKILL.md
└── skill-5/
    └── SKILL.md
```

## Example Usage

### デモシナリオ

```
司会者: 「では、スプレッドシートに職業とペインを記入してください」
（参加者が記入）

司会者: 「ワークショップスキル生成を開始」
Claude: 「CSVファイルまたはスプレッドシートURLを指定してください」

司会者: 「https://docs.google.com/spreadsheets/d/xxxxx」
Claude: 「5名の参加者を検出しました。パラレルでスキル生成を開始します...」
（5つのTaskが同時起動）

Claude: 「全員分の生成が完了しました！
- 山田太郎さん: 5スキル生成
- 佐藤花子さん: 5スキル生成
...」
```

## Constraints

- **DO**: パラレル実行で効率化
- **DO**: 各参加者の職業・ペインに最適化
- **DO NOT**: 同じスキルを複数参加者に使い回さない
- **DO NOT**: 汎用的すぎるスキルを生成しない

## Related Skills

- `profession-skill-generator`: 個別スキル生成サブエージェント（必須）
