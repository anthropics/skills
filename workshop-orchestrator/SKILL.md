---
name: workshop-orchestrator
description: |
  ワークショップ参加者のスプレッドシート（CSV）を読み取り、
  サブエージェントを最大限パラレル実行して全参加者のAgent Skillsを同時生成する。
  目標: 1人の生成時間 ≈ N人の生成時間（完全並列化）

  トリガー:
  - 「ワークショップスキル生成を開始」
  - 「参加者スプレッドシートからスキルを作成」
  - 「CSVから参加者スキルをパラレル生成」
---

# Workshop Orchestrator

ワークショップ参加者向けAgent Skillsを**最大限パラレル生成**するオーケストレーター。

## Core Principle: 完全並列化

```
目標: 1人の生成時間 ≈ N人の生成時間

従来（逐次処理）:
参加者1 → 参加者2 → 参加者3 → ... → 参加者N
[====]   [====]   [====]       [====]
合計時間: T × N

本スキル（完全並列）:
参加者1 [====]
参加者2 [====]  ← 同時実行
参加者3 [====]
...
参加者N [====]
合計時間: ≈ T（最も遅いタスクの時間）
```

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                  ORCHESTRATOR (このスキル)                   │
│                                                              │
│  1. CSV読み取り・解析                                        │
│  2. 全参加者分のTaskを【1メッセージで同時起動】              │
│  3. 全Task完了を待機                                         │
│  4. 結果集約・レポート生成                                   │
└─────────────────────────────────────────────────────────────┘
                              │
          ┌───────────────────┼───────────────────┐
          │                   │                   │
          ▼                   ▼                   ▼
    ┌──────────┐        ┌──────────┐        ┌──────────┐
    │  Task 1  │        │  Task 2  │        │  Task N  │
    │ 参加者A  │        │ 参加者B  │   ...  │ 参加者N  │
    │          │        │          │        │          │
    │ profession│        │ profession│        │ profession│
    │ -skill-  │        │ -skill-  │        │ -skill-  │
    │ generator│        │ generator│        │ generator│
    └──────────┘        └──────────┘        └──────────┘
          │                   │                   │
          ▼                   ▼                   ▼
    ┌──────────┐        ┌──────────┐        ┌──────────┐
    │ ZIP出力  │        │ ZIP出力  │        │ ZIP出力  │
    └──────────┘        └──────────┘        └──────────┘

    ← ─ ─ ─ ─ ─ ─ 完全並列実行 ─ ─ ─ ─ ─ ─ →
```

## Workflow

### Phase 1: スプレッドシート取得・解析

**入力方法:**

A) **CSVファイル直接指定**
```
ユーザー: 「/path/to/participants.csv を使って」
```

B) **Googleスプレッドシート URL**
```
1. スプレッドシートの共有設定を「リンクを知っている全員が閲覧可」に変更
2. URLを取得: https://docs.google.com/spreadsheets/d/{ID}/edit
3. CSVエクスポートURL自動構築: .../export?format=csv
4. WebFetchでダウンロード
```

**CSV形式:**
```csv
名前,職業,ペイン
山田太郎,ソフトウェアエンジニア,コードレビューに時間がかかりすぎる
佐藤花子,マーケター,レポート作成が毎週面倒
田中一郎,デザイナー,デザインシステムの管理が複雑
鈴木次郎,セミナー企画運営,業務フローが確立されていない
```

**解析処理:**
```python
# scripts/parse_spreadsheet.py を使用
python scripts/parse_spreadsheet.py participants.csv
# → JSON形式で参加者リストを出力
```

### Phase 2: パラレルTask起動【最重要】

**CRITICAL: 1メッセージで全参加者分のTaskを同時起動**

```
┌─────────────────────────────────────────────────────────────┐
│ 【重要】Taskツールの並列実行ルール                          │
│                                                              │
│ ・1つのメッセージ内で複数のTaskツールを呼び出すと並列実行   │
│ ・各Taskは独立したサブエージェントとして同時に動作          │
│ ・全Taskの完了を待ってから次のフェーズへ                    │
└─────────────────────────────────────────────────────────────┘
```

**実装パターン:**

N人の参加者がいる場合、**1つのアシスタントメッセージ内でN個のTaskツールを同時に呼び出す**。

各Taskのパラメータ:
```yaml
subagent_type: general-purpose
description: "{参加者名}スキル生成"
prompt: |
  profession-skill-generatorスキルの指示に従って、
  以下の参加者向けに5機能統合Agent Skillを生成し、ZIP化してください。

  ## 参加者情報
  - 名前: {name}
  - 職業: {profession}
  - ペイン: {pain}
  - 出力先: /home/user/skills/generated/

  ## 実行内容
  profession-skill-generatorのPhase 1〜7を実行:
  1. 5軸特性分析
  2. 7業務カテゴリー動的生成
  3. 35項目AI活用分析
  4. Agent Skill提案（8-12候補）
  5. 5機能選定
  6. 統合SKILL.md生成
  7. ZIP生成

  ## 出力
  - {name}-ai-assistant/SKILL.md
  - {name}-ai-assistant.zip

  ## 報告
  完了したら以下を報告:
  - 生成したスキル名
  - 5機能の一覧（機能名とトリガー）
  - ZIPファイルパス
```

**並列実行の例（5人の参加者）:**

```
1つのメッセージで5つのTaskツールを同時呼び出し:

Task 1: 山田太郎（エンジニア）     ─┐
Task 2: 佐藤花子（マーケター）     ─┼─ 同時並列実行
Task 3: 田中一郎（デザイナー）     ─┤
Task 4: 鈴木次郎（セミナー企画）   ─┤
Task 5: 高橋三郎（営業）           ─┘

→ 5人分が1人分とほぼ同じ時間で完了
```

### Phase 3: 結果収集・検証

各Taskの完了後:
1. 全Taskの成功/失敗を確認
2. 生成されたZIPファイルの存在確認
3. 失敗したTaskがあれば再実行（個別に）

```bash
# 生成確認
ls -la /home/user/skills/generated/*.zip
```

### Phase 4: サマリーレポート生成

**出力形式:**

```markdown
# ワークショップスキル生成結果

## 実行サマリー
- 参加者数: {N}名
- 成功: {成功数}名
- 失敗: {失敗数}名
- 実行時間: 約{時間}（並列実行）

## 参加者別生成スキル一覧

### 1. 山田太郎 (ソフトウェアエンジニア)
**ペイン**: コードレビューに時間がかかりすぎる
**生成スキル**: yamada-taro-ai-assistant.zip
| # | 機能名 | トリガー |
|---|--------|----------|
| 1 | コードレビュー要約 | 「PRを要約して」 |
| 2 | チェックリスト生成 | 「レビュー観点を出して」 |
| 3 | コードスメル検出 | 「問題点を探して」 |
| 4 | コメント下書き | 「コメントを書いて」 |
| 5 | PR説明文改善 | 「説明文を改善して」 |

### 2. 佐藤花子 (マーケター)
...

## 配布用ZIPファイル一覧
| 参加者 | ファイル | サイズ |
|--------|----------|--------|
| 山田太郎 | yamada-taro-ai-assistant.zip | 5KB |
| 佐藤花子 | sato-hanako-ai-assistant.zip | 5KB |
| ... | ... | ... |

## 配布方法
1. 上記ZIPファイルを参加者に配布
2. 参加者はClaude.ai → Settings → Custom Skills でアップロード
3. スキルをオンにして利用開始
```

## 最適化ポイント

### 並列度の最大化

```
【推奨】全参加者を1メッセージで同時起動

・10人以下: 全員同時起動（問題なし）
・11-20人: 全員同時起動（推奨）
・20人超: バッチ分割も検討（ただし並列度は維持）
```

### 各サブエージェントの効率化

```
profession-skill-generatorの各Phaseは:
- Phase 1-5: 分析・設計（テキスト生成のみ、高速）
- Phase 6: SKILL.md生成（Writeツール1回）
- Phase 7: ZIP生成（Bashツール1回）

→ I/Oは最小限、ほぼ計算のみなので高速
```

### 失敗時のリカバリー

```
失敗したTaskのみ個別に再実行:

if task_failed:
    # 失敗した参加者のみ再度Taskを起動
    Task(subagent_type="general-purpose", prompt="...")
```

## Input Requirements

- **CSVファイル** または **GoogleスプレッドシートURL**
- CSV列: `名前`, `職業`, `ペイン` (ヘッダー必須)
- 文字コード: UTF-8推奨

## Output Specification

```
/home/user/skills/generated/
├── yamada-taro-ai-assistant/
│   └── SKILL.md
├── yamada-taro-ai-assistant.zip
├── sato-hanako-ai-assistant/
│   └── SKILL.md
├── sato-hanako-ai-assistant.zip
├── ...
└── WORKSHOP_SUMMARY.md  ← 全体サマリー
```

## Example Demo Script

```
【デモ進行】

1. 司会者: 「スプレッドシートに職業とペインを記入してください」
   → 参加者が記入（2-3分）

2. 司会者: 「ワークショップスキル生成を開始」
   Claude: 「CSVまたはスプレッドシートURLを指定してください」

3. 司会者: スプレッドシートURLを貼り付け
   Claude: 「8名の参加者を検出しました」
   Claude: 「全員分のスキル生成をパラレルで開始します...」

   → 8つのTaskが同時起動（画面に8つの処理が並行して表示）

4. Claude: 「全員分の生成が完了しました！（約2分）」

   生成結果サマリー:
   - 山田太郎さん: yamada-taro-ai-assistant.zip ✅
   - 佐藤花子さん: sato-hanako-ai-assistant.zip ✅
   - ...

5. 司会者: 各参加者にZIPファイルを配布
   参加者: Claude.aiにアップロードして即利用開始
```

## Constraints

- **DO**: 1メッセージで全参加者分のTaskを同時起動
- **DO**: 各Taskは独立・並列で実行
- **DO**: 失敗時は該当Taskのみ再実行
- **DO NOT**: 参加者を1人ずつ順番に処理しない
- **DO NOT**: Taskの完了を待ってから次のTaskを起動しない
- **DO NOT**: 並列度を人為的に制限しない

## Related Skills

- `profession-skill-generator`: 個別参加者のスキル生成サブエージェント（必須）
