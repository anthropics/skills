# Meeting to Tasksheet Agent Skill（動的関数版 v2）

会議の音声入力・テキストから議事録とタスク管理表を自動生成するAgent Skillです。

## 🆕 v2.0の新機能

### 完全動的Excel関数版

**タスク一覧のステータスを変更するだけで、全シートが自動的に再計算されます！**

| 機能 | 従来版 | v2.0 動的関数版 |
|------|--------|----------------|
| 進捗サマリー | 生成時の固定値 | COUNTIF/SUMPRODUCT関数で自動更新 |
| ガントチャート色 | Python側で指定 | 条件付き書式でステータス連動 |
| 期限状況 | 生成時点 | TODAY()で常に最新 |
| 残日数 | 手計算 | =IF(H="完了","-",F-TODAY()) |

### 日付自動推定機能

会議内容から実際の日付を自動推定・抽出します:

| 発言内容 | 自動推定される日付 |
|---------|-----------------|
| 「年度内に完成」 | → 3月31日 |
| 「来月までに」 | → 翌月末 |
| 「3ヶ月後にリリース」 | → 会議日+3ヶ月 |
| 「11月～12月に作成」 | → 11/1開始、12/31期限 |

## インストール方法

### 1. スキルディレクトリの作成

```bash
mkdir -p ~/.claude/skills/meeting-to-tasksheet/scripts
```

### 2. ファイルの配置

以下のファイルを配置してください:

```
~/.claude/skills/meeting-to-tasksheet/
├── SKILL.md                                    # スキル定義ファイル
├── README.md                                   # このファイル
├── INSTALL.md                                  # インストールガイド
└── scripts/
    ├── generate_meeting_tasksheet.py           # シンプル版
    └── generate_meeting_tasksheet_rich.py      # リッチ版（推奨）
```

### 3. 依存ライブラリのインストール

```bash
pip install openpyxl --break-system-packages
```

## 使い方

### 基本的な使い方

Claudeに会議の文字起こしを渡すだけです:

```
この会議の文字起こしから議事録を作成して

[文字起こしテキストを貼り付け]
```

### 出力される内容

6シート構成のExcelファイル:

1. **議事録** - 会議の基本情報、前回の宿題、議論サマリー、決定事項
2. **タスク一覧** - ドロップダウン選択、残日数自動計算、期限アラート
3. **ガントチャート** - ステータス連動色、今週ハイライト、マイルストーン
4. **進捗サマリー** - 完了率、ステータス別・優先度別・担当者別集計（全て動的）
5. **リスク・課題** - リスクレベル管理、高リスク自動ハイライト
6. **Slack投稿用** - マークダウン/プレーンテキスト

## 動的関数の例

### タスク一覧でステータスを変更すると...

1. **進捗サマリー**の完了率が自動更新
2. **ガントチャート**のバーの色が自動変化
3. **期限状況**の件数が自動更新
4. **Slack投稿用**の進捗表示が自動更新

### 使用されている関数

```excel
# 完了率
=TEXT(COUNTIF(タスク一覧!H5:H14,"完了")/10,"0%")

# 期限超過タスク数
=SUMPRODUCT((タスク一覧!F5:F14<TODAY())*(タスク一覧!H5:H14<>"完了"))

# 担当者別工数
=SUMIF(タスク一覧!D5:D14,A24,タスク一覧!J5:J14)

# 残日数
=IF(H5="完了","-",F5-TODAY())
```

## コマンドラインでの使用

```bash
# デモモード（サンプルデータで試す）
python scripts/generate_meeting_tasksheet_rich.py --demo --output demo.xlsx

# JSONファイルから生成
python scripts/generate_meeting_tasksheet_rich.py --json meeting_data.json --output result.xlsx
```

## JSONデータ形式

```json
{
  "meeting_info": {
    "title": "プロジェクト定例会議",
    "datetime": "2025年1月15日 14:00-15:30",
    "location": "会議室A",
    "attendees": "田中、佐藤、鈴木",
    "recorder": "鈴木",
    "meeting_no": 1
  },
  "summary": "システム開発の進捗を確認。リリース日程を2月20日に決定。",
  "decisions": [
    "リリース日: 2025年2月20日",
    "テスト期間: 2週間確保"
  ],
  "tasks": [
    {
      "name": "テスト環境構築",
      "assignee": "田中",
      "start_date": "2025-01-15",
      "due_date": "2025-01-25",
      "status": "未着手",
      "priority": "高",
      "estimated_hours": 8
    }
  ],
  "risks": [
    {
      "type": "リスク",
      "content": "ネットワーク不安定",
      "level": "高",
      "impact": "デモ失敗",
      "countermeasure": "モバイルルーター準備",
      "assignee": "田中",
      "due_date": "2025-01-20",
      "status": "未対応"
    }
  ],
  "next_meeting": {
    "datetime": "2025年2月5日 14:00",
    "agenda": "進捗確認"
  },
  "prev_action_items": [
    {
      "content": "要件定義書の確認",
      "assignee": "佐藤",
      "status": "完了"
    }
  ]
}
```

## トラブルシューティング

### 日付が正しく推定されない

会議開催日が不明確な場合、以下の情報を追加してください:

```
会議日：2025年1月15日
[文字起こしテキスト]
```

### タスクの期限を手動調整したい

生成されたExcelファイルを直接編集できます。ステータスを変更すると、進捗サマリーも自動的に更新されます。

### 数式が計算されない

LibreOfficeがインストールされている場合、recalc.pyで再計算できます:

```bash
python /mnt/skills/public/xlsx/recalc.py output.xlsx 60
```

## ライセンス

このAgent Skillは自由に使用・改変できます。

## バージョン履歴

- **v2.0** (2025-11): 動的関数版リリース（COUNTIF/SUMPRODUCT/条件付き書式）
- **v1.5** (2025-01): 日付自動推定機能を追加
- **v1.0** (2024): 初版リリース

## 関連スキル

- **sales-analyzer-xlsx**: 売上データ分析
- **shift-scheduler**: シフト表自動生成
