# Meeting to Tasksheet Agent Skill - インストールガイド（v2.0 動的関数版）

会議の音声入力・テキストから議事録とタスク管理表を自動生成するAgent Skillの完全版です。

## 🆕 v2.0の特徴

- **完全動的Excel関数版**: タスク一覧のステータス変更で全シート自動更新
- **COUNTIF/SUMPRODUCT関数**: 進捗サマリーを動的計算
- **条件付き書式**: ガントチャートのバー色をステータス連動
- **TODAY()関数**: 期限状況を常に最新表示

## 📦 パッケージ内容

```
meeting-to-tasksheet/
├── SKILL.md                                    # Agent Skill定義ファイル
├── README.md                                   # 使用方法ガイド
├── INSTALL.md                                  # このファイル
└── scripts/
    ├── generate_meeting_tasksheet.py           # シンプル版スクリプト
    └── generate_meeting_tasksheet_rich.py      # リッチ版スクリプト（推奨）
```

## 🚀 インストール手順

### ステップ1: ディレクトリ構造を作成

```bash
# Macの場合
mkdir -p ~/.claude/skills/meeting-to-tasksheet/scripts

# Windowsの場合（PowerShell）
New-Item -ItemType Directory -Path "$env:USERPROFILE\.claude\skills\meeting-to-tasksheet\scripts" -Force
```

### ステップ2: ファイルを配置

ダウンロードしたファイルを以下のように配置:

```
~/.claude/skills/meeting-to-tasksheet/
├── SKILL.md                    ← ダウンロードしたファイル
├── README.md                   ← ダウンロードしたファイル
├── INSTALL.md                  ← ダウンロードしたファイル
└── scripts/
    ├── generate_meeting_tasksheet.py         ← ダウンロードしたファイル
    └── generate_meeting_tasksheet_rich.py    ← ダウンロードしたファイル
```

**Mac/Linuxの場合:**
```bash
cd ~/.claude/skills/meeting-to-tasksheet/
# ダウンロードフォルダからファイルをコピー
cp ~/Downloads/SKILL.md ./
cp ~/Downloads/README.md ./
cp ~/Downloads/INSTALL.md ./
cp ~/Downloads/generate_meeting_tasksheet.py ./scripts/
cp ~/Downloads/generate_meeting_tasksheet_rich.py ./scripts/
```

**Windowsの場合（PowerShell）:**
```powershell
cd $env:USERPROFILE\.claude\skills\meeting-to-tasksheet\
# ダウンロードフォルダからファイルをコピー
Copy-Item "$env:USERPROFILE\Downloads\SKILL.md" -Destination ".\"
Copy-Item "$env:USERPROFILE\Downloads\README.md" -Destination ".\"
Copy-Item "$env:USERPROFILE\Downloads\INSTALL.md" -Destination ".\"
Copy-Item "$env:USERPROFILE\Downloads\generate_meeting_tasksheet.py" -Destination "scripts\"
Copy-Item "$env:USERPROFILE\Downloads\generate_meeting_tasksheet_rich.py" -Destination "scripts\"
```

### ステップ3: 実行権限を付与（Mac/Linuxのみ）

```bash
chmod +x ~/.claude/skills/meeting-to-tasksheet/scripts/*.py
```

### ステップ4: 依存ライブラリをインストール

```bash
pip install openpyxl --break-system-packages
```

**依存パッケージ:**
- `openpyxl` - Excel操作（必須）

### ステップ5: 動作確認

```bash
cd ~/.claude/skills/meeting-to-tasksheet/scripts/
python generate_meeting_tasksheet_rich.py --demo --output test.xlsx
```

`test.xlsx` が生成されれば成功です！

## 🎯 使い方

### Claudeで使用する

1. Claudeを起動
2. 会議の文字起こしを貼り付けて、以下のように依頼:

```
この会議の文字起こしから議事録とタスク管理表を作成して

[会議の文字起こしテキストをここに貼り付け]
```

3. Claudeが自動的にこのAgent Skillを使用して、6シート構成のExcelファイルを生成します

### コマンドラインで直接使用する

```bash
# デモモード（サンプルデータで試す）
python scripts/generate_meeting_tasksheet_rich.py --demo --output demo.xlsx

# JSONファイルから生成
python scripts/generate_meeting_tasksheet_rich.py --json meeting_data.json --output result.xlsx
```

## 🆕 v2.0の主な機能

### 動的関数版の特徴

タスク一覧のステータスを変更すると、以下が自動更新されます:

1. **進捗サマリー**: 完了率、ステータス別件数、担当者別集計
2. **ガントチャート**: バーの色（未着手=グレー、進行中=青、完了=緑、保留=オレンジ）
3. **期限状況**: 期限超過、今週期限、来週以降の件数
4. **Slack投稿用**: 進捗表示

### 使用Excel関数

| 関数 | 用途 |
|------|------|
| COUNTIF | ステータス別カウント |
| COUNTIFS | 複数条件カウント（優先度×ステータス） |
| SUMIF | 担当者別工数合計 |
| SUMPRODUCT | 配列計算（期限超過等） |
| TODAY() | 現在日付参照 |
| IF | 条件分岐（残日数、バー表示） |

### 日付自動推定

会議内容から実際の日付を自動推定します:

| 発言内容 | 自動推定される日付 |
|---------|-----------------|
| 「年度内に完成」 | → 3月31日 |
| 「来月までに」 | → 翌月末 |
| 「3ヶ月後にリリース」 | → 会議日+3ヶ月 |
| 「11月～12月に作成」 | → 11/1開始、12/31期限 |

### 6シート構成のExcel

1. **議事録** - 会議基本情報、前回の宿題、決定事項、次回予定
2. **タスク一覧** - ドロップダウン選択、残日数自動計算、期限アラート
3. **ガントチャート** - ステータス連動色、今週ハイライト、マイルストーン
4. **進捗サマリー** - 完了率、担当者別負荷（全てExcel関数）
5. **リスク・課題** - リスクレベル管理
6. **Slack投稿用** - コピペで即共有

## 📝 JSONデータ形式

```json
{
  "meeting_info": {
    "title": "プロジェクト定例会議",
    "datetime": "2025年1月15日 14:00-15:30",
    "location": "会議室A",
    "attendees": "田中さん、佐藤さん、鈴木さん",
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
      "estimated_hours": 8,
      "depends_on": "",
      "is_milestone": false,
      "notes": "AWS環境を使用"
    }
  ],
  "risks": [
    {
      "type": "リスク",
      "content": "テスト環境の準備遅延",
      "level": "高",
      "impact": "リリース延期の可能性",
      "countermeasure": "早急に着手、進捗を毎日確認",
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

## 🔧 トラブルシューティング

### Q: Agent Skillが認識されない

**A:** 以下を確認してください:

1. ファイルが正しい場所にあるか
   ```bash
   ls -la ~/.claude/skills/meeting-to-tasksheet/SKILL.md
   ```

2. SKILL.mdにYAMLフロントマターがあるか
   ```bash
   head -5 ~/.claude/skills/meeting-to-tasksheet/SKILL.md
   ```
   最初に `---` で始まる行があるはずです

3. Claudeを再起動してみる

### Q: スクリプトが実行できない

**A:** 実行権限を確認:
```bash
chmod +x ~/.claude/skills/meeting-to-tasksheet/scripts/*.py
```

### Q: 依存ライブラリがインストールできない

**A:** 以下を試してください:

```bash
# Macの場合
pip3 install openpyxl --break-system-packages

# 仮想環境を使う場合
python -m venv venv
source venv/bin/activate  # Windowsの場合: venv\Scripts\activate
pip install openpyxl
```

### Q: 日付が正しく推定されない

**A:** 会議開催日を明示してください:

```
会議日時: 2025年1月15日 14:00
場所: 会議室A

[文字起こしテキスト]
```

### Q: 数式が計算されない

**A:** LibreOfficeがインストールされている場合、recalc.pyで再計算できます:

```bash
python /mnt/skills/public/xlsx/recalc.py output.xlsx 60
```

### Q: タスク一覧を編集しても進捗サマリーが更新されない

**A:** v2.0では全てExcel関数で実装されているため、Excelで開けば自動更新されます。Google スプレッドシートでは一部関数が動作しない場合があります。

## 📚 関連リソース

- **OpenPyXLドキュメント**: https://openpyxl.readthedocs.io/
- **Claude Agent Skills公式ドキュメント**: https://docs.claude.com/

## 🆘 サポート

問題が発生した場合:

1. READMEを確認
2. このINSTALL.mdのトラブルシューティングを確認
3. ログファイルを確認（もしあれば）

## 📄 ライセンス

このAgent Skillは自由に使用・改変できます。

## 🔄 アップデート履歴

- **v2.0** (2025-11): 動的関数版リリース
  - 進捗サマリーを完全Excel関数化（COUNTIF/COUNTIFS/SUMIF/SUMPRODUCT）
  - ガントチャートを条件付き書式で動的色変更
  - 残日数の動的計算（=IF(H="完了","-",F-TODAY())）
  - 期限状況のTODAY()関数対応
- **v1.5** (2025-01): 日付自動推定機能を追加
- **v1.0** (2024): 初版リリース

---

インストールが完了したら、READMEを読んで使い方を確認してください！
