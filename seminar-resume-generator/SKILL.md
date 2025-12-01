---
name: seminar-resume-generator
description: 勉強会・セミナー用のレジュメ（配布資料・ハンドアウト）をWord形式で自動生成。タイトル・日時、学習目標、タイムテーブル、事前準備、参考リンク、メモ欄を含むテンプレート。Jony Iveデザイン（グレースケール基調、メイリオフォント）で請求書・見積書と統一。「勉強会のレジュメを作成」「セミナー資料を作って」「ハンドアウトを準備」「研修の配布資料」等のリクエストで使用。
---

# Seminar Resume Generator

## Overview

勉強会・セミナー参加者向けの配布資料（レジュメ/ハンドアウト）をWord形式で自動生成するスキル。Jony Iveデザイン哲学に基づくミニマルなデザインで、他のビジネス文書（請求書・見積書・契約書等）と統一感のある出力を提供。

## 使用方法

### 基本ワークフロー

1. **情報確認**: ユーザーに以下の情報を確認
   - 勉強会タイトル
   - サブタイトル（任意）
   - 日時・場所
   - 講師名
   - 学習目標（箇条書き）
   - タイムテーブル（時間と内容）
   - 事前準備事項
   - 参考リンク・資料

2. **スクリプト実行**: `scripts/create_resume.js`をカスタマイズして実行

3. **出力**: `/mnt/user-data/outputs/`にWordファイルを出力

### スクリプトのカスタマイズ

`scripts/create_resume.js`の`RESUME_DATA`セクションを編集：

```javascript
const RESUME_DATA = {
  // 基本情報
  mainTitle: "生成AI勉強会",
  subTitle: "【タイトル】業務効率化のためのClaude活用術",
  date: "2025年○月○日（○）14:00〜16:00",
  venue: "○○会議室 / オンライン（Zoom）",
  instructor: "○○ ○○（株式会社けんけん / MIRAICHI）",
  
  // 学習目標
  goals: [
    "生成AIの基本概念と活用シーンを理解する",
    "Claudeの特徴と他のAIツールとの違いを把握する",
    "実務で使えるプロンプトの書き方を身につける",
    "自社業務への適用イメージを具体化する"
  ],
  
  // タイムテーブル
  timetable: [
    { time: "14:00-14:10", content: "オープニング・自己紹介" },
    { time: "14:10-14:40", content: "生成AIの基礎知識" },
    { time: "14:40-15:10", content: "Claude活用デモンストレーション" },
    { time: "15:10-15:20", content: "休憩", isBreak: true },
    { time: "15:20-15:50", content: "ハンズオン：プロンプト実践" },
    { time: "15:50-16:00", content: "質疑応答・クロージング" }
  ],
  
  // 事前準備
  preparations: [
    "Claudeアカウントの作成（https://claude.ai）",
    "PC（Chrome推奨）またはスマートフォンの持参",
    "Wi-Fi接続環境の確認"
  ],
  
  // 参考リンク
  references: [
    "Claude公式サイト: https://claude.ai",
    "Anthropic公式ドキュメント: https://docs.anthropic.com",
    "プロンプトエンジニアリングガイド: https://docs.anthropic.com/en/docs/build-with-claude/prompt-engineering"
  ],
  
  // ヘッダー・フッター
  headerText: "株式会社けんけん / MIRAICHI",
  footerNote: "本資料の無断複製・転載を禁じます。"
};
```

### 実行方法

```bash
node scripts/create_resume.js
```

## レジュメ構成

生成されるレジュメには以下のセクションが含まれる：

1. **ヘッダー**: 会社名（右上）
2. **タイトルブロック**: メインタイトル＋サブタイトル
3. **基本情報テーブル**: 日時・場所・講師（2列レイアウト）
4. **学習目標・ゴール**: 導入文＋箇条書きリスト
5. **タイムテーブル**: 時間×内容の表形式
6. **事前準備事項**: 番号付きリスト
7. **参考リンク・資料**: 箇条書きリスト
8. **メモ欄**: 書き込み用の空白枠
9. **フッター**: ページ番号＋著作権表示

## デザイン仕様（Jony Iveデザイン哲学）

### デザイン原則
**"Simplicity is the ultimate sophistication"**

1. **極限までシンプルに** - 不要な装飾を徹底的に排除
2. **余白を贅沢に使う** - 情報に呼吸する空間を与える
3. **完璧な整列** - すべての要素を精密に配置
4. **控えめな色使い** - グレースケール基調、アクセントは最小限
5. **階層の明確化** - フォントサイズで情報の重要度を表現

### 配色（グレースケール）

| 用途 | HEX | 使用場面 |
|------|-----|----------|
| ブラック | #000000 | メインタイトル |
| ダークグレー | #333333 | 本文、セクション見出し |
| ミディアムグレー | #666666 | サブタイトル、ラベル |
| ライトグレー | #999999 | 補足情報、休憩行 |
| セパレーター | #E0E0E0 | 区切り線、罫線 |
| 背景グレー | #F5F5F5 | テーブルヘッダー背景 |
| ホワイト | #FFFFFF | 基本背景 |

### フォント（メイリオ統一）

| レベル | サイズ | 用途 |
|--------|--------|------|
| 28pt | Bold | メインタイトル |
| 14pt | Bold | セクション見出し |
| 12pt | Regular | サブタイトル |
| 10pt | Regular | 本文 |
| 9pt | Regular | 補足情報、ヘッダー/フッター |

### レイアウト

- **余白**: 約2cm（1134 DXA）
- **罫線**: 最小限（薄いグレーのみ）
- **配置**: すべて左揃え（中央揃えは使わない）
- **行間**: 適度な余白で読みやすく

## カスタマイズオプション

### タイムテーブルの行追加

```javascript
timetable: [
  { time: "10:00-10:30", content: "セッション1" },
  { time: "10:30-11:00", content: "セッション2" },
  // 必要に応じて追加
]
```

### 休憩行のスタイル

休憩は`isBreak: true`を設定するとライトグレーで表示：
```javascript
{ time: "15:10-15:20", content: "休憩", isBreak: true }
```

### メモ欄のサイズ調整

```javascript
// 行の高さ（DXA単位、3600 = 約2.5インチ）
height: { value: 3600, rule: "exact" }
```

### PDF変換

Word出力後、LibreOfficeでPDFに変換可能：
```bash
soffice --headless --convert-to pdf 勉強会レジュメ.docx --outdir /mnt/user-data/outputs/
```

## 技術仕様

- **ライブラリ**: docx（Node.js）
- **フォント**: メイリオ
- **用紙サイズ**: A4
- **出力形式**: .docx
- **出力場所**: `/mnt/user-data/outputs/`

## 使用例

### 例1: 生成AI勉強会
```bash
# RESUME_DATAを編集後
node scripts/create_resume.js
```
→ 生成AI勉強会用のレジュメを作成

### 例2: DX研修
RESUME_DATAを以下のように変更：
```javascript
mainTitle: "DX推進研修",
subTitle: "【基礎編】業務プロセスのデジタル化",
// ... その他の項目を適宜変更
```

### 例3: 社内勉強会
ヘッダーを社内向けに変更：
```javascript
headerText: "社内限り",
footerNote: "本資料は社外秘です。"
```

## Resources

### scripts/
- `create_resume.js`: レジュメ作成のメインスクリプト

### references/
- `design_system.md`: Jony Iveデザインシステムの詳細
