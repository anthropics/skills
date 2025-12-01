---
name: manual-generator
description: 業務マニュアル・手順書を自動生成するスキル。テキスト説明、スクリーンショット画像、既存マニュアル（PDF/Word）から、プロフェッショナルなWord形式のマニュアルを作成。システム操作、業務フロー、接客・窓口対応の3タイプに対応。金融機関向けコンプラ項目自動挿入、協同組合向け平易化オプション、改訂履歴・新旧対比表連携機能を搭載。「マニュアルを作成」「手順書を作って」「操作説明書を生成」「既存マニュアルをリライト」等のリクエストで使用。
---

# Manual Generator Skill

業務マニュアル・手順書の自動生成スキル。複数の入力形式に対応し、Jony Iveデザインシステムに準拠した統一フォーマットで出力。

## 概要

### 対応マニュアルタイプ

| タイプ | 特徴 | 主な構成要素 |
|--------|------|------------|
| **system** | システム操作マニュアル | 画面キャプチャ、操作手順、入力例、エラー対応 |
| **workflow** | 業務フローマニュアル | フロー図、判断基準、例外処理、承認ルート |
| **service** | 接客・窓口対応マニュアル | トークスクリプト、FAQ、対応事例、エスカレーション |

### 入力形式

1. **テキスト説明** → 構造化してマニュアル生成
2. **スクリーンショット画像** → 画像解析して操作説明を自動生成
3. **既存マニュアル（PDF/Word）** → 読み込んでリライト・最新化

### 出力形式

- Word（.docx）- Jony Iveデザインシステム準拠
- 改訂履歴ページ自動生成
- comparison-table-v2との連携で新旧対比表出力

## トリガーワード

以下のキーワードでこのスキルを起動：
- 「マニュアルを作成」「手順書を作って」「操作説明書を生成」
- 「業務マニュアル」「作業手順書」「操作マニュアル」
- 「既存マニュアルをリライト」「マニュアルを更新」
- 「窓口対応マニュアル」「接客マニュアル」

## ワークフロー

### Phase 1: 入力分析

```bash
# アップロードファイルの確認
ls -la /mnt/user-data/uploads/
```

**入力パターン判定:**
- `.docx` / `.pdf` → 既存マニュアルリライトモード
- `.png` / `.jpg` / `.jpeg` → スクリーンショット解析モード
- テキストのみ → 新規作成モード

### Phase 2: マニュアルタイプ選択

ユーザーに確認（指定がない場合）：

```
どのタイプのマニュアルを作成しますか？

1. **システム操作マニュアル** - 画面操作、入力手順、エラー対応
2. **業務フローマニュアル** - 業務手順、判断基準、承認フロー
3. **接客・窓口対応マニュアル** - トークスクリプト、FAQ、対応事例

また、以下のオプションも指定できます：
- 業種: 金融機関 / 協同組合 / 一般企業
- 対象者: 新人向け / 経験者向け / 管理者向け
```

### Phase 3: 生成実行

```bash
cd /home/claude
node /mnt/skills/user/manual-generator/scripts/manual_generator.js \
  --type <system|workflow|service> \
  --title "マニュアルタイトル" \
  --industry <finance|cooperative|general> \
  --audience <beginner|experienced|manager> \
  --version "1.0" \
  --output /mnt/user-data/outputs/manual.docx
```

### Phase 4: 出力

```markdown
[マニュアルを見る](computer:///mnt/user-data/outputs/manual.docx)
```

## マニュアル構成テンプレート

### 共通構成

```
表紙
├── タイトル
├── バージョン / 改訂日
├── 作成部署 / 承認者
└── 機密区分（金融機関向け）

目次

1. はじめに
   ├── 本マニュアルの目的
   ├── 対象者
   ├── 適用範囲
   └── 関連文書

2. [タイプ別メインコンテンツ]

3. 注意事項
   ├── セキュリティ（金融機関向け自動挿入）
   ├── コンプライアンス（金融機関向け自動挿入）
   └── 禁止事項

4. FAQ / トラブルシューティング

5. 問い合わせ先

改訂履歴
├── バージョン
├── 改訂日
├── 改訂内容
└── 改訂者
```

### タイプ別メインコンテンツ

**system（システム操作）:**
```
2. 操作手順
   2.1 ログイン / 起動
   2.2 基本操作
       ├── 画面説明（キャプチャ挿入）
       ├── 操作手順（番号付きステップ）
       ├── 入力項目説明（表形式）
       └── 操作後の確認ポイント
   2.3 データ入力 / 更新
   2.4 出力 / 印刷
   2.5 終了 / ログアウト

3. エラー対応
   ├── エラーメッセージ一覧（表形式）
   ├── 対処方法
   └── エスカレーション先
```

**workflow（業務フロー）:**
```
2. 業務フロー
   2.1 業務概要
       ├── 目的
       ├── 関係部署
       └── 処理期限
   2.2 フロー図（Mermaid/表形式）
   2.3 各ステップの詳細
       ├── 作業内容
       ├── 判断基準
       ├── 必要書類
       └── 承認者
   2.4 例外処理
   2.5 チェックリスト

3. 判断基準・ルール
   ├── 承認権限マトリクス
   ├── 金額別処理ルール
   └── 期限・納期ルール
```

**service（接客・窓口）:**
```
2. 対応フロー
   2.1 来店時の挨拶・受付
   2.2 用件確認
   2.3 対応パターン別スクリプト
       ├── [パターンA] 基本対応
       │   ├── お客様「～～」
       │   └── 対応者「～～」
       ├── [パターンB] クレーム対応
       └── [パターンC] 専門的質問
   2.4 クロージング・お見送り

3. FAQ集
   ├── Q1: よくある質問
   │   └── A1: 回答テンプレート
   └── Q2: ...

4. エスカレーション基準
   ├── 上席対応が必要なケース
   └── 連絡先・対応フロー
```

## 業種別オプション

### 金融機関向け（--industry finance）

以下の項目を自動挿入：

**表紙に追加:**
```
機密区分: □社外秘 □部外秘 □一般
```

**セキュリティ注意事項（自動挿入）:**
```
【セキュリティに関する注意事項】
□ 本マニュアルは社外持ち出し禁止です
□ 電子データのコピー・転送は禁止です
□ 業務終了後は施錠保管してください
□ 不要になった紙媒体はシュレッダー処理してください
```

**コンプライアンス項目（自動挿入）:**
```
【コンプライアンス確認事項】
□ 個人情報の取り扱いに注意してください
□ 顧客情報は必要最小限の範囲で閲覧してください
□ 不正アクセス・不正利用は懲戒処分の対象です
□ 疑わしい取引を発見した場合は直ちに報告してください
```

### 協同組合向け（--industry cooperative）

以下の調整を適用：

**平易化オプション:**
- 専門用語に（　）で読み仮名・説明を追加
- 長文を短く分割
- 図表・イラストを多用
- 重要ポイントを「ここがポイント！」枠で強調

**組合員向け表現:**
```
【変換例】
× 当該事項に該当する場合は... 
○ この条件に当てはまる場合は...

× 所定の様式により申請してください
○ 決まった用紙で申し込んでください
```

## 入力形式別ワークフロー

### テキスト説明から生成

```javascript
// ユーザーからの入力例
const input = `
業務名: 経費精算
対象者: 全社員
手順:
1. 経費精算システムにログイン
2. 「新規申請」ボタンをクリック
3. 必要事項を入力
4. 領収書を添付
5. 上長に申請
`;

// → 構造化してマニュアル生成
```

### スクリーンショットから生成

```bash
# 画像ファイルがアップロードされた場合
ls /mnt/user-data/uploads/*.{png,jpg,jpeg} 2>/dev/null
```

**処理フロー:**
1. 画像をClaudeのビジョン機能で解析
2. UI要素を特定（ボタン、入力欄、メニュー等）
3. 操作手順を推測して記述
4. 画像を挿入した操作説明を生成

**ステップ情報JSON形式:**

画像付きマニュアルを生成する場合、以下の形式のJSONファイルを作成します：

```json
{
  "steps": [
    {
      "number": 1,
      "title": "ログイン画面を開く",
      "description": "ブラウザでシステムURLにアクセスします。",
      "image": "/path/to/screenshot1.png",
      "points": [
        "ブックマークに登録しておくと便利です",
        "社内ネットワークからのみアクセス可能"
      ],
      "warning": "パスワードを5回間違えるとロックされます"
    },
    {
      "number": 2,
      "title": "ユーザーID・パスワードを入力",
      "description": "発行されたIDとパスワードを入力します。",
      "image": "/path/to/screenshot2.png",
      "points": ["ユーザーIDは社員番号と同一"]
    }
  ]
}
```

**各フィールドの説明:**

| フィールド | 必須 | 説明 |
|-----------|------|------|
| `number` | ○ | ステップ番号 |
| `title` | ○ | ステップタイトル |
| `description` | ○ | 操作説明文 |
| `image` | - | スクリーンショット画像パス（PNG/JPG/JPEG） |
| `points` | - | ポイント・補足事項（配列） |
| `warning` | - | 注意事項（⚠️マーク付きで表示） |

**生成コマンド:**

```bash
node scripts/manual_generator.js \
  --type system \
  --title "システム操作マニュアル" \
  --steps-json /path/to/steps.json \
  --output /mnt/user-data/outputs/manual.docx
```

**画像挿入形式:**
```javascript
// docx-js での画像挿入
new Paragraph({
  alignment: AlignmentType.CENTER,
  children: [new ImageRun({
    type: "png",
    data: fs.readFileSync(imagePath),
    transformation: { width: 450, height: 270 },
    altText: { title: "画面キャプチャ", description: "操作画面", name: "screenshot" }
  })]
}),
new Paragraph({
  alignment: AlignmentType.CENTER,
  children: [new TextRun({ text: "図1: ログイン画面", italics: true, size: 18 })]
})
```

### 既存マニュアルリライト

PDF/Wordファイルから構造を抽出し、新フォーマットに変換します。

**対応形式:**
- Word (.docx)
- PDF (.pdf) ※テキストPDFのみ、スキャンPDFは非対応

**処理フロー:**

```
1. ファイルアップロード
       ↓
2. コンテンツ抽出（content_extractor.js）
   - Word: pandocでMarkdown変換
   - PDF: pdftotextでテキスト抽出
       ↓
3. 構造解析
   - 見出しパターン検出（#, 1., 第X章, 【】等）
   - セクション/サブセクション分割
   - メタデータ抽出（作成日、バージョン、作成者）
       ↓
4. 新フォーマット変換（manual_rewriter.js）
   - Jony Iveデザイン適用
   - 業種別オプション適用
   - 改訂履歴に「リライト」記録
       ↓
5. 新マニュアル出力
```

**抽出コマンド（構造確認用）:**

```bash
node scripts/content_extractor.js <入力ファイル> <出力JSON>
```

**出力JSON形式:**

```json
{
  "source": "old_manual.docx",
  "extractedAt": "2025-12-01T12:00:00.000Z",
  "structure": {
    "title": "経費精算業務マニュアル",
    "metadata": {
      "version": "1.0",
      "date": "2020年4月1日",
      "author": "総務部"
    },
    "sections": [
      {
        "level": 1,
        "title": "はじめに",
        "content": "本マニュアルは...",
        "subsections": []
      },
      {
        "level": 1,
        "title": "経費精算の流れ",
        "content": "経費精算は以下の手順で実施する...",
        "subsections": [
          {
            "level": 2,
            "title": "領収書の取り扱い",
            "content": "領収書は速やかに整理し..."
          }
        ]
      }
    ]
  }
}
```

**リライトコマンド:**

```bash
node scripts/manual_rewriter.js \
  --input <入力ファイル（PDF/DOCX/JSON）> \
  --output <出力ファイル> \
  --industry <general|finance|cooperative> \
  --version <新バージョン> \
  --author <作成者名>
```

**オプション詳細:**

| オプション | 説明 | デフォルト |
|-----------|------|----------|
| `--input` | 入力ファイル（必須） | - |
| `--output` | 出力ファイル | rewritten_manual.docx |
| `--industry` | 業種（general/finance/cooperative） | general |
| `--version` | 新バージョン番号 | 1.0 |
| `--author` | 作成者名 | 元のメタデータから継承 |

**協同組合向け平易化（--industry cooperative）:**

自動的に以下の表現変換が適用されます：

| 変換前 | 変換後 |
|--------|--------|
| 当該 | この |
| 該当する | 当てはまる |
| 所定の | 決められた |
| 様式 | 用紙 |
| 申請 | 申し込み |
| 記載 | 書く |
| 提出 | 出す |
| 遵守 | 守る |
| 留意 | 気をつける |
| 速やかに | すぐに |
| 適宜 | 必要に応じて |

**使用例:**

```bash
# 古いWordマニュアルをリライト（協同組合向け・平易化）
node scripts/manual_rewriter.js \
  --input /mnt/user-data/uploads/old_manual.docx \
  --output /mnt/user-data/outputs/new_manual.docx \
  --industry cooperative \
  --version "2.0" \
  --author "DX推進室"

# 金融機関向け（セキュリティ・コンプラ項目付き）
node scripts/manual_rewriter.js \
  --input /mnt/user-data/uploads/old_manual.pdf \
  --output /mnt/user-data/outputs/new_manual.docx \
  --industry finance \
  --version "3.0"
```

**リライト後のマニュアル構成:**

```
表紙
├── タイトル（意味のある単位で改行）
├── 【リライト版】マーク
├── バージョン / 改訂日
└── 機密区分（金融機関向け）

[元のセクション構造を保持]

改訂履歴
├── 元バージョン | 元の作成日 | 原本からリライト
└── 新バージョン | 今日の日付 | 新フォーマット適用
```

## バージョン管理・改訂履歴

### 改訂履歴テーブル

```javascript
// 自動生成される改訂履歴
const revisionHistory = [
  { version: "1.0", date: "2025-01-15", changes: "初版作成", author: "山田太郎" },
  { version: "1.1", date: "2025-03-01", changes: "第3章追加", author: "鈴木花子" },
  { version: "2.0", date: "2025-06-01", changes: "全面改訂", author: "山田太郎" }
];
```

### comparison-table-v2 との連携

旧マニュアルと新マニュアルの両方が存在する場合：

```bash
# 新旧対比表を同時生成
node /mnt/skills/user/comparison-table-v2/scripts/comparison_docx_generator_v4.js \
  /mnt/user-data/uploads/old_manual.docx \
  /mnt/user-data/outputs/new_manual.docx \
  /mnt/user-data/outputs/comparison_table.docx \
  "業務マニュアル" \
  "$(date '+%Y年%m月%d日')"
```

## デザインシステム

Jony Iveデザインシステム準拠（/mnt/skills/user/jony-ive-design-system/SKILL.md）

### タイトル分割ルール

表紙のタイトルは意味のある単位で自動改行されます：

**分割キーワード（優先度順）:**
1. `操作マニュアル` → 「経費精算システム」＋「操作マニュアル」
2. `業務マニュアル`
3. `マニュアル`
4. `手順書`
5. `操作手順`
6. `ガイドライン` / `ガイド`
7. `規程` / `規則` / `要領`
8. `フロー`
9. `対応マニュアル`

**例:**
```
入力: 経費精算システム操作マニュアル
出力:
  経費精算システム    ← 1行目（72pt）
  操作マニュアル      ← 2行目（64pt）

入力: 融資審査業務フロー
出力:
  融資審査業務        ← 1行目（72pt）
  フロー              ← 2行目（64pt）
```

**長いタイトルの場合:**
キーワードがない場合、助詞（「の」「に関する」「における」等）で分割を試みます。

### カラーパレット

```javascript
const COLORS = {
  black: "000000",       // タイトル、見出し
  dark_gray: "333333",   // 本文
  medium_gray: "666666", // 補足説明
  light_gray: "999999",  // 注釈
  separator: "E0E0E0",   // 区切り線
  bg_gray: "F5F5F5",     // 背景（注意書き枠）
  accent: "5B7B94",      // アクセント（重要項目）
};
```

### フォント

- **フォント**: メイリオ（統一）
- **タイトル**: 28pt Bold
- **見出し1**: 16pt Bold
- **見出し2**: 14pt Bold
- **見出し3**: 12pt Bold
- **本文**: 10pt Regular
- **注釈**: 9pt Regular

### レイアウト

- **用紙**: A4縦
- **余白**: 上下左右 25mm
- **行間**: 1.5行

## 使用例

### 例1: テキストからシステム操作マニュアル

```
User: 「経費精算システムの操作マニュアルを作成して。
       ログイン→新規申請→入力→添付→承認申請の流れで。」

Claude: [manual_generator.jsを実行]
        [マニュアルを見る](computer:///mnt/user-data/outputs/経費精算システム_操作マニュアル.docx)
```

### 例2: スクリーンショットから操作説明

```
User: [5枚の画面キャプチャをアップロード]
      「この画面の操作マニュアルを作って」

Claude: [画像を解析]
        [各画面の操作手順を生成]
        [マニュアルを見る](computer:///mnt/user-data/outputs/操作マニュアル.docx)
```

### 例3: 既存マニュアルのリライト

```
User: [古いPDFマニュアルをアップロード]
      「このマニュアルを最新フォーマットでリライトして」

Claude: [PDFからテキスト抽出]
        [内容を解析・再構成]
        [新フォーマットで生成]
        [マニュアルを見る](computer:///mnt/user-data/outputs/updated_manual.docx)
        
        旧版との比較が必要な場合は、新旧対比表も生成できます。
```

### 例4: 金融機関向けマニュアル

```
User: 「融資審査システムのマニュアルを作成。金融機関向けで。」

Claude: [--industry finance オプションで実行]
        [セキュリティ・コンプラ項目を自動挿入]
        [マニュアルを見る](computer:///mnt/user-data/outputs/融資審査システム_操作マニュアル.docx)
```

## スクリプト

### メイン生成スクリプト

`scripts/manual_generator.js` - マニュアル本体を生成

### ユーティリティ

`scripts/image_analyzer.js` - スクリーンショット解析補助
`scripts/content_extractor.js` - PDF/Word からのコンテンツ抽出

## 依存関係

```bash
# 必要なパッケージ
npm install docx
pip install python-docx pypdf2 --break-system-packages

# pandoc（テキスト抽出用）
sudo apt-get install pandoc
```

## エラーハンドリング

| エラー | 原因 | 対処 |
|--------|------|------|
| 画像が読み込めない | 形式不正 | PNG/JPG/JPEG形式で再アップロード |
| PDF抽出失敗 | スキャンPDF | OCR処理を実行するか、Word版を要求 |
| 生成失敗 | 情報不足 | 必要情報をヒアリング |

## ベストプラクティス

1. **タイプを明確に** - system/workflow/serviceの選択で構成が最適化される
2. **業種を指定** - 金融/協同組合では自動挿入項目が追加される
3. **画像は高解像度で** - 300dpi以上推奨
4. **既存マニュアルはWord形式で** - PDF（特にスキャン）より精度が高い
5. **バージョン管理を活用** - 改訂履歴と新旧対比表で変更管理

## 注意事項

- 生成されるマニュアルは雛形です。実運用前に内容を確認・調整してください
- 機密情報を含む場合は、出力ファイルの取り扱いに注意してください
- 画像解析は推測を含むため、正確性の確認が必要です
