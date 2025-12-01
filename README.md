# Skills（スキル）
スキルは、Claudeが特定のタスクのパフォーマンスを向上させるために動的に読み込む、指示、スクリプト、リソースのフォルダです。スキルは、企業のブランドガイドラインに従ったドキュメント作成、組織固有のワークフローを使用したデータ分析、個人的なタスクの自動化など、特定のタスクを再現可能な方法で完了する方法をClaudeに教えます。

詳細については、こちらをご覧ください：
- [スキルとは？](https://support.claude.com/en/articles/12512176-what-are-skills)
- [Claudeでのスキルの使用](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [カスタムスキルの作成方法](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [エージェントスキルで現実世界に対応するエージェントを装備](https://anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)

# このリポジトリについて

このリポジトリには、Claudeのスキルシステムで可能なことを示すサンプルスキルが含まれています。これらの例は、クリエイティブなアプリケーション（アート、音楽、デザイン）から技術的なタスク（Webアプリのテスト、MCPサーバー生成）、エンタープライズワークフロー（コミュニケーション、ブランディングなど）まで多岐にわたります。

各スキルは独自のディレクトリに自己完結しており、Claudeが使用する指示とメタデータを含む `SKILL.md` ファイルがあります。これらの例を参照して、独自のスキルのインスピレーションを得たり、さまざまなパターンやアプローチを理解したりしてください。

このリポジトリのサンプルスキルはオープンソース（Apache 2.0）です。また、[Claudeのドキュメント機能](https://www.anthropic.com/news/create-files)の裏側で動作するドキュメント作成・編集スキルを [`document-skills/`](./document-skills/) フォルダに含めています。これらはオープンソースではなくソース公開ですが、本番のAIアプリケーションで積極的に使用されているより複雑なスキルの参考として、開発者と共有したいと考えています。

**注意：** これらは、インスピレーションと学習のための参考例です。組織固有のワークフローや機密コンテンツではなく、汎用的な機能を紹介しています。

## 免責事項

**これらのスキルは、デモンストレーションおよび教育目的でのみ提供されています。** これらの機能の一部はClaudeで利用可能な場合がありますが、Claudeから受け取る実装や動作は、これらの例で示されているものとは異なる場合があります。これらの例は、パターンと可能性を示すことを目的としています。重要なタスクに依存する前に、必ず自分の環境でスキルを徹底的にテストしてください。

# サンプルスキル

このリポジトリには、さまざまな機能を示す多様なサンプルスキルのコレクションが含まれています：

## クリエイティブ＆デザイン
- **algorithmic-art** - シード付き乱数、フローフィールド、パーティクルシステムを使用してp5.jsでジェネレーティブアートを作成
- **canvas-design** - デザイン哲学を使用して.pngおよび.pdf形式で美しいビジュアルアートをデザイン
- **slack-gif-creator** - Slackのサイズ制限に最適化されたアニメーションGIFを作成
- **jony-ive-design-system** - Jony Iveのデザイン哲学に基づくビジネス文書のスタイルガイドライン
- **seminar-resume-generator** - 勉強会・セミナー用のレジュメをWord形式で自動生成

## 開発＆技術
- **artifacts-builder** - React、Tailwind CSS、shadcn/uiコンポーネントを使用して複雑なclaude.ai HTMLアーティファクトを構築
- **mcp-server** - 外部APIとサービスを統合するための高品質なMCPサーバー作成ガイド
- **webapp-testing** - UIの検証とデバッグのためにPlaywrightを使用してローカルWebアプリケーションをテスト
- **data-cleaner** - CSV/Excel/TSV/JSONファイルの自動データクリーニングと前処理
- **smart-chart-generator** - CSVデータから最適なチャートを自動生成
- **mermaid-flow-generator** - Mermaid記法でフローチャートやシーケンス図を自動生成

## エンタープライズ＆コミュニケーション
- **brand-guidelines** - Anthropicの公式ブランドカラーとタイポグラフィをアーティファクトに適用
- **internal-comms** - ステータスレポート、ニュースレター、FAQなどの社内コミュニケーションを作成
- **theme-factory** - 10種類のプリセットプロフェッショナルテーマでアーティファクトをスタイル化、またはカスタムテーマをその場で生成

## ビジネス文書＆契約書
- **billing-documents** - 請求書・見積書を自動生成する統合スキル
- **consulting-contract-generator** - 生成AIアドバイザリー・コンサルティング業務委託契約書を自動生成
- **nda-generator** - 日本語の機密保持契約書（NDA）を自動生成
- **contract-analyzer** - 日本語契約書PDFを分析し、重要項目を構造化して抽出
- **comparison-table-v2** - 新旧対比表を階層構造解析でWord文書に生成
- **manual-generator** - 業務マニュアル・手順書を自動生成

## プロジェクト管理＆分析
- **gantt-chart-generator** - プロジェクトのガントチャートをExcel形式で自動生成
- **meeting-to-tasksheet** - 会議の音声入力・テキストから議事録とタスク管理表を自動生成
- **hearing-sheet-generator** - 初回商談・現状把握ヒアリング用のExcelシートを動的に生成
- **shift-scheduler** - ショッピングセンター・小売店向けシフト表自動生成
- **sales-analyzer-xlsx** - 売上データCSVから高度な分析Excelを自動生成
- **daily-report-voice** - 音声入力による業務日報作成とGoogle Drive連携
- **monthly-report-generator** - 日報データから月次活動レポートを自動生成

## メタスキル
- **skill-creator** - Claudeの機能を拡張する効果的なスキルを作成するためのガイド
- **template-skill** - 新しいスキルの出発点として使用する基本テンプレート
- **agent-skill-planner** - Agent Skill作成のための対話型分析プランナー

## ワークフロー＆自動化
- **workflow-kenken** - 株式会社けんけんの業務ワークフロー自動化（契約フェーズ・実行フェーズ・パラレル実行対応）

# ドキュメントスキル

`document-skills/` サブディレクトリには、Claudeがさまざまなドキュメントファイル形式を作成するのに役立つようにAnthropicが開発したスキルが含まれています。これらのスキルは、複雑なファイル形式とバイナリデータを扱うための高度なパターンを示しています：

- **docx** - 変更履歴、コメント、書式保持、テキスト抽出をサポートするWordドキュメントの作成、編集、分析
- **pdf** - テキストと表の抽出、新しいPDFの作成、ドキュメントの結合/分割、フォーム処理のための包括的なPDF操作ツールキット
- **pptx** - レイアウト、テンプレート、チャート、自動スライド生成をサポートするPowerPointプレゼンテーションの作成、編集、分析
- **xlsx** - 数式、書式設定、データ分析、視覚化をサポートするExcelスプレッドシートの作成、編集、分析

**重要な免責事項：** これらのドキュメントスキルは特定時点のスナップショットであり、積極的に保守または更新されていません。これらのスキルのバージョンはClaudeに事前に含まれて出荷されます。これらは主に、Anthropicがバイナリファイル形式やドキュメント構造を扱うより複雑なスキルを開発する方法を示す参考例として意図されています。

# Claude Code、Claude.ai、APIでお試しください

## Claude Code
Claude Codeで次のコマンドを実行して、このリポジトリをClaude Codeプラグインマーケットプレイスとして登録できます：
```
/plugin marketplace add anthropics/skills
```

次に、特定のスキルセットをインストールするには：
1. `Browse and install plugins`を選択
2. `anthropic-agent-skills`を選択
3. `document-skills`または`example-skills`を選択
4. `Install now`を選択

または、次のコマンドで直接プラグインをインストール：
```
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
```

プラグインをインストール後、スキルに言及するだけで使用できます。例えば、マーケットプレイスから`document-skills`プラグインをインストールした場合、Claude Codeに次のようなリクエストができます：「PDFスキルを使用してpath/to/some-file.pdfからフォームフィールドを抽出してください」

## Claude.ai

これらのサンプルスキルはすべて、Claude.aiの有料プランですでに利用可能です。

このリポジトリのスキルを使用したり、カスタムスキルをアップロードするには、[Claudeでのスキルの使用](https://support.claude.com/en/articles/12512180-using-skills-in-claude#h_a4222fa77b)の指示に従ってください。

## Claude API

Claude APIを介して、Anthropicの事前構築されたスキルを使用し、カスタムスキルをアップロードできます。詳細は[Skills API クイックスタート](https://docs.claude.com/en/api/skills-guide#creating-a-skill)をご覧ください。

# 基本的なスキルの作成

スキルは簡単に作成できます - YAMLフロントマターと指示を含む`SKILL.md`ファイルのあるフォルダだけです。このリポジトリの**template-skill**を出発点として使用できます：

```markdown
---
name: my-skill-name
description: このスキルが何をするか、いつ使用するかの明確な説明
---

# My Skill Name

[このスキルがアクティブな時にClaudeが従う指示をここに追加]

## 例
- 使用例 1
- 使用例 2

## ガイドライン
- ガイドライン 1
- ガイドライン 2
```

フロントマターには2つのフィールドのみが必要です：
- `name` - スキルの一意の識別子（小文字、スペースはハイフン）
- `description` - スキルが何をするか、いつ使用するかの完全な説明

以下のマークダウンコンテンツには、Claudeが従う指示、例、ガイドラインが含まれています。詳細については、[カスタムスキルの作成方法](https://support.claude.com/en/articles/12512198-creating-custom-skills)をご覧ください。

# パートナースキル

スキルは、特定のソフトウェアの使用方法をClaudeに上達させるための優れた方法です。パートナーからの素晴らしいサンプルスキルを見つけたら、ここでハイライトすることがあります：

- **Notion** - [Claude用Notionスキル](https://www.notion.so/notiondevs/Notion-Skills-for-Claude-28da4445d27180c7af1df7d8615723d0)