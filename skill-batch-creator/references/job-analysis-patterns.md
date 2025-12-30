# 職業分析パターン集

職業・ペインポイントからAgent Skillsを提案するための分析フレームワーク。

---

## 分析フロー

```
職業 → 業務特性の推定 → ペインポイント分類 → スキルパターン選択 → 提案生成
```

---

## 1. 職業カテゴリと業務特性

### 営業系（Sales）

| 職種 | 主要業務 | よくあるペインポイント | 推奨スキルパターン |
|------|----------|----------------------|------------------|
| 営業担当 | 顧客訪問、商談、提案 | 提案書作成、日報、見積もり | proposal-generator, visit-report, quote-creator |
| 営業マネージャー | チーム管理、予実管理 | 週次レポート、パイプライン分析 | sales-report-generator, pipeline-analyzer |
| インサイドセールス | 架電、メール、リード管理 | コールスクリプト、フォローアップ | call-script-generator, followup-email-creator |
| カスタマーサクセス | 導入支援、チャーン防止 | オンボーディング資料、健康スコア | onboarding-guide-creator, health-score-analyzer |

### 人事系（HR）

| 職種 | 主要業務 | よくあるペインポイント | 推奨スキルパターン |
|------|----------|----------------------|------------------|
| 採用担当 | 応募者管理、面接調整 | 面接評価、候補者比較 | interview-evaluator, candidate-ranker |
| 研修担当 | 教育プログラム設計 | 研修資料作成、効果測定 | training-material-creator, learning-analyzer |
| 労務担当 | 勤怠管理、給与計算 | 勤怠集計、規程確認 | attendance-summarizer, policy-checker |
| HRBP | 部門支援、組織開発 | 1on1記録、エンゲージメント分析 | oneone-summarizer, engagement-analyzer |

### 開発系（Engineering）

| 職種 | 主要業務 | よくあるペインポイント | 推奨スキルパターン |
|------|----------|----------------------|------------------|
| バックエンドエンジニア | API設計、DB設計 | ドキュメント更新、コードレビュー | api-doc-generator, code-review-helper |
| フロントエンドエンジニア | UI実装、コンポーネント設計 | デザイン→コード変換 | design-to-code, component-generator |
| QAエンジニア | テスト設計、バグ管理 | テストケース作成、バグレポート | testcase-generator, bug-report-formatter |
| DevOps | インフラ構築、CI/CD | 手順書作成、障害報告 | runbook-creator, incident-report-generator |
| テックリード | 技術選定、アーキ設計 | ADR作成、技術調査 | adr-writer, tech-research-summarizer |

### マーケティング系（Marketing）

| 職種 | 主要業務 | よくあるペインポイント | 推奨スキルパターン |
|------|----------|----------------------|------------------|
| コンテンツマーケター | ブログ、SNS、動画 | コンテンツ企画、投稿管理 | content-calendar-creator, social-post-generator |
| 広告運用 | リスティング、ディスプレイ | レポート作成、入札調整 | ad-report-generator, bid-optimizer |
| PRマーケター | プレスリリース、メディア対応 | リリース作成、メディアリスト | press-release-writer, media-list-manager |
| イベントマーケター | セミナー、展示会 | 集客メール、参加者管理 | event-email-creator, attendee-analyzer |

### 経理・財務系（Finance）

| 職種 | 主要業務 | よくあるペインポイント | 推奨スキルパターン |
|------|----------|----------------------|------------------|
| 経理担当 | 仕訳、決算、税務 | 請求書処理、仕訳入力 | invoice-processor, journal-entry-creator |
| 財務担当 | 資金繰り、予算管理 | 予実分析、キャッシュフロー | budget-variance-analyzer, cashflow-forecaster |
| 管理会計 | 原価計算、KPI管理 | 部門別PL、KPIレポート | cost-analyzer, kpi-dashboard-generator |

### 法務・コンプライアンス系（Legal）

| 職種 | 主要業務 | よくあるペインポイント | 推奨スキルパターン |
|------|----------|----------------------|------------------|
| 法務担当 | 契約審査、法務相談 | 契約書レビュー、リスク分析 | contract-analyzer, risk-highlighter |
| コンプライアンス担当 | 規程管理、監査対応 | チェックリスト、監査資料 | compliance-checker, audit-prep-assistant |
| 知財担当 | 特許、商標管理 | 出願書類、先行技術調査 | patent-draft-helper, prior-art-searcher |

### 管理職・経営層（Management）

| 職種 | 主要業務 | よくあるペインポイント | 推奨スキルパターン |
|------|----------|----------------------|------------------|
| 部長・マネージャー | 部門運営、承認業務 | 報告資料、会議準備 | executive-summary-generator, meeting-prep-assistant |
| 経営企画 | 戦略立案、M&A | 市場分析、事業計画 | market-analyzer, business-plan-writer |
| 役員・CxO | 意思決定、対外活動 | 取締役会資料、スピーチ | board-deck-creator, speech-writer |

### 専門職系（Specialist）

| 職種 | 主要業務 | よくあるペインポイント | 推奨スキルパターン |
|------|----------|----------------------|------------------|
| 研究者・学者 | 論文執筆、実験 | 文献サーベイ、論文整理 | literature-reviewer, paper-summarizer |
| コンサルタント | 課題分析、提案 | 提案書作成、分析レポート | consulting-proposal-creator, analysis-report-generator |
| デザイナー | UI/UX設計、ブランディング | デザインレビュー依頼、仕様書 | design-review-request-creator, spec-writer |

---

## 2. ペインポイント分類と対応パターン

### 時間系のペインポイント

**キーワード**: 「時間がかかる」「毎週/毎月」「繰り返し」「手作業で」

| ペインポイントパターン | スキルタイプ | 命名パターン |
|----------------------|------------|-------------|
| 〜の作成に時間がかかる | generator | {対象}-generator |
| 毎週/毎月〜を作成している | auto-generator | weekly-{対象}-generator |
| 同じ形式の〜を繰り返し作成 | template-filler | {対象}-template-filler |
| 手作業で〜を入力している | processor | {対象}-processor |

**例:**
- 「週次レポート作成に3時間」→ `weekly-report-generator`
- 「請求書を手作業で処理」→ `invoice-processor`

### 情報整理系のペインポイント

**キーワード**: 「集計」「比較」「分析」「まとめ」「抽出」

| ペインポイントパターン | スキルタイプ | 命名パターン |
|----------------------|------------|-------------|
| 〜を集計している | aggregator | {対象}-aggregator |
| 複数の〜を比較している | comparer | {対象}-comparer |
| 〜を分析してレポート化 | analyzer | {対象}-analyzer |
| 大量の〜から情報を抽出 | extractor | {対象}-extractor |

**例:**
- 「面接評価の集計が煩雑」→ `interview-score-aggregator`
- 「競合情報を比較分析」→ `competitor-analyzer`

### ドキュメント系のペインポイント

**キーワード**: 「ドキュメント」「資料」「更新」「フォーマット」

| ペインポイントパターン | スキルタイプ | 命名パターン |
|----------------------|------------|-------------|
| ドキュメントの更新が追いつかない | doc-generator | {対象}-doc-generator |
| 資料のフォーマットがバラバラ | formatter | {対象}-formatter |
| 〜を文書化する必要がある | documenter | {対象}-documenter |

**例:**
- 「APIドキュメントの更新が追いつかない」→ `api-doc-generator`
- 「議事録のフォーマットが統一されていない」→ `meeting-minutes-formatter`

### コミュニケーション系のペインポイント

**キーワード**: 「メール」「連絡」「報告」「依頼」「調整」

| ペインポイントパターン | スキルタイプ | 命名パターン |
|----------------------|------------|-------------|
| メールの文面作成に時間 | email-writer | {目的}-email-writer |
| 報告の文面を考えるのが大変 | report-writer | {目的}-report-writer |
| 依頼文の作成 | request-creator | {対象}-request-creator |

**例:**
- 「フォローアップメールの作成」→ `followup-email-writer`
- 「日程調整のやりとりが多い」→ `schedule-coordinator`

### チェック・検証系のペインポイント

**キーワード**: 「チェック」「確認」「レビュー」「漏れ」「ミス」

| ペインポイントパターン | スキルタイプ | 命名パターン |
|----------------------|------------|-------------|
| 〜のチェックに時間がかかる | checker | {対象}-checker |
| 〜の漏れがないか確認 | validator | {対象}-validator |
| 〜のレビューが追いつかない | reviewer | {対象}-reviewer |

**例:**
- 「契約書のリスク箇所チェック」→ `contract-risk-checker`
- 「コードレビューが追いつかない」→ `code-review-helper`

---

## 3. 出力形式の選定ガイド

| ユースケース | 推奨形式 | 理由 |
|-------------|---------|------|
| 社内報告、プレゼン用 | Excel, PowerPoint | ビジネス標準フォーマット |
| 技術ドキュメント | Markdown | バージョン管理、可読性 |
| 外部提出書類 | PDF | 改変防止、印刷対応 |
| データ連携 | CSV, JSON | 他システムとの連携 |
| 社内共有メモ | Markdown, テキスト | 軽量、編集容易 |

---

## 4. スキル提案テンプレート

CSVの各行に対して、以下の形式で提案を生成:

```
## 提案: {記入者名}さん向けスキル

### 分析結果
- **職業カテゴリ**: {営業系/開発系/etc.}
- **主要業務**: {推定される主要業務}
- **ペインポイント分類**: {時間系/情報整理系/etc.}

### 提案スキル
- **スキル名**: `{提案するスキル名}`
- **目的**: {1文で説明}
- **入力**: {想定される入力データ}
- **出力**: {出力形式}
- **自動化効果**: {時間削減見込み}

### このスキルでできること
1. {機能1}
2. {機能2}
3. {機能3}

### 作成しますか？
この提案でスキルを作成する場合は「はい」と回答してください。
調整が必要な場合は、修正点をお知らせください。
```

---

## 5. 複合スキルの検討

同じ部門/チームから複数のリクエストがある場合、関連するスキルをまとめて設計することを検討:

**例: 営業部から3つのリクエスト**
1. 週次レポート作成
2. 提案書作成
3. 見積書作成

**検討オプション:**
- A) 個別スキル: `sales-weekly-report`, `sales-proposal`, `sales-quote`
- B) 統合スキル: `sales-document-suite`（ただし1 Skill = 1 Purpose原則に注意）

**推奨**: 基本は個別スキルで作成し、共通の参照資料（顧客情報、商品マスタ等）を共有する設計。
