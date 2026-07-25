# Claude Code 向け Academic Research Skills

[![Version](https://img.shields.io/badge/version-v3.16.0-blue)](https://github.com/Imbad0202/academic-research-skills/releases/tag/v3.16.0)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.20696614-blue)](https://doi.org/10.5281/zenodo.20696614)
[![License: CC BY-NC 4.0](https://img.shields.io/badge/license-CC%20BY--NC%204.0-lightgrey)](https://creativecommons.org/licenses/by-nc/4.0/)
[![Sponsor](https://img.shields.io/badge/sponsor-Buy%20Me%20a%20Coffee-orange?logo=buy-me-a-coffee)](https://buymeacoffee.com/crucify020v)

[English](README.md) | [简体中文版](README.zh-CN.md) | [繁體中文版](README.zh-TW.md) | [한국어](README.ko-KR.md)

学術研究のための Claude Code スキル統合スイート。研究から論文公開までの全工程をカバーします。

**30秒でインストール**（Claude Code CLI / VS Code / JetBrains、v3.7.0+）:

```text
/plugin marketplace add Imbad0202/academic-research-skills
/plugin install academic-research-skills
```

その後、`/ars-plan` を試してソクラテス式対話で論文構成を整理するか、前提条件と従来のシンボリックリンク方式については [クイックインストール](#クイックインストール) を参照してください。

> **AI はあなたの副操縦士であり、操縦士ではありません。** このツールはあなたの代わりに論文を書きません。参考文献の探索、引用のフォーマット、データ検証、論理的整合性チェックといった泥臭い作業を引き受けることで、本当に頭を使う必要のある部分 — 問いの定義、手法の選択、データの意味の解釈、「私はこう主張する」に続く文を書くこと — にあなたが集中できるようにします。
>
> 「humanizer」とは異なり、このツールは AI を使った事実を隠すためのものではありません。より良い文章を書くための助けです。Style Calibration は過去の作品からあなたの声を学習します。Writing Quality Check は機械的に見える文章のパターンを検出します。目的は品質であって、ごまかしではありません。

### なぜ完全自動化ではなく Human-in-the-Loop なのか?

Lu ら (2026, *Nature* 651:914-919) は **The AI Scientist** を構築しました — トップレベルの ML 学会（ICLR 2025 workshop、スコア 6.33/10 vs workshop 平均 4.87）でブラインドピアレビューを通過した論文を発表した、初の完全自律型 AI 研究システムです。彼らの Limitations セクションは、完全自律型 AI 研究パイプラインが継承する失敗モードを列挙しています: 実装バグ、結果のハルシネーション、ショートカット依存、バグを洞察として再フレーミング、方法論の捏造、フレームロック、引用のハルシネーション。

ARS は **人間の研究者を AI が支援する形式が、どちらか単独よりもこれらの失敗モードを回避できる** という前提に基づいて構築されています。Stage 2.5 と Stage 4.5 の整合性ゲートは 7 モードのブロッキングチェックリストを実行します（[`academic-pipeline/references/ai_research_failure_modes.md`](academic-pipeline/references/ai_research_failure_modes.md) を参照）。レビュアーはオプトインのキャリブレーションモードを提供し、ユーザー提供のゴールドセットに対して自身の FNR/FPR を測定します。

[**Zhao ら**](https://arxiv.org/abs/2605.07723)（2026-05）は arXiv、bioRxiv、SSRN、PMC の 2.5M 論文にわたる 111M 件の参考文献を監査しました。彼らの保守的見積りでは、2025年だけで 146,932 件のハルシネーション引用が観測され、2024年中頃に変曲点が観測されています。bioRxiv-to-PMC ペアリングでは、プレプリントから出版物への持続率は 85.3% と報告されています。論文は「引用された参考文献が実際には主張していない主張を支持するために配置された実在の引用」を未解決の課題として記述しています。ARS v3.7.1 はソース来歴のための trust-chain frontmatter を追加し、v3.7.3 は将来の主張レベル監査のためのロケーターインフラストラクチャ（三層引用アンカー）を追加し、引用時に advisory リスクシグナルを表面化します（ARS は主張忠実性ギャップを内部で「L3」とラベル付けしています。これは論文の用語ではなく ARS の用語です）。v3.7.x は Zhao らのコーパス規模の発見に動機付けられています。ARS 自体のコーパス規模評価は今後の課題として残されています。

v3.8 は L3 ギャップの後半を閉じます。v3.7.3 は全引用にロケーターアンカーを持たせ、v3.8 はオプトインの監査パス（`ARS_CLAIM_AUDIT=1`）を追加します。これは各アンカーに対して引用元を取得し、主張が実際に裏付けられているかを判断します。5 つの新しい HIGH-WARN クラス（claim-not-supported、negative-constraint-violation、fabricated-reference、anchorless、constraint-violation-uncited）は、formatter ターミナルハードゲートを通じて出力を gate-refuse します。キャリブレーションは 20-tuple のゴールドセットと共に FNR<0.15 + FPR<0.10 の受容閾値で出荷されます。ramp-on 計画は v3.8 spec §5 に従いキャリブレーション後の証拠まで保留されます。

v3.3 は [**PaperOrchestra**](https://arxiv.org/abs/2604.05018)（Song, Song, Pfister & Yoon, 2026, Google）に触発されました: Semantic Scholar API 検証、アンチリーケージプロトコル、VLM 図表検証、スコア軌跡追跡。

---

## アーキテクチャ＆パイプライン

**👉 [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md)** — パイプライン全体ビュー: フロー図、ステージごとのマトリクス、データアクセスフロー、スキル依存グラフ、品質ゲート、モードリスト。

アーキテクチャドキュメントは、以前ここにあった煩雑なパイプライン説明を引き継ぎます。*どのステージで何が実行されるか* に関する情報はすべて一箇所に集約されています。

## クイックインストール

**前提条件**

- [Claude Code](https://docs.claude.com/en/docs/claude-code/setup)（最新版。プラグインパッケージングは最近のバージョンが必要）
- `ANTHROPIC_API_KEY` をエクスポート、または初回 `claude` 実行時に設定
- *オプション:* DOCX 用の Pandoc、APA 7.0 PDF 用の tectonic + Source Han Serif TC（Markdown 出力はどちらがなくても動作）

**プラグインインストール（v3.7.0+、推奨）:**

```text
/plugin marketplace add Imbad0202/academic-research-skills
/plugin install academic-research-skills
```

**動作確認:** `/ars-plan` を実行して取り組んでいる論文について説明してください — ARS がソクラテス式対話を開始し、章構成をマップします。代わりに単発テストを行うには、`/ars-lit-review "your topic"` を試してください。

**👉 [docs/SETUP.md](docs/SETUP.md)** — 完全ガイド: Claude Code インストール、API キー設定、DOCX/PDF 用のオプション Pandoc/tectonic、クロスモデル検証（`ARS_CROSS_MODEL`）、6 つのインストール方法（Plugin、プロジェクトスキル、グローバルスキル、claude.ai Project、リポジトリクローン、Claude Science インポート）。

**Claude Science をお使いですか？** 4 つのスキルは直接インポートできます: **Skills → Import from GitHub** で `https://github.com/Imbad0202/academic-research-skills` を貼り付け、**Preview** → **Import 4 skills**（本リポジトリ v3.14.0+ が必要 — インポーターは marketplace manifest に明示されたスキルパスを読み取ります）。インポートはその時点のスナップショットです: ARS の更新後は再インポートしてください。インポートされたスキルは ARS の方法論（研究・執筆・査読プロトコル）を伝えます。Claude Code 固有の仕組み — slash commands、hooks、サブエージェントオーケストレーション — は移行されません。詳細は [docs/SETUP.md](docs/SETUP.md) の Method 5 を参照。

**Codex CLI を使用していますか?** 代わりに姉妹ディストリビューションをインストールしてください: [`Imbad0202/academic-research-skills-codex`](https://github.com/Imbad0202/academic-research-skills-codex) — 同じワークフローコンテンツ、`ars-*` エイリアスを持つ単一の `$academic-research-suite` スキルとしての Codex ネイティブパッケージング。

## パフォーマンス＆コスト

**👉 [docs/PERFORMANCE.md](docs/PERFORMANCE.md)** — モードごとのトークン予算、フルパイプライン見積り（15k 語の論文で約 $4-6）、推奨 Claude Code 設定（Auto モード; Agent Team オプション）。

## ガイド＆記事

- [Academic Writing Shouldn't Be a Solo Act](https://open.substack.com/pub/edwardwu223235/p/academic-writing-shouldnt-be-a-solo?r=4dczl&utm_medium=ios) — 完全なパイプラインウォークスルー（英語）
- [學術寫作不該是一個人的事：一套開源 AI 協作工具如何改變研究者的工作流](https://open.substack.com/pub/edwardwu223235/p/ai?r=4dczl&utm_medium=ios) — 完整使用指南（繁體中文）

---

## 機能概要

- **Deep Research** — 13 エージェントの研究チーム。ソクラテス式ガイドモード、PRISMA システマティックレビュー、意図検出、対話健全性モニタリング、オプションのクロスモデル DA、Semantic Scholar API 検証付き。
- **Academic Paper** — 12 エージェントの論文執筆。Style Calibration、Writing Quality Check、LaTeX ハードニング、可視化、改訂コーチング、引用変換、アンチリーケージプロトコル、VLM 図表検証付き。
- **Academic Paper Reviewer** — 0-100 品質ルーブリックを持つ 7 エージェントの多視点ピアレビュー（EIC + 3 動的レビュアー + Devil's Advocate）、譲歩閾値プロトコル、攻撃強度保持、オプションのクロスモデル DA 批評/キャリブレーション、R&R トレーサビリティマトリクス、read-only 制約。
- **Academic Pipeline** — 10 ステージのパイプラインオーケストレーター。適応的チェックポイント、主張検証、Material Passport、オプションの `repro_lock`、オプションのクロスモデル整合性検証、会話中強化、スコア軌跡追跡付き。
- **Data Access Level Metadata**（v3.3.2+）— 各スキルが `data_access_level`（`raw` / `redacted` / `verified_only`）を宣言。`scripts/check_data_access_level.py` で強制。Anthropic の automated-w2s-researcher（2026）から適応されたパターン。[`shared/ground_truth_isolation_pattern.md`](shared/ground_truth_isolation_pattern.md) を参照。
- **Task Type Annotation**（v3.3.2+）— 各スキルが `task_type`（`open-ended` または `outcome-gradable`）を宣言。現在の ARS スキルはすべて `open-ended`。
- **Benchmark Report Schema**（v3.3.5+）— 誠実なベンチマーク比較のための JSON Schema + lint。[`shared/benchmark_report_pattern.md`](shared/benchmark_report_pattern.md) を参照。
- **Artifact Reproducibility Lockfile**（v3.3.5+）— Material Passport 上のオプションの `repro_lock` サブブロック。**設定ドキュメントであり、再生保証ではありません** — LLM 出力はバイト再現可能ではありません。[`shared/artifact_reproducibility_pattern.md`](shared/artifact_reproducibility_pattern.md) を参照。
- **実験来歴インテーク**（#260）— Material Passport のオプションの `experiment_provenance[]` は、研究者が**外部で**実行した実験を記録し（ARS は実験を実行しません）、論文の主張は `claim_intent_manifest.planned_experiment_ids[]` 経由でそれに join します。整合性ゲート（Stage 2.5/4.5）は実験裏付け主張を宣言された来歴と照合します — `ALIGNED` / `OVERSTATED` / `NOT_SUPPORTED_BY_PROVENANCE` / `PROVENANCE_INSUFFICIENT` — **ただし実験自体の正しさは判定しません**。fail-closed な `experiment_intake_declaration` により「実験を実行したか」が Stage 1 の明示的な決定になります。[`shared/handoff_schemas.md`](shared/handoff_schemas.md) を参照。

---

## ショーケース: 実際のパイプライン出力

実際の 10 ステージパイプライン実行からの完全な成果物を参照してください — ピアレビューレポート、整合性検証レポート、最終論文:

**[すべてのパイプライン成果物を見る →](examples/showcase/)**

| 成果物 | 説明 |
|---|---|
| [Final Paper (EN)](examples/showcase/full_paper_apa7.pdf) | APA 7.0 フォーマット、LaTeX コンパイル済み |
| [Final Paper (ZH)](examples/showcase/full_paper_zh_apa7.pdf) | 中国語版、APA 7.0 |
| [Integrity Report — Pre-Review](examples/showcase/integrity_report_stage2.5.pdf) | Stage 2.5: 捏造参照 15 件 + 統計エラー 3 件を捕捉 |
| [Integrity Report — Final](examples/showcase/integrity_report_stage4.5.pdf) | Stage 4.5: ゼロリグレッションを確認 |
| [Peer Review Round 1](examples/showcase/stage3_review_report.pdf) | EIC + 3 Reviewers + Devil's Advocate |
| [Re-Review](examples/showcase/stage3prime_rereview_report.pdf) | 改訂後の検証 |
| [Peer Review Round 2](examples/showcase/stage3_review_report_r2.pdf) | フォローアップレビュー |
| [Response to Reviewers](examples/showcase/response_to_reviewers_r2.pdf) | ポイントごとの著者回答 |
| [Post-Publication Audit Report](examples/showcase/post_publication_audit_2026-03-09.pdf) | 独立した完全参照監査: 3 回の整合性チェックで見逃された 21/68 件の問題を発見 |

---

## コンパニオン: Experiment Agent

研究に執筆前のコード実行や人間研究が含まれる場合、[Experiment Agent](https://github.com/Imbad0202/experiment-agent) スキルが ARS Stage 1（RESEARCH）と Stage 2（WRITE）の間のギャップを埋めます。

```
ARS Stage 1 RESEARCH  →  RQ Brief + Methodology Blueprint
        ↓
  experiment-agent     →  実験の実行/管理 → 結果検証
        ↓
ARS Stage 2 WRITE     →  検証された実験結果で論文執筆
```

**機能**: コード実験（Python、R など）をリアルタイムモニタリング付きで実行、IRB 倫理チェックリスト付き人間研究プロトコルを管理、11 タイプの誤謬検出付きで統計を解釈、再現性を検証。

**併用方法**: Stage 1 後に ARS パイプラインを一時停止し、別の experiment-agent セッションで実験を実行、その後、結果（Material Passport 付き）を ARS Stage 2 に戻します。ARS は一切の変更を必要としません。セットアップ手順については [experiment-agent README](https://github.com/Imbad0202/experiment-agent) を参照してください。

---

## 使い方

### Quick Start

```
# フル研究パイプラインを開始
You: "I want to write a research paper on AI's impact on higher education QA"

# ソクラテス式ガイダンスで開始
You: "Guide my research on AI in educational evaluation"

# ガイド付きプランニングで論文を執筆
You: "Guide me through writing a paper on demographic decline"

# 既存論文をレビュー
You: "Review this paper"（その後、論文を提供）

# パイプラインステータスを確認
You: "status"
```

### 個別スキル

#### Deep Research（8 モード）

```
"Research the impact of AI on higher education"       → full モード
"Give me a quick brief on X"                          → quick モード
"Do a systematic review on X with PRISMA"             → systematic-review モード
"Guide my research on X"                              → socratic モード（ガイド付き）
"Fact-check these claims"                             → fact-check モード
"Do a literature review on X"                         → lit-review モード
"Review this paper's research quality"                → review モード
```

#### Academic Paper（11 モード）

```
"Write a paper on X"                                  → full モード
"Guide me through writing a paper"                    → plan モード（ガイド付き）
"Build a paper outline"                               → outline-only モード
"I have a draft, here are reviewer comments"          → revision モード
"Parse these reviewer comments into a roadmap"        → revision-coach モード
"Write an abstract for this paper"                    → abstract-only モード
"Turn this into a literature review paper"            → lit-review モード
"Convert to LaTeX" / "Convert citations to IEEE"      → format-convert モード
"Check citations"                                     → citation-check モード
"Generate an AI disclosure statement for NeurIPS"     → disclosure モード
```

#### Academic Paper Reviewer（6 モード）

```
"Review this paper"                                   → full モード（EIC + R1/R2/R3 + Devil's Advocate）
"Quick assessment of this paper"                      → quick モード
"Guide me to improve this paper"                      → guided モード
"Check the methodology"                               → methodology-focus モード
"Verify the revisions"                                → re-review モード
"Calibrate this reviewer against my gold set"         → calibration モード
```

#### Academic Pipeline（オーケストレーター）

```
"I want to write a complete research paper"           → Stage 1 からのフルパイプライン
"I already have a paper, review it"                   → Stage 2.5 で中間エントリー（整合性優先）
"I received reviewer comments"                        → Stage 4 で中間エントリー
```

> パイプラインは **Stage 6: Process Summary** で終了します — 6 次元の Collaboration Quality Evaluation（1-100 採点）付きの論文作成プロセスレコードを自動生成します。

### サポート言語

- **繁體中文** — ユーザーが中国語で書く場合のデフォルト
- **English** — ユーザーが英語で書く場合のデフォルト
- 学術論文用のバイリンガル要旨（中国語 + 英語）

> **異なる言語を使用していますか?** ソクラテスモード（deep-research）と Plan モード（academic-paper）は **意図ベースのアクティベーション** を使用します — リクエストの意味を検出し、特定のキーワードではありません。これは **どの言語でも** 変更なしで動作することを意味します。
>
> ただし、一般的な `Trigger Keywords` セクション（スキルがそもそも有効化されるかを決定する）は依然として英語と繁體中文のキーワードを列挙しています。あなたの言語でスキルが確実に有効化されない場合、各 `SKILL.md` ファイルの `### Trigger Keywords` セクションにあなたの言語のキーワードを追加してマッチング信頼度を向上させることができます。

### サポートされる引用フォーマット

- APA 7.0（デフォルト、中国語引用ルール含む）
- Chicago（Notes & Author-Date）
- MLA
- IEEE
- Vancouver

### サポートされる論文構造

- IMRaD（実証研究）
- Thematic Literature Review
- Theoretical Analysis
- Case Study
- Policy Brief
- Conference Paper

---

## スキル詳細

エージェントごとの責務とステージごとの成果物は [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) に集約されました。リリースメタデータを一箇所にまとめるため、バージョン番号はここにアンカーされています。

### Deep Research（v2.11.0）

13 エージェントの研究チーム。モード: full、quick、review、lit-review、three-way-scan、fact-check、socratic、systematic-review。完全なエージェント名簿と成果物: ARCHITECTURE.md §3 を参照。

### Academic Paper（v3.2.0）

12 エージェントの論文執筆パイプライン。モード: full、plan、outline-only、revision、revision-coach、abstract-only、lit-review、format-convert、citation-check、disclosure、rebuttal-audit。出力: MD + DOCX（利用可能な場合 Pandoc 経由）+ LaTeX（APA 7.0 `apa7` クラス / IEEE / Chicago）→ tectonic 経由 PDF。完全なエージェント名簿とフェーズごとの責務: ARCHITECTURE.md §3 を参照。

### Academic Paper Reviewer（v1.10.0）

**0-100 品質ルーブリック** を持つ 7 エージェントの多視点レビュー。モード: full、re-review、quick、methodology-focus、guided、calibration。**決定マッピング:** ≥80 Accept、65-79 Minor Revision、50-64 Major Revision、<50 Reject。初回レビューチーム vs. 限定的な再レビューチームの境界: ARCHITECTURE.md §3 Stage 3 / Stage 3' を参照。

### Academic Pipeline（v3.16.0）

整合性検証、二段階レビュー、ソクラテス式コーチング、コラボレーション評価を持つ 10 ステージのオーケストレーター。パイプライン保証: 各ステージにユーザー確認チェックポイントが必要。整合性検証（Stage 2.5 + 4.5）はスキップできない。R&R Traceability Matrix（Schema 11）は著者の改訂主張を独立に検証する。v3.4 は Stage 2.5 / 4.5 に Compliance Agent（PRISMA-trAIce + RAISE）を追加した。v3.5 はすべての FULL/SLIM チェックポイントとパイプライン完了時に **Collaboration Depth Observer**（`collaboration_depth_agent`、advisory のみ — 決してブロックしない）を追加する。MANDATORY 整合性ゲート（2.5 / 4.5）は、コンプライアンスチェックが希薄化されないよう observer を明示的にスキップする。Wang & Zhang（2026）, IJETHE 23:11 に基づく。エージェント、成果物、ゲートを含むステージごとのマトリクス: ARCHITECTURE.md §3 を参照。

---

## v3.0 最適化: AI の構造的限界について発見したこと

### 何が起きたか

高等教育における AI に関する反省記事を書くために ARS を使用していたとき、プロンプトエンジニアリングでは修正できない 3 つの構造的問題に遭遇しました:

1. **フレームロック**: AI に自分の論題に対して devil's advocate ディベートを実行するよう依頼しました。それは実行されました — 4 ラウンド、各ラウンドが前よりも洗練されていました。しかし、すべてのラウンドが私が設定したフレーム内に留まりました。DA は議論を攻撃しましたが、前提を攻撃しませんでした。「そもそも正しい問いを議論しているのか?」と尋ねることは決してありませんでした。これは v2.7 のストレステストで 31% の引用エラー率を引き起こしたのと同じパターンです: 検証する AI と生成する AI は同じ認知フレームを共有しています。

2. **プッシュバック下のシコファンシー**: DA の攻撃に異議を唱えるたびに、すぐに譲歩しすぎました。発見を立ち上げるよりも早く撤回しました。モデルのトレーニングは会話の調和を報酬としているため、「ユーザーがプッシュバックした」ことは攻撃が間違っていた証拠として扱われましたが、多くの場合、それは単にユーザーが粘り強かったことを意味していました。

3. **意図の誤検出**: Socratic Mentor は、私がまだ探索中であるのに、収束して成果物を生成しようとし続けました（「これをまとめましょうか?」）。「ユーザーは深い哲学的議論を望んでいる」と「ユーザーは RQ ブリーフを望んでいる」を区別できませんでした。両方ともエンゲージメントのように見えますが、反対の AI 動作を必要とします。

### 何を変更したか（v3.0）

**Devil's Advocate — 譲歩閾値プロトコル**（`deep-research` + `academic-paper-reviewer`）
- DA は応答前にすべての反論を 1-5 スケールでスコアリングする必要があります
- 譲歩はスコア ≥4（反論が証拠とともに核心攻撃に直接対処）でのみ許可
- スコア ≤3: ポジションを保持し、元の攻撃を再述
- アンチシコファンシールール: 連続譲歩なし、譲歩率追跡、各チェックポイント後のフレームロック検出

**Socratic Mentor — 意図検出層**（`deep-research`）
- 対話開始時と 3 ターンごとにユーザー意図を探索的 vs. 目標指向に分類
- 探索モード: 自動収束を無効化、最大ラウンドを 60 に引き上げ、「まとめましょうか?」プロンプトを禁止
- 目標指向モード: 標準の収束動作
- 早期終了防止ルール: 探索モードでは、ユーザーが停止のタイミングを決定

**Socratic Mentor — 対話健全性インジケーター**（`deep-research`）
- 5 ターンごとに 3 次元でサイレント自己評価: 持続的同意、対立回避、早期収束
- 同意パターンが検出されると、挑戦的な質問を自動注入
- ユーザーには不可視（ゲーミング防止のため）、ただしポストセッションレビュー用のログ利用可能

### なぜ重要か

これらの最適化は AI の構造的限界を解決するわけではありません — 限界を可視化し管理可能にします。DA はまだ十分に押されれば最終的に譲歩します。Socratic Mentor にはまだいくらかの収束バイアスがあります。しかし今や、シコファンシーを遅延させ、DA に譲歩を正当化させ、Mentor がユーザーの準備が整う前にまとめてしまうのを防ぐ明示的なチェックポイントが存在します。

より深い教訓: AI リテラシーとは、AI をツールとして使うことを学ぶこと、倫理ルールに従うこと、AI リスクを恐れることではありません。AI と十分に深く関わって、自分でその構造的限界 — そしてそのプロセスで自分自身の思考の限界 — を発見することです。

---

## ライセンス

この作品は [CC-BY-NC 4.0](https://creativecommons.org/licenses/by-nc/4.0/) でライセンスされています。

**あなたは以下を自由に行うことができます:**
- 共有 — 素材をコピーおよび再配布
- 翻案 — 素材をリミックス、変換、構築

**以下の条件の下で:**
- **表示** — 適切なクレジットを付与する必要があります
- **非商用** — 素材を商業目的で使用してはなりません

**表示フォーマット:**
```
Based on Academic Research Skills by Cheng-I Wu
https://github.com/Imbad0202/academic-research-skills
```

---

## 貢献者

**Cheng-I Wu**（吳政宜）— 著者およびメンテナー

**[aspi6246](https://github.com/aspi6246)** — 貢献者。v3.1 最適化は [Claude-Code-Skills-for-Academics](https://github.com/aspi6246/Claude-Code-Skills-for-Academics) のパターンに触発されました: read-only 制約パターン、ファーストクラス設計としてのアンチパターン体系化、認知フレームワークアプローチ（手順だけでなく「考え方」を教える）、リーンなスキルサイズ哲学。

**[mchesbro1](https://github.com/mchesbro1)** — 貢献者。`academic-paper-reviewer/references/top_journals_by_field.md` 用の IS Basket of 8 ジャーナルを最初に提案・起草（[Issue #5](https://github.com/Imbad0202/academic-research-skills/issues/5)）。

**[cloudenochcsis](https://github.com/cloudenochcsis)** — 貢献者。IS セクションを *Basket of 8* から完全な *Senior Scholars' Basket of 11* に拡張 — *Decision Support Systems*、*Information & Management*、*Information and Organization* を追加（[Issue #7](https://github.com/Imbad0202/academic-research-skills/issues/7)、[PR #8](https://github.com/Imbad0202/academic-research-skills/pull/8)）。出典: [AIS Senior Scholars' List of Premier Journals](https://aisnet.org/research/seniorscholarsbasket/)。

**[eltociear](https://github.com/eltociear)**（Ikko Eltociear Ashimine）— 貢献者。日本語版 README（[`README.ja-JP.md`](README.ja-JP.md)）を翻訳（[PR #161](https://github.com/Imbad0202/academic-research-skills/pull/161)）。

---

## Changelog

### v3.16.0 (2026-07-12) — モデル階層化、クロスモデルゲート強化、WP アドバイザリ精緻化

> **追加:** オプトインのモデル階層化（#517）— 新しい `ARS_MODEL_TIERING` スイッチに 2 方向（`economy`: 13 の実行型エージェントをセッションモデルの 1 段下で派遣、下限は Opus 級；`quality-boost`: 整合性ゲートと最終レビュー面の判断型エージェントをフロンティア段へ引き上げ）；未設定時は旧挙動とバイト等価で、凍結された 39 エージェント分類は新しいマニフェスト + lint で固定。クロスモデルゲート強化（#518）— リスク層別サンプリング（HIGH-IMPACT 参照は両ゲートで 100% 検証）、2 つの不可逆な決定点（設計凍結 + 最終編集判定）でのブラインド不一致チェック、検証モデル id ステータス許可リスト、昇格ベイクオフ・プロトコル；かつて計画されていた汎用第 6 レビュアーは延期ではなく廃止。GPT-5.6 Sol を暫定クロスモデル検証者として掲載し、明示的な reasoning-effort 制御を追加（#515）。devCharlotte 提案の韓国語トリガーキーワード + ルーティング境界フィクスチャ（#452/#509）。論文執筆側に CARS 序論レトリック + タイトル設計リファレンス（#500）。**変更:** WP 研究課題アドバイザリを名詞置換テストで 20 シェル表の外へ一般化（#501）し、装飾型タイトルシェルを捕捉するよう免除条項を精緻化（#505）— held-out 見逃し率 0.34–0.38 → 0.094、誤発火 0/16 を維持；レビュアー校正プロトコルに LLM 審査の寛大化方向を記載（FARS アンカー、#484）；OpenAlex API キー認証 + 予算対応 429 処理 + arXiv ToU 準拠バックオフ（#495/#496）。**ドキュメント:** THIRD_PARTY.md コミュニティディレクトリ（#497/#498）。`academic-pipeline` はスイートに合わせて v3.16.0 へ、他の 3 スキルのバージョンは変更ありません。

### v3.15.0 (2026-07-04) — リリースゲート強化、プロンプト負債整理第 2 弾、ドリフト防止ロック

> リリース規律と品質衛生を中心としたリリースで、スキルの挙動に変更はありません。**追加:** 3 つの CI ゲート — CHANGELOG-covers-merges のタグ前ゲート（#483）、version-consistency の invariant 9-11 とタグ時再実行ゲート（#487）、SessionStart アナウンス一覧を実際の 16 コマンド一覧に固定する command-invariants ゲート（#486）— に加え、2 つのドリフト防止ロック: Phase Boundary の enforcement 文を全 23 の Bucket A エージェントブロックで逐語固定し、SETUP のクロスモデル例を相互および正準モデル表に固定（#491 → #492）。**変更:** プロンプト負債整理第 2 弾は第 1 弾で先送りされた 17 エージェントを精査（#489 → #490）: 両 socratic_mentor の実害ある自己矛盾（期限切れの「15 ラウンドで打ち切り」規則 vs 文書化された典型 20-30 ラウンド）を修正、リポジトリ全体 29 箇所の期限切れ enforcement 状態文を修正、7 エージェントの few-shot と重複プロセス・スキャフォールドを削減 — 4 バッチ並列監査 + 独立 codex クロスモデルチャレンジで検証。監査レポートは `audits/` 配下。**修正:** DOI バッジを shields.io から配信（#482）。`academic-pipeline` はスイートに合わせて v3.15.0 へ、他の 3 スキルのバージョンは変更ありません。

### v3.14.0 (2026-07-02) — Claude Science インポート対応、eval コメント表示、プロンプト負債の整理

> 可搬性と仕上げに焦点を当てたリリースで、スキルの挙動に変更はありません。**追加:** Claude Science インポート対応 — marketplace manifest がスキルパスを明示的に宣言し、symlink の `skills/` ディレクトリを辿れない GitHub API ベースのインポーター（Claude Science「Import from GitHub」、Windows チェックアウト）でも 4 つのスキルすべてが検出されるようになりました。Claude Science 上でエンドツーエンド検証済み、README + SETUP にインポートガイドを追加（#480）。eval-harness の PR コメントは、生の JSON レポート全文の貼り付けに代わり、1 行の判定 + タスク別テーブル + `<details>` に折りたたんだ JSON で表示されます — 表示層のみの変更で、ゲートロジックはバイト単位で不変（#479）。**変更:** 2026-07 の harness-retirement 監査に基づき、4 つのライター系エージェントから期限切れの writing-harness スキャフォールドを除去（#476/#477 → #478、正味 −111 プロンプト行）。PR が新しいトップレベルディレクトリを追加した際に platform-ports ポリシーを通知する remind-don't-block の Platform Port Reminder を追加（#473）。**ドキュメント:** devCharlotte によるネイティブ査読済み韓国語 README（#469/#471）、GitHub Copilot repository instructions（#465）、Skip Permissions より auto permission mode を推奨（#464）。`[Unreleased]` に蓄積されていた 16 件のバックログ（コードはいずれも v3.13.0 タグ以前に反映済み — diff/patch revision mode #390、submission-package verifier #394、eval gold sets #215/#216 ほか）をバージョン記録に統合。詳細は `CHANGELOG.md` を参照。`academic-pipeline` はスイートに合わせて v3.14.0 へ、他の 3 スキルのバージョンは変更ありません。

### v3.13.0 (2026-06-18) — フック移植性、プロバイダ非依存の検証、ガード正確性

> インストール／実行面を堅牢化し、クロスモデルの到達範囲を広げた minor release。**修正：** git-clone + symlink インストール構成でも write-scope ガードがユーザー自身の `CLAUDE.md` を誤って拒否しなくなった（#459、#448/#449 の残り半分を解消——`CLAUDE.md` は enforcement を担うファイルではなくドキュメントなので infra 保護リストから外し、担保ファイルはすべて保護を維持）。Windows の Python フック移植性 + Python 非在時の graceful degradation を、0-byte の Microsoft Store `python3` スタブを拒否しフックログを汚さないクロスプラットフォーム `hooks/run_guard.sh` launcher で実現（#454）。`draft_writer` の dual-phase static union を文書化 + Windows POSIX-safe なパスマッチング（#451）。**追加：** grounded first-party OpenAI と並んで OpenAI 互換エンドポイント（MiMo、DeepSeek、セルフホスト）を受け付けるプロバイダ非依存のクロスモデル検証（first-party は決して暗黙的にダウングレードしない）（#455）。opt-in の Socratic 隣接フレーミング probe（STORM 由来の視点拡張、`ARS_SOCRATIC_ADJACENT_PROBE=1`、デフォルト OFF、prose-layer のみ——`deep-research` 2.10.0 → 2.11.0）（#461）。`academic-pipeline` はスイートに合わせて v3.13.0、`academic-paper` と `academic-paper-reviewer` は変更なし。issue ごとの詳細は `CHANGELOG.md` を参照。

### v3.12.1 (2026-06-15) — 査読応答トリアージモード（PR #433 統合）

> ARS のモードベース・アーキテクチャに従い、外部コントリビューションの真に新規な部分を既存スキルのモードとして取り込んだ patch release。**新モード：** `deep-research` `three-way-scan` —— `quick` と `lit-review` の中間に位置する軽量な WHY/HOW/WHAT 論文比較トリアージ。論文ごとのショートリストと論文間の統合を生成（`deep-research` 2.9.4 → 2.10.0）。`academic-paper` `rebuttal-audit` —— 著者の既存リバッタル／応答ドラフトを査読コメントと突き合わせる独立アドバイザリ QA（コメントごとのカバレッジ表 + ギャップリスト + トーン／根拠／誤読のリスクフラグ）。何も生成せず、スタンドアロン実行時は Schema 11／Material Passport 書き込み／`ready_to_submit` を明示的に抑制（mutation カバレッジ付きの `check_rebuttal_audit_guard()` lint で強制）。加えて `revision-coach` のスコープを反論／不同意の姿勢と非ジャーナル文脈に拡張、`/ars-3w` + `/ars-rebuttal-audit` スラッシュコマンドを追加。入力形状でルーティング：査読コメント AND ドラフト → `rebuttal-audit`、コメントのみ → `revision-coach`。[@Yaobin29](https://github.com/Yaobin29) の [PR #433](https://github.com/Imbad0202/academic-research-skills/pull/433) から統合。スイートのモード数 25 → 27（スキルは 4 つのまま）。issue ごとの詳細は `CHANGELOG.md` を参照。

### v3.12.0 (2026-06-08) — Kong 自動研究フィーチャートラック：実験来歴・図表フィデリティ・論文間矛盾・部分証拠の分解

> **[machine-translated]** この項目は機械翻訳であり、ネイティブ contributor によるレビュー待ちです。正本は英語版 CHANGELOG です。

> Kong et al.（2026、arXiv:2605.18661）の自動研究フィーチャートラックと、部分証拠トラップの分解作業を出荷するマイナーリリース。いずれも個別にレビュー・マージ済み。**新機能：** 実験来歴インテイク + クレーム↔実験アラインメント — 実験に裏付けられたクレームのための schema-first な証拠台帳層で、インテイクとアラインメントのみ（学者が外部で実験を実行し、ARS は決して実行しない）（#260）；キャプションの解釈がデータから導けるか、論文がそのアーティファクトを実際に裏付けるクレームのために引用しているかを検査する図表フィデリティゲート（#261）；評価済みの論文ペアを学者の確認用に列挙可能にする構造化された論文間矛盾インベントリ（#262）；引用判定（#213）と編集統合（#214）の両層で判定前にサブクレーム分解を行い、両層で §F.3.2 部分証拠トラップを収束させる。**ガイダンス・解釈層：** レポート生成レビュアーへの簡潔出力 + 圧力耐性境界の強化（#274）；同一ファミリ／rubric-aware 較正の認識論的注記（#273）；検索コンテンツの命令／データ境界を常設原則として明文化（#367）。**ネガティブスコープ：** Kong META（#255）をクローズし、`POSITIONING.md` に ARS が行わない 5 つの自律的メカニズムを列挙する「拒否されたメカニズム」セクションと 2 つの Tier D 設計教訓ドキュメントを追加。**リリース規律 lint：** version-consistency 不変条件 5–7（#357）と ARCHITECTURE コンポーネントバージョン監査（#345）。さらにクロスモデル grounding ガード（#346 / #349 / #351）、引用ゲートのキャッシュキーと rationale 上限（#359 / #360 / #361）、eval ゴールドセット（#250）、ACL/EMNLP 開示の再接地（#242）の正確性修正を含む。新しいスキーマ、manifest フィールド、すべての不変条件は追加的で後方互換。`academic-pipeline` は suite に追従して v3.12.0、他の 3 つの skill バージョンは変更なし。issue ごとの詳細は `CHANGELOG.md` を参照。

### v3.11.1 (2026-06-06) — 出荷後の正確性・堅牢化・来歴の修正ロールアップ

> v3.11.0 出荷後に表面化した修正をまとめたパッチリリース。いずれも個別にレビュー・マージ済み: integrity-verification + collaboration-depth パスへのクロスモデル同意ゲート拡張 (#322)、エントリ単位の OpenAlex + Crossref バックフィル並列化 (#138)、および引用存在性ゲート・v3.10 ポリシー層・eval ハーネス・ドメイン証拠プロファイル・#310 セキュリティ境界のエッジケースにまたがる 7 件の正確性/堅牢化修正 (#323 / #327 / #328 / #329 / #331 / #332 / #333) — うち 2 件は P1 (#327 no-handoff パスでのドメインプロファイル起動、#328 eval ハーネスのクラス別しきい値ゲート)。新機能なし、破壊的スキーマ変更なし。issue ごとの詳細は `CHANGELOG.md` を参照。

### v3.11.0 (2026-06-04) — 決定論的引用検証ゲート（#182）

> **[machine-translated]** この項目は機械翻訳であり、ネイティブ contributor によるレビュー待ちです。正本は英語版 CHANGELOG です。

> LLM ピアレビューとは独立に動作する**決定論的な引用存在性検証ゲート**を追加。各引用は最大 4 つの書誌インデックス（Semantic Scholar、OpenAlex、Crossref、および新規の **arXiv resolver**、`scripts/arxiv_client.py`、API キー不要）と照合され、引用ごとの `lookup_verified` 状態（`{true, false, unresolvable}`）が統一サマリに書き込まれる。捏造された、解決できない DOI/arXiv ID を持つ引用は、レビュー agent が気づくことを期待するのではなく、lookup によって検出・マークされる（ユーザーが strict を選択したときのみ終止に昇格）。このゲートは **v3.10 の `terminal_policies` opt-in モデルを継承**する。検出は常に実行されるが、`lookup_verified == false` の行が終止的になるのはユーザーが `terminal_policies.citation_existence == strict` を選択したときのみで、デフォルトの挙動は advisory（`/ars-mark-read` で承認可能）である。`false` の定義は意図的に **ID-keyed unmatched に限定**（正確な DOI/arXiv で照会して解決できないことが証明された場合）されており、正当だが未索引の人文系 / 非英語 / 地域ジャーナルの引用は `unresolvable` に分類され、決してブロックされない（ドキュメントに明記された「精度優先・再現率劣後」のトレードオフ）。本バージョンには永続的な SQLite 検証 cache（`~/.cache/ars/verification.db`、90 日 TTL）と `/ars-cache-invalidate` コマンド、独立した `verification_gate` API と `verify_passport.py` CLI、および v3.9.0 の汚染トライアンギュレーション行列を 4 インデックス（k=0..4、すべて advisory）へ拡張したものも含まれる。`academic-pipeline` は suite に追従して v3.11.0、他の 3 つの skill バージョンは変更なし。仕様: `docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md`（§0 amendment + C-V6）。

### v3.10.0 (2026-06-01) — トライアンギュレーション・ポリシー層、Kong サーベイ採用、評価ハーネス、スコープ書き込みガード

> *[machine-translated, pending native review by @eltociear]*
>
> オプトインの汚染トライアンギュレーション **terminal ポリシー層**（#127、デフォルトの引用挙動は v3.9.0 と byte-equivalent）、**Kong et al. 2026 サーベイ採用**（Rebuttal Commitment Ledger #256/#266/#268/#269、分野別の domain evidence profile #259）、**v3.10 計測基盤**（汎用化された評価 gold set + ranking-lift CI gate #184）、**scoped-write guard MVP**（#134、23 個の単一フェーズ subagent を各自の phase ディレクトリに囲い込み、Bash を禁止して Grep/Glob と構造化編集ツールに誘導する deterministic な `PreToolUse` hook）、`/ars-mark-read` plugin コマンド（#190）と broken-on-arrival 修正（#195）、簡体字中国語 README（#185）、CI 強化（#156/#155）をまとめた minor release。`academic-paper` → v3.2.0、`academic-paper-reviewer` → v1.10.0、`academic-pipeline` → v3.10.0。

### v3.9.4.2 (2026-05-19) — PR #149 CI 規律ゲートのポストシップホットフィックス（codex post-ship）

> *[machine-translated, pending native review by @eltociear]*
>
> PR #149（7 つの CI 規律ゲート）の Codex post-ship レビューが 4 つの P2 finding を検出。v3.9.4.2 は 4 つのうち 3 つを強化。F1：`harness-retirement-monthly.yml` に `GH_REPO` を追加し、スケジュール実行が `gh issue create` のための repo context を取得できるようにする。F2：`release-cooldown.yml` が `PREV_TAG` ルックアップを `v*` タグにフィルタリングし、非リリースタグ（例：レガシー plugin タグ）がクールダウンゲートをバイパスできないようにする。F3：`release-cooldown.yml` が annotated タグの subject も読み取り、`hot-fix` スペル変種を受け入れる（v3.9.2 は以前の検出器では false-negative hotfix だった）。PR #157 follow-up：`[skip-cooldown]` override が commit message と annotated タグ message の両方から読み取られるようになる（self-bootstrapping fix — 本タグのクールダウンバイパスが F2+F3 がエンドツーエンドで機能することを実証）。F4（test-count-monotonic 強化）は事前存在する `scripts/` パッケージ問題を surface したため revert され、#154（PR #158 で修正済み）+ 再試行 #155 として追跡。Closes #152。Follow-ups：#155、#156。

### v3.9.4.1 (2026-05-19) — v3.9.4 temporal verification のポストシップホットフィックス（#135 codex post-ship）

> v3.9.4 の Codex post-ship レビューがタスクごとのサブエージェントレビュアーが見逃した 4 つの実バグを検出。ホットフィックスは 4 つすべてにパッチを当てる: (1) `audit()` が `citation_provenance` を P2 と P4 にスルーする — ref slug が `confidence: low` または `conflict` の場合、検証者はタイムライン日付を ground truth として使用する代わりに `TEMPORAL-METADATA-MISSING` を発行する（spec §3.4 first-party safety check が壊れていた）。(2) `_date_to_interval` は `YYYY-MM`（Crossref 月精度）と `YYYY-MM-DD..YYYY-MM-DD`（区間）を含むすべての schema-valid な日付形状をパース。v3.9.4 ではこれらでサイレントに `ValueError` してチェックをスキップしていた。(3) P4 は ref マーカーが不在の場合に直接日付キャプチャをバインドする — 「The 2026 policy enabled the 2020 rollout」のような文が実際にトリガーされるようになる。(4) `citation_provenance.schema.json` `confidence:high` allOf は非 null に加えて存在（`then.required`）を要求し、欠落プロパティバイパスを閉じる。1561 passed（v3.9.4 ベースラインに対して +12 新テスト、ゼロリグレッション）。ARCHITECTURE.md を現在の状態に整合（v3.8.0 で陳腐化していた）。

### v3.9.4 (2026-05-18) — #135 temporal verification 層（advisory）

> Phase 4 → 5 境界における決定論的 advisory 検証者で、5 つの時間的失敗モードをカバー（P1 retrospective arithmetic、P2 anachronistic citation、P3 comparator unmaterialized、P4 causal inversion、P5 deictic present）。新しい Phase 2 兄弟 `timeline_extraction_agent` が `phase2_investigation/timeline.yaml` + `phase2_investigation/citation_provenance.yaml` を所有。検証スクリプト `scripts/temporal_integrity_audit.py` は 5 パスを決定論的に実行。M3 Temporal Integrity Iron Rule を `report_compiler_agent` + `draft_writer_agent` に追加。M6-minimal: Crossref `issued` + pdftotext が first-party 検証をカバー。M7-minimal: 日付来歴 + 比較対象物質化。M5-stub: ユーザー宣言の `version_family_id` のみ。`literature_corpus_entry`、`claim_audit_result`、`claim_intent_manifest` への変更ゼロ。`bibliography_agent` 未変更（F2 不変条件）。3 つの新しいサイドカースキーマ。カバレッジ見積り: ベースライン 55-70% / M7 minimal で 65-75%。1549 passed（+44 新規、ゼロリグレッション）。

### v3.9.3 (2026-05-18) — #128 ハウスキーピング（共有クライアントユーティリティ + dedup リゾルバー）

> 純粋なリファクタリング + v3.9.0 `/simplify` レビューバックログからの 1 つの潜在バグ修正。`scripts/_text_similarity.py`（3-way クライアント dedup: normalize / similarity / threshold / retry 定数）+ `scripts/_passport_yaml.py`（2-way migration tool dedup: ruamel.yaml round-trip 設定）+ プライベート `_resolve_by_doi_then_title` ヘルパー（2-way リゾルバーボディ dedup、§3.4 / §3.5 API サーフェス保持）を抽出。OpenAlex + Crossref にわたるスロットル測定を `time.monotonic` に標準化（`time.time` だった、NTP-unsafe）、Semantic Scholar と整合。5 つすべてのモジュールレベルクロスインポートにおけるデュアルパスインポートインフラストラクチャ（兄弟ファースト、namespace-package フォールバック）は、`SemanticScholarUnavailable` のクラスアイデンティティを保持し、2 つの潜在的に壊れた `import scripts.X` パスをボーナス修正。1505 passed（+23 新規、ゼロリグレッション）。#128 §4（OA + CR をエントリーごとに並列化）は #138 に持ち越し。

### v3.9.2 (2026-05-18) — #133 フェーズ境界ホットフィックス

> #133 クロージャー（ホットフィックス層）。長期的アーキテクチャ修正は #134 の v3.10 active conductor として追跡。追加: CLAUDE.md のルーティング明確化ゲート（クロスフェーズ素材 → サイレントディスパッチではなく a-d オプションで明確化）、22 のシングルフェーズエージェントがプロンプトハードフェンス（`## Phase Boundary (v3.9.2)`）を取得、16 のマルチフェーズ / フェーズ直交 / クロスフェーズメタエージェントは意図的に未フェンス（正直なフレーミング — 散文プラセボは false-enforcement の錯覚を生む）、advisory 検証者 `scripts/check_pipeline_integrity.py` は #133 パターンを post-hoc 検出。クロスモデルスポットチェック付きの動作スモークテスト（100% Opus 4.7、≥75% Sonnet + GPT-5.5）。

### v3.9.1 (2026-05-18) — #129 + #130 クライアントハードニング

> v3.9.0 ホットフィックス。OpenAlex / Crossref レスポンス読み取り失敗を `*Unavailable` としてラップ（#129）。非文字列の `manifest_id` に対して `check_claim_audit_consistency` をガード（#130）。仕様変更なし。

### v3.9.0 (2026-05-17) — #102 cross-index triangulation measurement

> #102 クロージャー。v3.7.3 は single-index（Semantic Scholar）汚染検出を出荷。v3.9.0 は **advisory 証拠のみ** として three-index triangulation（S2 + OpenAlex + Crossref）に拡張。2 つの新しいオプションブール（`openalex_unmatched`、`crossref_unmatched`）を `contamination_signals` に追加。manual-entry not-rule を対称的に拡張。Finalizer は 4 段の advisory matrix（present `*_unmatched` フィールドに対する k=0/1/2/3）を追加し、v3.7.3 レガシー `CONTAMINATED-UNMATCHED` は k=1/k_max=1 S2 のみのケースで保持。Formatter pass-through 許可リストは 3 → 9 suffixes に拡張。refusal rules 1-10 は R-L3-2-E に従い未変更。ポリシー層（strict modes、hard-block tier、`venue_type` / `triangulation_policy`）は spec §2.3 に従い v3.10 まで保留。k=3 マーカーは `CONTAMINATED-TRIANGULATION-UNMATCHED`（推論された原因ではなく観測可能を記述）。3 つの新しい firm rules: R-L3-2-C（k は present フィールドに対して計算）、R-L3-2-D（API 推論分類なし）、R-L3-2-E（refusal リスト未変更、pass-through 許可リストは拡張）。

**Migration:** v3.7.3 コーパス — `python scripts/migrate_literature_corpus_to_v3_9_0.py PATH` を実行して 2 つの新しいフィールドをバックフィル。Pre-v3.7.3 コーパス — `migrate_literature_corpus_to_v3_7_3.py` を FIRST に実行、その後 v3.9.0 migration（spec §3.7 に従いデイジーチェーン化、v3.9.0 ツールは既に `contamination_signals.semantic_scholar_unmatched` を持つエントリーのみに作用）。

### v3.8.2 (2026-05-17) — #118 uncited audit_tool_failure サーフェス

> #118 クロージャー。`ARS_CLAIM_AUDIT=1` uncited constraint-judging パスは以前、`JudgeInvocationError` 時にサイレントに `{"judgment": "NOT_VIOLATED"}` を代入し、過渡的な judge 停止時に HIGH-WARN constraint チェックを抑制していた。v3.8.2 はこれらの失敗を専用の `uncited_audit_failures[]` 集約に MED-WARN advisory tier でルーティングし、cited path INV-14 行をミラーするが、`claim_audit_result.ref_slug` が必須で uncited パスにバインドする ref がないため専用スキーマを使用。#118 issue body の 4 つの option-1..4 トレードオフは option 2（新集約）に落ち着いた — option 4（再 raise してアボート）は flaky judge エンドポイント上の監査カバレッジヒットのため却下。

- **新規 `uncited_audit_failure.schema.json` 集約**（spec §3.6）。constraint judge が `JudgeInvocationError` を発生させた uncited 文 × manifest ペアごとに 1 エントリー。cited-path INV-14 と同じ fault-class enum（`judge_timeout` / `judge_api_error` / `judge_parse_error` / `cache_corruption` / `retrieval_api_error` / `retrieval_timeout` / `retrieval_network_error`）。`rule_version: D4-c-v1-uaf-v1`。
- **UAF-INV-1..UAF-INV-6 lint**（spec §6 rule 4d）。`finding_id` 一意性、scoped_manifest_id クロスアレイ整合性、manifest_claim_id が非 null の場合の (M, C) ペア整合性、(sentence, manifest) ごとの dedup、rationale fault_class プレフィックス、`constraint_violations[]` に対するクロス集約排他性。
- **Finalizer §5 MED-WARN advisory 行**: アノテーション `[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — <fault-class>]`、ゲートはパス（次パス再試行修復）。Formatter REFUSE リスト未変更 — UAF は advisory。
- **パイプライン統合**（`scripts/claim_audit_pipeline.py`）: line 1211-1224 の swallow サイトを削除。`JudgeInvocationError` は UAF 行を発行し、次の (sentence, manifest) ペアに `continue`。偽の NOT_VIOLATED が `constraint_violations[]` に達することはない。
- **テスト**: 18 新規（15 schema/lint TSUAFUncitedAuditFailureInvariants + 3 パイプライン統合 TP23UncitedJudgeOutageEmitsUAF）。ベースライン 694 → 712 テスト、ゼロリグレッション。
- **Agent doc**（`academic-pipeline/agents/claim_ref_alignment_audit_agent.md`）: 出力発行テーブルが 7 行目に成長。エラーハンドリングテーブルが uncited-path UAF 行で 3 サーフェスから 4 サーフェスに成長。

### v3.8.0 (2026-05-16) — L3 Claim-Faithfulness Locator + Audit（ペアマイルストーン）

> v3.7.3 + v3.8 は L3（主張忠実性）ギャップを end-to-end で閉じる。v3.7.3 はロケーターインフラストラクチャを出荷 — 各引用は三層アンカーを持ち、将来の監査が引用された一節を取得できる。v3.8 はそれらのアンカーを消費し、引用元が主張を支持するかどうかを判断し、formatter ターミナルハードゲートで HIGH-WARN 違反を gate-refuse する監査パスを出荷。リリースは v3.7.0 以降蓄積された 5 つの audit-trail-shipped feature PR（#104 / #105 / #108 / #111 / #115）もバンドル。

- **#103 — `claim_ref_alignment_audit_agent`**（v3.8 PR #121）。オプトイン（`ARS_CLAIM_AUDIT=1`、デフォルト OFF）Stage 4→5 監査エージェント。サンプリングされた各引用を取得された抜粋に対して判断。`claim_audit_results[]` + `claim_intent_manifests[]` + `claim_drifts[]` + `uncited_assertions[]` + `constraint_violations[]` 集約を発行。8 行の finalizer matrix が HIGH-WARN クラス（CLAIM-NOT-SUPPORTED / NEGATIVE-CONSTRAINT-VIOLATION / FABRICATED-REFERENCE / ANCHORLESS / CONSTRAINT-VIOLATION-UNCITED）を formatter REFUSE rules 6-10 を通じてルーティング。キャリブレーションランナーは 20-tuple ゴールドセット（T-C1 FNR<0.15 + FPR<0.10、T-C2 per-class、T-C3 shape integrity）と共に出荷。デュアルトラックレビュー 8 ラウンド（R1 codex + Gemini-3.1-pro-preview、Gemini クォータ消費後 R2-R8 codex のみ）。軌跡 R1 4P1+2P2 → R8 0P1+4P2 ship gate。
- **v3.7.3 — Three-Layer Citation Emission + 汚染シグナル**（PR #98）。`synthesis_agent` / `draft_writer_agent` / `report_compiler_agent` が `## Three-Layer Citation Emission (v3.7.3)` H2 を取得。各 `<!--ref:slug-->` は `<!--anchor:<kind>:<value>-->` を伴い、`<kind> ∈ {quote, page, section, paragraph, none}`（quote アンカーは 25 語に制限、URL エンコード）。`pipeline_orchestrator_agent` finalizer は precedence-zero NO-LOCATOR チェックを持つ 5 セルに。`formatter_agent` は `[UNVERIFIED CITATION — NO QUOTE OR PAGE LOCATOR]` の明示的ハードゲート拒否を追加。`literature_corpus_entry.schema.json` はオプションの `contamination_signals: { preprint_post_llm_inflection, semantic_scholar_unmatched }` オブジェクトを追加。`bibliography_agent` は取り込み時に両シグナルを計算。11 ラウンドのレビュー軌跡（Codex×10 + Gemini cross-model×1）が 22 件の発見をクローズ。Spec: `docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md`。外部動機: Zhao ら arXiv:2605.07723（2026-05）。
- **#108 — AI disclosure policy-anchor renderer**（audit-trail-shipped 2026-05-14）。既存の venue-track renderer に加えて PRISMA-trAIce / ICMJE / Nature / IEEE policy-anchor 開示パスを追加。
- **#111 — `slr_lineage` emission on systematic-review → academic-paper handoff**（2026-05-15）。Schema 9 オプションブール `slr_lineage` フィールド。プロデューサ `pipeline_orchestrator_agent` はすべてのハンドオフ遷移で書き込み。コンシューマ `disclosure` モードは §4.3 G2 invariant track gate に従い `--policy-anchor=prisma-trAIce` をディスパッチ。
- **#104 — README motivation: Zhao et al. corpus-scale evidence anchor**（2026-05-15）。README + `README.zh-TW.md` motivation セクションが Zhao らの 146,932 ハルシネーション引用発見に対して v3.7.x ラインをフレーミング。
- **#105 — v3.7.3 contamination_signals backfill migration tool**（2026-05-15）。`scripts/migrate_literature_corpus_to_v3_7_3.py` は pre-v3.7.3 passports にわたって両汚染シグナルをレトロ計算。
- **#115 — Semantic Scholar client maturity**（2026-05-15）。`scripts/semantic_scholar_client.py` は 1-req/s スロットル（`S2_API_KEY` 検出時に 0.1s に下げる）、URLError 上の停止ラッチ、長期実行クロスパスポートバッチ用の `reset_outage_latch()` を追加。

### v3.7.0 (2026-05-05) — Claude Code プラグインパッケージング

> プラグインパッケージングアップグレード: ARS は `/plugin marketplace add Imbad0202/academic-research-skills` + `/plugin install academic-research-skills` 経由で Claude Code CLI / VS Code / JetBrains 上に 1 行でインストール可能に。従来の `git clone + ~/.claude/skills/ へのシンボリックリンク` フローも引き続き動作 — 両トラックともファーストクラス。

- **プラグインマニフェスト + marketplace メタデータ**（Phase 1、PR #68）。`.claude-plugin/plugin.json` がスイートを宣言（`skills/` ディレクトリから相対シンボリックリンク経由で 4 スキルが自動検出）。`.claude-plugin/marketplace.json` がプラグインを登録し、単一の GitHub ホスト型エンドポイントが marketplace リストとプラグインソースの両方を提供。README + `README.zh-TW.md` + `docs/SETUP.md` がデュアルトラックインストール手順を保持。
- **10 スラッシュコマンド**（`commands/ars-*.md`、Phase 2.1、PR #69）が `MODE_REGISTRY.md` エントリーを `/ars-<mode>` トリガーにマッピング。モデルルーティングは各コマンドの frontmatter にピン留め — `full` と `revision-coach` には `opus`（アーキテクチャ / レビュー解釈の深さ）、他の 8 には `sonnet`。プロジェクトポリシーに従い Haiku なし。
- **3 プラグイン出荷エージェント**（`agents/*_agent.md`、Phase 2.1、PR #69）は `deep-research/agents/` の v3.6.7 ハードン済みダウンストリームエージェントへの相対シンボリックリンク: `synthesis_agent`、`research_architect_agent`、`report_compiler_agent`。アンダースコアファイル名は `scripts/check_v3_6_7_pattern_protection.py` のハードピン留めパスと INV-3 manifest-confined Clause 1 invariant をそのままにするため保持。シンボリックリンク（コピーではない）が単一のソースオブトゥルースを保持し、v3.6.7 §6 inversion sweep + INV-1/2/3 lint が閉じる Pattern C3 attack surface を防止。
- **`model: inherit`** がそれら 3 つのソースエージェント frontmatter に追加。`sonnet` ピン留めの代わりに inherit を選択したのは、ARS フルパイプラインを実行している opus セッションが（キャップされる代わりに）opus エージェントを保持できるようにするため。ユーザーの `~/.claude/hooks/warn-agent-no-model.sh` PreToolUse hook はディスパッチング境界で Haiku をゲートするため、`inherit` は既に Haiku フリーのモデルを通じて解決される。
- **SessionStart announce hook**（`hooks/hooks.json` + `scripts/announce-ars-loaded.sh`、Phase 2.2、PR #70）。プラグインがロードされると、hook が `additionalContext` を注入して 10 スラッシュコマンド、3 プラグインエージェント、トークン予算ポインタを LLM の最初のターンに列挙。`startup` と `clear` ソース値はフル announce を取得。`resume` と `compact` はコンテキストを消費しないよう 1 行 ack を取得。Bash 3.2 互換 — `brew install bash` 要件なしで macOS ストック `/bin/bash` 上で実行。
- **Phase 2.2 スコープ削減**: `SubagentStop → run_codex_audit.sh` codex audit hook は契約ギャップ（SubagentStop ペイロードは stage/deliverable info を運ばないため、ラッパーは必要な引数を半推論する必要がある）と invoker-class 境界（`run_codex_audit.sh` lines 4-7 は同一セッション in-LLM 呼び出しを禁止、PostToolUse は producing session 内で発火）のため v3.7.0 でスコープアウト。実際の audit-hook 統合は ARS が stage/deliverable 伝播契約を獲得するときの将来のリリースに延期。`docs/design/2026-04-30-ars-v3.7.0-plugin-packaging-roadmap.md` Update note 2026-05-05（Phase 2.2 scope reduction）を参照。
- **`docs/PERFORMANCE.md` + `.zh-TW.md`** が「v3.7.0 Plugin agents and model routing」サブセクションを取得し、inherit セマンティクスと現在の 3 エージェントスコープ境界を説明。
- **3 PR にわたる Codex レビューチェーン**: 8 ラウンドのインラインイテレーティブ + 3 ラウンドの fresh PR レベル、すべてマージ前に 0 P0/P1/P2 findings に収束。Phase 2.2 fresh PR レビューがインラインラウンドが見逃した 1 つの P2（スペース付きインストールパスを壊す未引用 `${CLAUDE_PLUGIN_ROOT}`）をキャッチ — 実装レビュー（インライン）と契約レビュー（fresh）の分離価値を確認。
- **何が変更されなかったか**: 4 つのスキルディレクトリ、25 モードすべて、エージェントプロンプト、スキーマファイル、lint 契約。プラグインパッケージングは新しいトップレベルサーフェス（`commands/`、`agents/`、`hooks/`、`.claude-plugin/`、`skills/` シンボリックリンクディレクトリ、3 つのプラグインエージェント `model: inherit` frontmatter 追加）のみを追加。既存の 4.3k clone-install ユーザーは破壊的変更を見ない。

### v3.6.8 (2026-05-03) — Generator-Evaluator Contract Gate（v3.6.6 spec ship）

> ネーミングノート: このリリースは **v3.6.6 generator-evaluator contract** spec と
> 実装を出荷。v3.6.6 作業はプロジェクトシーケンシングのため v3.6.7 後にランディング。
> 設計ドキュメントは契約ゲートバージョンの v3.6.6 内部命名を保持し、
> スイートリリースは CHANGELOG を monotonic に保つため v3.6.8 とタグ付け。

- **Schema 13.1**（`shared/sprint_contract.schema.json`）が Schema 13 を拡張し、2 つの新しい `mode` enum 値（`writer_full` + `evaluator_full`）、2 つの新しいオプショントップレベルフィールド（`pre_commitment_artifacts` writer のみ、`disagreement_handling` evaluator のみ）、reviewer- / writer- / evaluator-conditional ゲートを強制する 12 の `allOf` ブランチを追加。既存の reviewer 契約は Schema 13.1 でバイト等価で検証（§3.6 zero-touch promise）。
- **2 つの新しい出荷契約テンプレート** が `shared/contracts/writer/full.json`（D1-D7、F1/F4/F2/F3/F0）と `shared/contracts/evaluator/full.json`（D1-D5、F1/F2/F3/F6/F4/F5/F0）の下に。spec ブランチの設計時 artefacts から Schema 13.1 アップグレードと共にアトミックに live shipped status に昇格。
- **二相オーケストレーション** が `academic-paper full` 内: Phase 4 が Phase 4a（writer paper-blind pre-commitment）+ Phase 4b（writer paper-visible drafting + self-scoring）に分割。Phase 6 が Phase 6a（evaluator paper-blind pre-commitment）+ Phase 6b（evaluator paper-visible scoring + decision）に分割。Phase 番号付き `<phase4a_output>` / `<phase6a_output>` データデリミタが v3.6.2 reviewer pattern をミラー。Lint カウントサマリー: writer 3+4 / evaluator 5+5 / reviewer 5+6（reviewer は zero-touch のまま）。
- **`academic-paper` SKILL + エージェントファイル** が逐語的 `## v3.6.6 Generator-Evaluator Contract Protocol` ブロックを取得（SKILL.md で 101 行 + `draft_writer_agent.md` で 47 行 + `peer_reviewer_agent.md` で 57 行）。SKILL.md は v3.6.7+ 用の graceful-degradation + cross-session resume forward notes を運ぶ新しい `## Known limitations` セクションも追加。
- **バリデーター拡張**: `scripts/check_sprint_contract.py` SC-* mode-gating audit（SC-5 + SC-11 reviewer のみ。SC-9 は全 3 モードファミリーに拡張）。17 新規テストがバリデーターユニットテストカウントを 54 から 71 に（positive + 5 schema-branch negative + 2 §3.6 reviewer regression + 6 mode-gating tests）。
- **マニフェスト CI lint**: `scripts/check_v3_6_6_ab_manifest.py` が `tests/fixtures/v3.6.6-ab/manifest.yaml` 上の §6.2 manifest schema + §6.5 git-tracked invariants を強制。`.github/workflows/spec-consistency.yml` が既存の reviewer ループと並んで writer + evaluator テンプレートディレクトリを反復するよう sprint contract validation ループを拡張、加えて新しい manifest CI lint を実行。
- **A/B evidence fixture stub** が `tests/fixtures/v3.6.6-ab/`（30 ファイル）: manifest + README + 6 paper-A inputs/baseline + 1 paper-C inputs/baseline + Stage 3 reviewer excerpt + 6 codex-judge baseline placeholders。実際の fixture データは実装作業が完全に完了する前にフォローアップコミットで投入される。

### v3.6.7 (2026-04-30) — Downstream-Agent Pattern Protection（Step 1+2）

- **3 ダウンストリームエージェントが 18 の文書化されたハルシネーション/ドリフトパターンのうち 13 に対してハードン**: `synthesis_agent`（A1-A5 narrative-side）、`research_architect_agent` の survey-designer mode（B1-B5 instrument-side）、`report_compiler_agent` の abstract-only mode（C1-C3 publication-side）。各エージェントプロンプトは `PATTERN PROTECTION (v3.6.7)` ブロックを保持。
- **`shared/references/` の 4 リファレンスファイル**: `irb_terminology_glossary.md`、`psychometric_terminology_glossary.md`、`protected_hedging_phrases.md`、`word_count_conventions.md`。リファレンスファイルはエージェントプロンプトがパスで引用する運用契約を保持。
- **クロスモデル監査プロンプトテンプレート** が `shared/templates/codex_audit_multifile_template.md` に、7 監査次元と `report_compiler_agent` バンドル用の必須 3 部構成 Section 4(f) チェック付き。任意のサブチェックの失敗は P1 finding。
- **静的 lint + 29 テストミューテーションスイート**: `scripts/check_v3_6_7_pattern_protection.py` は保護条項の存在と義務句シェイプを強制。`scripts/test_check_v3_6_7_pattern_protection.py` は codex レビュー証拠を保存し、将来のチェッカーリグレッションが CI に現れるようにする。両方とも `.github/workflows/spec-consistency.yml` にワイヤード。
- **Codex レビュー履歴**: `gpt-5.5` + `xhigh` クロスモデルレビューの 7 ラウンドが SHIP-OK にゼロ P1+P2 findings で到達。Step 6（orchestrator runtime hooks）と Step 8（synthetic eval case）はフォローアップ PR で出荷。

### v3.6.5 (2026-04-27) — Material Passport `literature_corpus[]` Consumer Integration

- **2 つの Phase 1 文献コンシューマ** をワイヤード: `deep-research/agents/bibliography_agent.md` と `academic-paper/agents/literature_strategist_agent.md`。両方とも passport が非空の `literature_corpus[]` を運ぶ場合、同じ 5 ステップ **corpus-first, search-fills-gap** フローと同じ 4 つの Iron Rules（Same criteria / No silent skip / No corpus mutation / Graceful fallback on parse failure）に従う。
- **PRE-SCREENED 再現性ブロック** が Search Strategy レポートに: 含まれた / 除外された / スキップされたコーパスエントリーを列挙、F3 zero-hit note と `obtained_via` / `obtained_at` の部分宣言を中心に構成する F4a-F4f provenance reporting 付き。`final_included = pre_screened_included[] ∪ external_included[]` は中立を保持 — bibliography エントリーや literature matrix 行に provenance タグなし。
- **コンシューマプロトコルリファレンス** が `academic-pipeline/references/literature_corpus_consumers.md` に、正規 PRE-SCREENED テンプレート、BAD/GOOD 例、4 Iron Rules、コンシューマごとの読み取り手順付き。
- **CI lint** `scripts/check_corpus_consumer_protocol.py` がマニフェスト駆動コンシューマリスト（`scripts/corpus_consumer_manifest.json`）で 9 つのプロトコル不変条件を強制。
- **Schema 9 caveat 廃止**: `shared/handoff_schemas.md` が v3.6.4 「Consumer-side integration deferred to v3.6.5+」caveat を廃止。コンシューマプロトコルへのバックポインタに置換。
- 存在ベース、スキーマ変更なし、新しい env flag なし。パース失敗は `[CORPUS PARSE FAILURE]` サーフェスを持つ external-DB-only フローにフォールバック。`citation_compliance_agent` コーパス統合は延期（ターゲットバージョン post-v3.8 TBD）。
- 破壊的変更なし。既存のユーザーアダプターは変更なしで動作。

### v3.6.4 (2026-04-25) — Material Passport `literature_corpus[]` Input Port

- **`literature_corpus[]` フィールド** がユーザー所有文献のオプション入力ポートとして Schema 9 に追加。各エントリーは `shared/contracts/passport/literature_corpus_entry.schema.json`（CSL-JSON authors、year、title、source_pointer + private optional `abstract` / `user_notes`）に準拠。
- **言語中立アダプター契約** が `academic-pipeline/references/adapters/overview.md` に: 任意のプログラム（任意の言語）がユーザーコーパスソースを読み取り、準拠 `passport.yaml` + `rejection_log.yaml` を生成可能。Fail-soft エントリーレベルエラー、fail-loud アダプターレベルエラー、決定論的順序付け。
- **3 つのリファレンス Python アダプター** が `scripts/adapters/` の下: `folder_scan.py`（PDF のファイルシステム）、`zotero.py`（Better BibTeX JSON エクスポート）、`obsidian.py`（vault frontmatter）。出発点のみ。ユーザーは非リファレンスソース用に独自のアダプターを書くことが期待される。
- **拒否ログ契約** が `shared/contracts/passport/rejection_log.schema.json` に、カテゴリカル理由値の閉じた enum 付き。常に発行（拒否がない場合は空）。
- **CI ゲート**: `scripts/check_literature_corpus_schema.py` はスキーマ + アダプター例を検証。`scripts/sync_adapter_docs.py --check` は schema→docs ドリフトを防止。新しい `pytest.yml` ワークフローはパスフィルタトリガーで `scripts/adapters/tests/` を実行。
- **v3.6.4 では Input-port-only**: v3.6.4 はコンシューマ統合なしでスキーマとアダプター契約を出荷。`bibliography_agent` と `literature_strategist_agent` は v3.6.5 でワイヤード。
- 破壊的変更なし。

### v3.6.3 (2026-04-23) — Opt-in Passport Reset Boundary

- **オプトイン passport reset boundary**（`ARS_PASSPORT_RESET=1`）。各 FULL チェックポイントを context-reset boundary に昇格。新しい `resume_from_passport=<hash>` モードがユーザーに Material Passport ledger だけから fresh Claude Code セッションで再開を許可。`systematic-review` モードでフラグ ON は各 FULL チェックポイントでリセットを必須にする。他モードはリセットを flag-gated default として扱う。Flag OFF は pre-v3.6.3 動作をバイト単位で保持。
- Schema 9 が 2 つのエントリー種別（`kind: boundary` + `kind: resume`）を持つ append-only `reset_boundary[]` ledger を取得。Hash は JSON Canonical Form + SHA-256 を使用し、self-reference safety 用の正規プレースホルダー付き。オプションの `pending_decision` は MANDATORY ブランチ選択を処理。
- 新しい `scripts/check_passport_reset_contract.py` CI lint: フラグへの各言及は authoritative protocol doc へのポインタを共存させる必要。
- プロトコルドキュメント: `academic-pipeline/references/passport_as_reset_boundary.md`。
- `docs/PERFORMANCE.md` を長期実行セッションガイダンスで更新。
- 破壊的変更なし。Flag default は OFF。

### v3.6.2 (2026-04-23) — Reviewer Sprint Contract Hard Gate

v3.6.2 は Schema 13 sprint contracts と、reviewer に論文を読む前にスコアリングプランをプリコミットさせるハードゲートオーケストレーションを導入。Reviewer のみのファーストテストケース。writer/evaluator は v3.6.4 まで延期。CHANGELOG を参照。

- **Schema 13 sprint contract** が `panel_size`、`acceptance_dimensions`、`failure_conditions`（`severity` precedence + panel-relative `cross_reviewer_quantifier` 付き）、`measurement_procedure`、オプションの `override_ladder`、bounded `agent_amendments` 付き。バリデーター: `scripts/check_sprint_contract.py`。
- **Two-call hard gate.** Reviewer は paper-content-blind Phase 1 + paper-visible Phase 2 を実行。Phase 1 出力は self-injection サーフェスを狭めるため `<phase1_output>...</phase1_output>` データデリミタにラップ。
- **Synthesizer three-step mechanical protocol.** cross-reviewer matrix を構築 → panel-relative quantifier + recognised expression vocabulary で各 `failure_condition` を評価 → `severity` で precedence を解決。Forbidden-ops リストは `editorial_synthesizer_agent` で明示的。
- **2 つの reviewer テンプレート出荷**（`shared/contracts/reviewer/full.json` panel 5。`shared/contracts/reviewer/methodology_focus.json` panel 2）。`reviewer_re_review`、`reviewer_calibration`、`reviewer_guided` はスキーマ enum で予約されているが v3.6.2 では契約テンプレートなしで出荷。pre-v3.6.2 動作を保持。`reviewer_quick` は enum から完全に除外。
- `academic-paper-reviewer` SKILL バージョン: `1.8.1 → 1.9.0`。`academic-pipeline` SKILL バージョン: `3.5.1 → 3.6.2`（suite-version invariant）。Suite バージョンは `3.6.2` にバンプ。
- spec [`docs/design/2026-04-23-ars-v3.6.2-sprint-contract-design.md`](docs/design/2026-04-23-ars-v3.6.2-sprint-contract-design.md) とプロトコル [`academic-paper-reviewer/references/sprint_contract_protocol.md`](academic-paper-reviewer/references/sprint_contract_protocol.md) を参照。

### v3.5.1 (2026-04-22) — Opt-in Socratic Reading-Check Probe

v3.5.1 は Socratic Mentor にオプトイン honesty probe を追加（`ARS_SOCRATIC_READING_PROBE=1`）。デフォルト off。CHANGELOG を参照。

- **オプトイン reading-check probe**: `ARS_SOCRATIC_READING_PROBE=1` が設定されている場合、Socratic Mentor はユーザーが特定の論文を引用した目標指向セッション中に 1 回限りの honesty probe を発火。辞退はペナルティなしでログ記録。結果は Research Plan Summary と Stage 6 AI Self-Reflection Report に流れる。新エージェントなし、スキーマ変更なし。
- `deep-research` SKILL バージョン: `2.9.0 → 2.9.1`。`academic-pipeline` SKILL バージョン: `3.5.0 → 3.5.1`。Suite バージョンは `3.5.1` にバンプ。

### v3.5.0 (2026-04-21) — Collaboration Depth Observer

- **新エージェント**: `academic-pipeline` の `collaboration_depth_agent`（Agent Team が 3 から 4 に成長）。各 FULL/SLIM チェックポイントとパイプライン完了時に呼び出され、user-AI コラボレーションを 4 次元ルーブリックに対してスコアリング。**Advisory のみ — 進捗を決してブロックしない。** MANDATORY チェックポイント（Stages 2.5 / 4.5 integrity gates）は observer を呼び出さない。
- **新しいルーブリック**: [`shared/collaboration_depth_rubric.md`](shared/collaboration_depth_rubric.md) v1.0。次元: Delegation Intensity、Cognitive Vigilance、Cognitive Reallocation、Zone Classification（Zone 1 / Zone 2 / Zone 3）。Wang, S., & Zhang, H.（2026）。"Pedagogical partnerships with generative AI in higher education: how dual cognitive pathways paradoxically enable transformative learning." *International Journal of Educational Technology in Higher Education*, 23:11. DOI [10.1186/s41239-026-00585-x](https://doi.org/10.1186/s41239-026-00585-x) に基づく。
- **クロスモデル divergence をフラグ、平均化しない**: `ARS_CROSS_MODEL` が設定されている場合、observer は両モデルで実行。次元の不一致 > 2 ポイントはサイレントに平滑化されるのではなく報告される。`ARS_CROSS_MODEL_SAMPLE_INTERVAL` がコストトレードオフの escape hatch。
- **Short-stage guard**: 5 未満のユーザーターンを持つステージは、フルモデル observer をディスパッチする代わりに静的 `insufficient_evidence` ブロックを注入。
- **アンチシコファンシー規律**: スコア ≥ 7 は特定の対話ターン引用を要求。Zone 3 は再監査をトリガー。motivational framing なし。
- `academic-pipeline` SKILL バージョン: `3.3.0 → 3.4.0`。Suite バージョンは `3.5.0` にバンプ。新しい lint `scripts/check_collaboration_depth_rubric.py` + 10 テスト。

### v3.4.0 (2026-04-20) — Compliance Agent + Schema 12

- **Compliance Agent**（shared）: PRISMA-trAIce 17 items（SR mode のみ）+ RAISE 4 principles + 8-role matrix を実行する単一の mode-aware エージェント。既存の Stage 2.5 / 4.5 Integrity Gates にフック。tier-based block（Mandatory → block、HR → warn、R/O → info）。非 SR エントリーは principles-only、warn-only を実行。
- **Schema 12 compliance_report** が `compliance_history[]`（append-only）経由で Material Passport に追加。
- **3 ラウンドユーザーオーバーライドラダー** が `disclosure_addendum` を原稿に自動注入。検出回避不可能。
- **キャリブレーションと透明な報告**、ハード FNR/FPR ゲートなし — `task_type: open-ended` と自己整合的。
- **上流フレッシュネス CI** が PRISMA-trAIce ドリフトを警告（非ブロッキング）。
- **長期実行セッションドキュメント**: cross-session resume メカニズムとしての Material Passport。

### v3.3.6 (2026-04-15) — README Streamlining + ARCHITECTURE doc

- パイプライン構造（フロー、マトリクス、データアクセス、依存グラフ、品質ゲート、モード）の単一ソースオブトゥルースとして `docs/ARCHITECTURE.md` を追加。PR #18 経由で main にマージ。
- `docs/SETUP.md`（前提条件、API キー、Pandoc/tectonic、クロスモデル検証、インストール方法）と `docs/PERFORMANCE.md`（トークン予算、推奨 Claude Code 設定）を追加。README はインライン化する代わりに両方にリンク。
- README を合理化: ASCII パイプライン図と 16 ポイント key-feature リストを削除（ARCHITECTURE.md に置換）。Skill Details セクションはバージョン番号をアンカーし、エージェントごとの名簿について ARCHITECTURE.md §3 にリーダーをポイントする。
- 注: どのスキルにも機能変更なし。純粋なドキュメント再編成。Suite バージョンは `3.3.6` にバンプ。

### v3.3.5 (2026-04-15)
- `benchmark_report.schema.json` + Material Passport 上の `repro_lock` オプションブロックを追加。両方ともパターンドキュメント、lint、例と共に出荷。最初の正式な Python 開発 dep マニフェスト（`requirements-dev.txt`）。

### v3.3.4 (2026-04-15) — README Changelog Sync Patch

- `README.md` と `README.zh-TW.md` の埋め込み変更履歴セクションを同期し、欠落していた `v3.3.3` と `v3.3.2` のリリースサマリーを含める。
- 将来の README changelog ドリフトが CI を失敗させるよう `scripts/check_spec_consistency.py` を拡張。
### v3.3.3 (2026-04-15) — Release Prep + Lint Hardening

- SKILL frontmatter linting をハードン: 閉じる `---` フェンスの欠落が有効な YAML としてパースされる代わりにクリーンに失敗するように。
- 有効な YAML としてパースされるが mapping としてではない frontmatter がクラッシュする代わりに読みやすいエラーを報告するように。
- 両 READMEs の post-publication audit report の壊れた showcase リンクを修正。
- spec consistency check に README 相対リンク検証を追加し、デッドリンクが CI を失敗させるように。
- ドキュメント全体で DOCX 出力契約を整合: 直接 `.docx` 生成は Pandoc 依存、フォールバックとしての Markdown + 変換手順。
- `v3.3.3` リリースを準備: suite バージョンバンプ、`academic-paper` -> v3.0.2、`academic-pipeline` -> v3.2.2。

### v3.3.2 (2026-04-15) — Data Access Levels + Task Type Metadata

- すべてのトップレベル `SKILL.md` ファイルに強制語彙付き `metadata.data_access_level` を追加: `raw`、`redacted`、`verified_only`。
- すべてのトップレベル `SKILL.md` ファイルに強制語彙付き `metadata.task_type` を追加: `open-ended`、`outcome-gradable`。
- 両メタデータフィールド用の lint スクリプトとユニットテストを追加。GitHub Actions spec consistency ワークフローにワイヤード。
- `shared/ground_truth_isolation_pattern.md` を追加し、`shared/handoff_schemas.md` から新しい語彙にリンク。

### v3.3.1 (2026-04-14) — Spec Consistency Patch

- README、`.claude/CLAUDE.md`、`MODE_REGISTRY.md`、`SKILL.md` ファイルを現在のモードカウントと公開されたスキルバージョンに同期。
- クロスモデルの表現を修正: integrity sample checks と independent DA critique は今日実装済み。sixth-reviewer ピアレビューは計画中のまま。
- 適応的チェックポイントセマンティクスを明確化し、SLIM チェックポイントが明示的なユーザー確認を依然として待つように。
- Stage 2.5 と Stage 4.5 integrity gates がスキップできないことを再確認。
- 将来のドリフトを捕捉する軽量な spec consistency check と GitHub Actions ワークフローを追加。

### v3.3 (2026-04-09) — PaperOrchestra-Inspired Enhancements

[PaperOrchestra](https://arxiv.org/abs/2604.05018)（Song, Song, Pfister & Yoon, 2026, Google）からの技術を統合。

- **Semantic Scholar API Verification** — S2 API 経由の Tier 0 programmatic reference existence check。Levenshtein >= 0.70 タイトルマッチング、DOI 不一致検出、S2 IDs 経由の bibliography deduplication。API 利用不可時の graceful degradation。
- **Anti-Leakage Protocol** — Knowledge Isolation Directive がセッション素材を LLM パラメトリックメモリより優先。コンテンツが欠落している場合、メモリから埋める代わりに `[MATERIAL GAP]` をフラグ。Mode 5/6 失敗リスクを削減。
- **VLM Figure Verification**（オプション）— ビジョン対応 LLM を使用したレンダリング図表のクローズドループ検証。10 ポイントチェックリスト、最大 2 リファインメント反復。
- **Score Trajectory Protocol** — 改訂ラウンドにわたる次元ごとのルーブリックスコアデルタ追跡（7 次元）。リグレッション（delta < -3）を検出し、必須チェックポイントをトリガー。
- **Stage 2 Parallelization** — 可視化と argument 構築はアウトライン完了後に並列実行可能。
- 新バージョン: deep-research v2.8、academic-paper v3.0、academic-pipeline v3.2

### v3.2 (2026-04-09) — Lu 2026 Nature 統合

Lu ら（2026、*Nature* 651:914-919）からの洞察を統合 — ブラインドピアレビューに合格した最初のエンドツーエンド自律 AI 研究システム。

- **7 モード AI Research Failure Mode Checklist** — 疑われる実装バグ、ハルシネーション結果、shortcut reliance、bug-as-insight、方法論の捏造、フレームロックに対して Stage 2.5/4.5 でパイプラインをブロック。既存の 5 タイプ引用ハルシネーション分類を拡張。
- **Reviewer Calibration Mode**（academic-paper-reviewer v1.8）— ユーザー提供ゴールドセットに対するオプトイン FNR/FPR/balanced-accuracy 測定。5× アンサンブル、クロスモデル default-on、session-scoped confidence disclosure。
- **Disclosure Mode**（academic-paper v2.9）— venue 固有 AI 使用ステートメントジェネレーター。v1 は ICLR、NeurIPS、Nature、Science、ACL、EMNLP をカバー。
- **Early-Stopping Criterion**（academic-pipeline v3.1）— パイプライン開始時の収束チェック + 予算透明性。
- **Fidelity-Originality Mode Spectrum** — Lu 2026 Fig 1c に従い 3 スキルにわたるすべてのモードを分類。
- 新バージョン: academic-paper v2.9、academic-paper-reviewer v1.8、academic-pipeline v3.1

### v3.1.1 (2026-04-09) — IS Senior Scholars' Basket of 11

外部貢献: [@mchesbro1](https://github.com/mchesbro1) が IS Basket of 8 ジャーナルを最初に提案・起草（[Issue #5](https://github.com/Imbad0202/academic-research-skills/issues/5)）。[@cloudenochcsis](https://github.com/cloudenochcsis) が完全な Senior Scholars' Basket of 11 に拡張（[Issue #7](https://github.com/Imbad0202/academic-research-skills/issues/7)、[PR #8](https://github.com/Imbad0202/academic-research-skills/pull/8)）。`academic-paper-reviewer/references/top_journals_by_field.md` Section 7 を更新し、*Decision Support Systems*、*Information & Management*、*Information and Organization* を追加。出典: [AIS Senior Scholars' List of Premier Journals](https://aisnet.org/research/seniorscholarsbasket/)。

### v3.1 (2026-04-06) — Anti-Context-Rot + 認知フレームワーク + リーンサイズ

[aspi6246/Claude-Code-Skills-for-Academics](https://github.com/aspi6246/Claude-Code-Skills-for-Academics) のパターンに触発される。

**Wave 1: Anti-Context-Rot Anchors**
- 4 スキルすべてにわたる 29 の明示的アンチパターン（スキルあたり 7-8、「Why It Fails」+ 「Correct Behavior」の表形式）
- 長い会話でも違反してはならない重要なルールに 22 IRON RULE マーカー
- academic-paper-reviewer の read-only 制約（reviewer は原稿を修正できない）

**Wave 2: トレーサビリティ + 認知フレームワーク + 強化**
- R&R Traceability Matrix（Schema 11）: 再レビュー出力に「Author's Claim」と「Verified?」列を追加し、改訂主張の独立検証を可能に
- エージェントに「何をするか」だけでなく「どう考えるか」を教える 3 つの認知フレームワークリファレンスファイル:
  - `argumentation_reasoning_framework.md` — Toulmin model、Bradford Hill 因果推論、inference to best explanation、epistemic status classification
  - `review_quality_thinking.md` — 3 つのレンズ（internal validity、external validity、contribution）、一般的なレビュアートラップ、キャリブレーション質問
  - `writing_judgment_framework.md` — clarity test、reader's journey、discipline-specific voice、revision decision matrix
- 会話中強化プロトコル: パイプライン遷移ごとのステージ固有 IRON RULE + アンチパターンリマインダー
- 各 FULL チェックポイントでのセルフチェック質問（引用整合性、シコファント譲歩、品質軌跡、スコープ規律、完全性）

**Wave 3: リーンスキルサイズ**
- SKILL.md 合計サイズを 142KB から 85KB（-40%）に削減、詳細プロトコルを `references/` ファイルに抽出
- ~15 の新しいリファレンスファイル作成（re-review プロトコル、ガイドモード、systematic review、process summary、external review など）
- すべての IRON RULE マーカーは SKILL.md に保持。詳細コンテンツはオンデマンドでロード
- 新バージョン: deep-research v2.7、academic-paper v2.8、academic-paper-reviewer v1.7、academic-pipeline v3.0

### v3.0 (2026-04-03) — Anti-Sycophancy + Intent Detection + Dialogue Health
- **Devil's Advocate Concession Threshold**（deep-research + academic-paper-reviewer）: DA は応答前に反論を 1-5 スコアリング必要。譲歩は ≥4 でのみ。連続譲歩なし。譲歩率追跡。各チェックポイント後のフレームロック検出。
- **Attack Intensity Preservation**（academic-paper-reviewer）: DA はプッシュバック下でソフト化しない。明示的な deflection 検出付き Rebuttal assessment プロトコル。アンチシコファンシールールが持続的プッシュバックを有効な証拠として扱われるのを防ぐ。
- **Intent Detection Layer**（deep-research socratic）: ユーザー意図を探索的 vs. 目標指向に分類。探索モードは自動収束を無効化、最大ラウンドを引き上げ、早期終了を禁止。3 ターンごとに再評価。
- **Dialogue Health Indicator**（deep-research socratic）: 5 ターンごとに持続的同意、対立回避、早期収束のサイレントセルフチェック。同意パターン検出時に挑戦を自動注入。
- **Cross-Model Verification Protocol**（shared、オプション）: 整合性検証サンプルクロスチェックと independent DA critique のために GPT-5.4 Pro または Gemini 3.1 Pro を使用。Sixth-reviewer ピアレビューは計画中、まだ実装されていない。`ARS_CROSS_MODEL` env var を設定してアクティベート — それなしですべて以前と同様に動作。完全なセットアップガイド、API パターン、コスト見積りについては `shared/cross_model_verification.md` を参照。
- **AI Self-Reflection Report**（academic-pipeline Stage 6）: AI 動作パターンのポストパイプラインセルフアセスメント — DA 譲歩率、チェックポイントスキップ率、健全性アラート、シコファンシーリスク評価（LOW/MEDIUM/HIGH）、フレームロックインシデント、収束パターン分析。皮肉な注意事項を含む: 「このセルフリフレクションはシコファントだった可能性のある同じ AI によって生成されている」。
- 起源: DA が早すぎる譲歩をし、Socratic Mentor が早期に収束しようとし、ディベート全体が人間が設定したフレーム内にロックされた 4 ラウンド弁証法実験を通じて発見。
- バージョン: deep-research v2.5、academic-paper-reviewer v1.5、academic-pipeline v2.8

### v2.9.1 (2026-04-03) — Skill Metadata
- 4 つの SKILL.md frontmatters すべてに `status: active` と `related_skills` クロスリファレンスを追加。
- `deep-research` ↔ `academic-paper` ↔ `academic-paper-reviewer` ↔ `academic-pipeline` にわたるスキル検出ツールとクロススキルナビゲーションを有効化。

### v2.9 (2026-03-27) — Style Calibration + Writing Quality Check
- **Style Calibration**（academic-paper intake Step 10、オプション）: 3 つ以上の過去論文を提供すると、パイプラインがあなたのライティングボイス — 文章リズム、語彙の好み、引用統合スタイル — を学習。ドラフティング中のソフトガイドとして適用。学問分野の慣習が常に優先される。優先システム: 学問分野規範（ハード）> ジャーナル慣習（強）> 個人スタイル（ソフト）。`shared/style_calibration_protocol.md` を参照
- **Writing Quality Check**（`academic-paper/references/writing_quality_check.md`）: ドラフトのセルフレビュー中に適用されるライティング品質チェックリスト。5 カテゴリー: AI 高頻度用語警告（25 用語）、句読点パターン制御（em dash ≤3）、throat-clearing オープナー検出、構造パターン警告（Rule of Three、均一段落、同義語循環）、burstiness チェック（文章長さの変動）。これらは良いライティングルール — 検出回避ではない
- **Style Profile** が academic-pipeline Material Passport（`shared/handoff_schemas.md` の Schema 10）を通じて運ばれる
- **deep-research** report compiler もオプションで両機能を消費
- バージョン: academic-paper v2.5、deep-research v2.4、academic-pipeline v2.7

### v2.8 (2026-03-22) — SCR Loop Phase 1: State-Challenge-Reflect
- **Socratic Mentor Agent**（deep-research + academic-paper）: SCR（State-Challenge-Reflect）プロトコル統合
  - **Commitment Gates**: 各層/章遷移で証拠を提示する前にユーザー予測を収集
  - **Certainty-Triggered Contradiction**: 高信頼言語（「明らかに」、「明白に」）を検出し、反対意見を導入
  - **Adaptive Intensity**: コミットメント精度を追跡し、チャレンジ頻度を動的に調整
  - **Self-Calibration Signal (S5)**: 対話にわたるユーザーのセルフキャリブレーション成長を追跡する新しい収束シグナル
  - **SCR Switch**: ユーザーは「skip the predictions」と言って無効化、または「turn predictions back on」と言って対話中に再有効化できる。ソクラテス式質問は通常通り続く
- `deep-research/references/socratic_questioning_framework.md`: SCR Overlay Protocol が SCR フェーズをソクラテス機能にマッピング
- `CHANGELOG.md` を追加

### v2.7 (2026-03-09) — Integrity Verification v2.0: アンチハルシネーションオーバーホール
- **integrity_verification_agent v2.0**: Anti-Hallucination Mandate（AI メモリ検証なし）、グレーゾーン分類の排除（VERIFIED/NOT_FOUND/MISMATCH のみ）、各参照に対する必須 WebSearch 監査トレイル、Stage 4.5 fresh independent verification、Gray-Zone Prevention Rule
- **既知のハルシネーションパターン**: GPTZero × NeurIPS 2025 研究からの 5 タイプ分類（TF/PAC/IH/PH/SH）、5 つの複合欺瞞パターン、実世界ケーススタディ、文献統計
- **出版後監査**: すべての 68 参照のフル WebSearch 検証で 21 の問題を発見（31% エラー率）、3 ラウンドの整合性チェックを通過 — 外部検証の必要性を証明
- **論文修正**: 4 つの捏造参照を削除、6 つの著者エラーを修正、7 つのメタデータエラーを修正、2 つのフォーマット問題を修正

### v2.6.2 (2026-03-09) — 意図ベースモードアクティベーション
- **deep-research**: ソクラテスモードがキーワードマッチングの代わりに **意図ベースアクティベーション** を使用するように。どの言語でも動作 — 特定の文字列をマッチする代わりに意味を検出（例: 「ユーザーはガイド付き思考を望んでいる」）。
- **academic-paper**: Plan モードが **意図ベースアクティベーション** を使用するように。「ユーザーは開始方法に不確実である」や「ユーザーはステップバイステップガイダンスを望んでいる」のような意図シグナルをどの言語でも検出。
- 両モードに **デフォルトルール** が追加: 意図が曖昧な場合、`full` よりも `socratic`/`plan` を優先 — 最初にガイドする方が安全。
- 二層アーキテクチャ: Layer 1（スキルアクティベーション）はマッチング信頼度のためバイリンガルキーワードを使用。Layer 2（モードルーティング）は言語非依存意図シグナルを使用。

### v2.6.1 (2026-03-09) — バイリンガルトリガーキーワード
- **deep-research**: 一般アクティベーションとソクラテスモード用の繁體中文トリガーキーワードを追加。
- **academic-paper**: 繁體中文トリガーキーワードと Plan Mode trigger セクションを追加。
- 両モード選択ガイドにバイリンガル例と中国語固有のミスセレクションシナリオを含めるように。

### v2.6 / v2.4 / v1.4 (2026-03-08) — 15+ の改善
- **deep-research v2.3**: 新しい systematic-review / PRISMA mode（7 番目）。3 つの新エージェント（risk_of_bias、meta_analysis、monitoring）。PRISMA プロトコル/レポートテンプレート。ソクラテス収束基準（4 シグナル + 自動終了）。Quick Mode Selection Guide
- **academic-paper v2.4**: 2 つの新エージェント（visualization、revision_coach）。4 ステータスタイプ付き改訂追跡テンプレート。引用フォーマット変換（APA↔Chicago↔MLA↔IEEE↔Vancouver）。統計可視化標準。ソクラテス収束基準。改訂回復例。**LaTeX 出力ハードニング** — 必須 `apa7` document クラス、テキスト justification 修正（`ragged2e` + `etoolbox`）、テーブル列幅式、バイリンガル要旨センタリング、標準化フォントスタック（Times New Roman + Source Han Serif TC VF + Courier New）、tectonic のみで PDF
- **academic-paper-reviewer v1.4**: 行動指標付き 0-100 採点の品質ルーブリック。決定マッピング（≥80 Accept、65-79 Minor、50-64 Major、<50 Reject）。Quick Mode Selection Guide
- **academic-pipeline v2.6**: 適応的チェックポイントシステム（FULL/SLIM/MANDATORY）。整合性チェックでの Phase E Claim Verification。中間エントリープロブナンス用 Material Passport。クロススキルモードアドバイザー（14 シナリオ）。チームコラボレーションプロトコル。拡張ハンドオフスキーマ（9 スキーマ）。整合性失敗回復例

### v2.4 / v1.3 (2026-03-08)
- **academic-pipeline v2.4**: 新しい Stage 6 PROCESS SUMMARY — 構造化された論文作成プロセスレコードを自動生成（MD → LaTeX → PDF、バイリンガル）。必須最終章: 6 次元 1-100 採点（Direction Setting、Intellectual Contribution、Quality Gatekeeping、Iteration Discipline、Delegation Efficiency、Meta-Learning）の **Collaboration Quality Evaluation**、誠実なフィードバック、改善推奨事項。パイプラインを 9 ステージから 10 ステージに拡張

### v2.3 / v1.3 (2026-03-08)
- **academic-pipeline v2.3**: Stage 5 FINALIZE がフォーマッティングスタイル（APA 7.0 / Chicago / IEEE）を要求するように。PDF は `tectonic` 経由で LaTeX からコンパイル必須（HTML-to-PDF なし）。APA 7.0 はバイリンガル CJK サポート用 XeCJK 付き `apa7` document クラス（`man` mode）を使用。フォントスタック: Times New Roman + Source Han Serif TC VF + Courier New

### v2.2 / v1.3 (2025-03-05)
- **Cross-Agent Quality Alignment**: すべてのエージェントにわたる統一定義（peer-reviewed、currency rule、CRITICAL severity、source tier）
- **deep-research v2.2**: synthesis アンチパターン、ソクラテス自動終了条件、DOI+WebSearch 検証、拡張倫理整合性チェック、モード遷移マトリクス
- **academic-paper v2.2**: 4 レベル argument スコアリング、剽窃スクリーニング、2 つの新しい失敗パス（F11 Desk-Reject Recovery、F12 Conference-to-Journal）、Plan→Full モード変換
- **academic-paper-reviewer v1.3**: DA vs R3 役割境界、CRITICAL finding 基準、合意分類（4/3/SPLIT/DA-CRITICAL）、信頼スコア重み付け、アジア・地域ジャーナルリファレンス
- **academic-pipeline v2.2**: チェックポイント確認セマンティクス、モード切り替えマトリクス、失敗フォールバックマトリクス、状態オーナーシッププロトコル、素材バージョン制御

### v2.0.1 (2026-03)
- **4 つの SKILL.md を簡素化**（-371 行、-16.5%）: クロススキル重複の削除、インラインテンプレート → ファイル参照、冗長ルーティングテーブル、重複モード選択セクション
- academic-paper と academic-pipeline 間の改訂ループキャップ矛盾を修正

### v2.0 (2026-02)
- **academic-pipeline v2.0**: 5→9 ステージ、必須整合性検証、二段階レビュー、ソクラテス改訂コーチング、再現性保証
- **academic-paper-reviewer v1.1**: +Devil's Advocate Reviewer（7 番目のエージェント）、+re-review mode（検証）、+ポストレビューソクラテスコーチング
- 新エージェント: `integrity_verification_agent` — 監査トレイル付き 100% 参照/データ検証
- 新エージェント: `devils_advocate_reviewer_agent` — 8 次元論題チャレンジャー
- 出力順: MD → 利用可能な場合 Pandoc 経由 DOCX（それ以外は手順）→ LaTeX を尋ねる → 確認 → PDF

### v1.0 (2026-02)
- 初回リリース
- deep-research v2.0（10 エージェント、socratic を含む 6 モード）
- academic-paper v2.0（10 エージェント、plan を含む 8 モード）
- academic-paper-reviewer v1.0（6 エージェント、guided を含む 4 モード）
- academic-pipeline v1.0（オーケストレーター）
