# Academic Research Skills for Claude Code

[![Version](https://img.shields.io/badge/version-v3.16.0-blue)](https://github.com/Imbad0202/academic-research-skills/releases/tag/v3.16.0)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.20696614-blue)](https://doi.org/10.5281/zenodo.20696614)
[![License: CC BY-NC 4.0](https://img.shields.io/badge/license-CC%20BY--NC%204.0-lightgrey)](https://creativecommons.org/licenses/by-nc/4.0/)
[![Sponsor](https://img.shields.io/badge/sponsor-Buy%20Me%20a%20Coffee-orange?logo=buy-me-a-coffee)](https://buymeacoffee.com/crucify020v)

[English](README.md) | [简体中文版](README.zh-CN.md) | [日本語版](README.ja-JP.md) | [한국어](README.ko-KR.md)

一套完整的學術研究 Claude Code 技能包，涵蓋從研究到論文出版的全流程。

**30 秒安裝**（Claude Code CLI / VS Code / JetBrains，v3.7.0+）：

```text
/plugin marketplace add Imbad0202/academic-research-skills
/plugin install academic-research-skills
```

裝完跑 `/ars-plan`，ARS 會用蘇格拉底對話幫你規劃章節結構。需要前置條件或傳統 symlink 安裝請看 [快速安裝](#快速安裝)。

> **AI 是你的副駕駛，不是機長。** 這工具不會幫你寫論文。它處理苦工 — 搜文獻、排格式、驗數據、查邏輯一致性 — 讓你專注在真正需要你腦子的事：定義問題、選方法、詮釋數據的意義、寫出「我認為」後面那句話。
>
> 跟 humanizer 不同，這工具不是幫你隱藏用 AI 協作的事實，而是幫你把關文章品質。風格校準從你過去的文章學習你的聲音，寫作品質檢查抓出讓文字讀起來像機器產的模式。目標是品質，不是遮掩。

### 為什麼選「人機協作」而不是「全自動」？

Lu 等人（2026，*Nature* 651:914-919）發表的 **The AI Scientist** 是第一個端到端全自動的 AI 研究系統，其生成的論文通過 ICLR 2025 workshop 的盲審（評分 6.33/10，workshop 平均 4.87）。他們自己的 Limitations 段落也列出了這類系統會遇到的結構性失敗模式：實作錯誤、幻覺實驗結果、取巧特徵依賴、實作錯誤被包裝成「意外發現」、方法論偽造、框架鎖定、引用幻覺。

ARS 建立在這個前提上：**人類研究者 + AI 的組合，比純自動或純人工都更能避開這些失敗模式**。Stage 2.5 與 Stage 4.5 誠信閘門執行 7 類阻斷式檢查清單（見 [`academic-pipeline/references/ai_research_failure_modes.md`](academic-pipeline/references/ai_research_failure_modes.md)），reviewer 也提供 opt-in 的 calibration mode 用使用者自備的 gold set 測量 FNR/FPR。

[**Zhao 等人**](https://arxiv.org/abs/2605.07723)（2026-05）盤點了 arXiv、bioRxiv、SSRN、PMC 上 250 萬篇論文裡的 1.11 億筆引用，保守估計 2025 年單年就有 146,932 筆幻覺引用，並觀察到 2024 年中是上升的拐點；bioRxiv-to-PMC 這條配對的「預印本進到正式發表」幻覺存活率達 85.3%。他們把「真實引用被用來支撐被引文獻其實沒有提出的主張」描述為當前未解的問題。ARS v3.7.1 為來源 provenance 加上 trust-chain frontmatter，v3.7.3 為未來的 claim-level 稽核鋪上 locator 基礎建設（三層引用 anchor），並在引用時段帶出 advisory 風險訊號（ARS 內部把這條 claim-faithfulness 缺口標記為「L3」，此為 ARS 的用詞，不是論文的用詞）。v3.7.x 的設計動機來自 Zhao 等人的 corpus-scale 發現；ARS 本身的 corpus-scale 評估仍是未來工作。

v3.8 補上 L3 缺口的另一半。v3.7.3 讓每一筆引用都帶 locator anchor，v3.8 在這個基礎上加一道 opt-in 稽核（`ARS_CLAIM_AUDIT=1`）：抓回每一個 anchor 指向的原始文本，判斷論文裡的 claim 是否真有被該引用支撐。五類新的 HIGH-WARN annotation（claim-not-supported、negative-constraint-violation、fabricated-reference、anchorless、constraint-violation-uncited）會在 formatter terminal hard gate 直接攔下輸出。Calibration 隨 release 出 20 筆 gold set，採 FNR<0.15、FPR<0.10 雙閾值；正式放大投入前要先有 calibration 證據（v3.8 spec §5）。

v3.3 的靈感來自 [**PaperOrchestra**](https://arxiv.org/abs/2604.05018)（Song, Song, Pfister & Yoon, 2026, Google）：Semantic Scholar API 驗證、反洩漏協議、VLM 圖表驗證、分數軌跡追蹤。

---

## 架構與 pipeline

**👉 [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md)** — 完整 pipeline 視圖：流程圖、階段 × 維度矩陣、資料存取流、skill 依賴圖、品質閘門、模式清單。

這份架構文件取代了原本散在 README 各處的 pipeline 描述。關於「哪個階段跑什麼」的所有資訊都集中在一個地方。

## 快速安裝

**前置條件**

- [Claude Code](https://docs.claude.com/en/docs/claude-code/setup)（建議最新版；plugin packaging 需要近期版本）
- 已 export `ANTHROPIC_API_KEY`，或第一次跑 `claude` 時設定
- *選用：* Pandoc 用於 DOCX 輸出，tectonic + 思源宋體 TC 用於 APA 7.0 PDF（純 Markdown 輸出兩個都不需要）

**Plugin 安裝（v3.7.0+，推薦）：**

```text
/plugin marketplace add Imbad0202/academic-research-skills
/plugin install academic-research-skills
```

**驗證可用：** 跑 `/ars-plan` 並描述你正在寫的論文，ARS 會用蘇格拉底對話幫你規劃章節結構。想要單次測試的話改跑 `/ars-lit-review "你的主題"`。

**👉 [docs/SETUP.zh-TW.md](docs/SETUP.zh-TW.md)** — 完整指南：安裝 Claude Code、設定 API key、選用的 Pandoc/tectonic（DOCX/PDF）、跨模型驗證（`ARS_CROSS_MODEL`），以及六種安裝方式（Plugin、專案 skills、全域 skills、claude.ai Project、repo clone、Claude Science 匯入）。

**使用 Claude Science？** 四個 skill 可直接匯入：**Skills → Import from GitHub**，貼上 `https://github.com/Imbad0202/academic-research-skills`，按 **Preview**，再按 **Import 4 skills**（需本 repo v3.14.0+——匯入器讀取 marketplace manifest 中明列的 skill 路徑）。匯入是單次快照：ARS 更新後需重新匯入。匯入的 skill 承載 ARS 方法論（研究／寫作／審查協定）；Claude Code 專屬機制——slash commands、hooks、subagent 編排——不會轉移。細節見 [docs/SETUP.zh-TW.md](docs/SETUP.zh-TW.md) 方法五。

**用 Codex CLI？** 請改裝姊妹版：[`Imbad0202/academic-research-skills-codex`](https://github.com/Imbad0202/academic-research-skills-codex)。同一套 workflow 內容，Codex 原生包裝為單一 `$academic-research-suite` skill，提供 `ars-*` 別名。

## 效能與費用

**👉 [docs/PERFORMANCE.zh-TW.md](docs/PERFORMANCE.zh-TW.md)** — 各模式 token 預算、完整 pipeline 估算（一篇 15k 字論文約 ~$4–6），以及建議的 Claude Code 設定（Auto 模式；Agent Team 選用）。

## 使用指南與文章

- [學術寫作不該是一個人的事：一套開源 AI 協作工具如何改變研究者的工作流](https://open.substack.com/pub/edwardwu223235/p/ai?r=4dczl&utm_medium=ios) — 完整使用指南（繁體中文）
- [Academic Writing Shouldn't Be a Solo Act](https://open.substack.com/pub/edwardwu223235/p/academic-writing-shouldnt-be-a-solo?r=4dczl&utm_medium=ios) — Full pipeline walkthrough (English)

---

## 功能特色一覽

- **Deep Research** — 13 個 Agent 的研究團隊，支援蘇格拉底引導、PRISMA 系統性回顧、意圖偵測、對話健康度監控、可選跨模型 DA、Semantic Scholar API 驗證。
- **Academic Paper** — 12 個 Agent 的論文撰寫團隊，含風格校準、寫作品質檢查、LaTeX 輸出強化、視覺化、修訂教練、引用格式轉換、反洩漏協議、VLM 圖表驗證。
- **Academic Paper Reviewer** — 7 個 Agent 的多視角同儕審查，0-100 品質量表（主編 + 3 位動態審查者 + 魔鬼代言人），含讓步門檻協議、攻擊強度保持、可選跨模型 DA critique / calibration、R&R 追溯矩陣、唯讀約束。
- **Academic Pipeline** — 10 階段全流程調度器，含自適應 checkpoint、宣稱驗證、素材護照、可選 `repro_lock`、可選跨模型誠信驗證、中途強化機制、分數軌跡追蹤。
- **資料存取層級標註**（v3.3.2+）— 每個 skill 宣告 `data_access_level`（`raw` / `redacted` / `verified_only`），由 `scripts/check_data_access_level.py` 強制執行。設計靈感來自 Anthropic 的 automated-w2s-researcher（2026）。詳見 [`shared/ground_truth_isolation_pattern.md`](shared/ground_truth_isolation_pattern.md)。
- **任務類型標註**（v3.3.2+）— 每個 skill 宣告 `task_type`（`open-ended` 或 `outcome-gradable`）。目前 ARS 所有 skills 皆為 `open-ended`。
- **Benchmark 報告 Schema**（v3.3.5+）— JSON Schema + lint script，要求誠實的 benchmark 比較報告。詳見 [`shared/benchmark_report_pattern.md`](shared/benchmark_report_pattern.md)。
- **Artifact 可重現性 Lockfile**（v3.3.5+）— Material Passport 新增可選 `repro_lock` 子區塊。**是設定文件化，不是重播保證** — LLM 輸出不是位元可重現。詳見 [`shared/artifact_reproducibility_pattern.md`](shared/artifact_reproducibility_pattern.md)。
- **實驗來源憑證登錄**（#260）— Material Passport 可選的 `experiment_provenance[]` 記錄研究者在**外部**跑過的實驗（ARS 從不執行實驗），論文宣稱透過 `claim_intent_manifest.planned_experiment_ids[]` 與之 join。誠信 gate（Stage 2.5/4.5）逐條比對實驗支撐型宣稱與登錄憑證 — `ALIGNED` / `OVERSTATED` / `NOT_SUPPORTED_BY_PROVENANCE` / `PROVENANCE_INSUFFICIENT` — **但不判定實驗本身是否正確**。fail-closed 的 `experiment_intake_declaration` 讓「有沒有跑實驗」成為 Stage 1 明確決定。詳見 [`shared/handoff_schemas.md`](shared/handoff_schemas.md)。

---

## 實際產出展示

查看完整 10 階段 pipeline 的實際產出 — 包含**同儕審查報告、誠信驗證報告、完稿論文**：

**[瀏覽所有 pipeline 產出 →](examples/showcase/)**

| 產出物 | 說明 |
|---|---|
| [完稿論文（英文）](examples/showcase/full_paper_apa7.pdf) | APA 7.0 格式，LaTeX 編譯 |
| [完稿論文（中文）](examples/showcase/full_paper_zh_apa7.pdf) | 中文版，APA 7.0 |
| [誠信報告 — 審稿前](examples/showcase/integrity_report_stage2.5.pdf) | Stage 2.5：抓出 15 個虛構引用 + 3 個統計錯誤 |
| [誠信報告 — 最終](examples/showcase/integrity_report_stage4.5.pdf) | Stage 4.5：確認零回歸 |
| [同儕審查第一輪](examples/showcase/stage3_review_report.pdf) | 主編 + 3 審查者 + 魔鬼代言人 |
| [複審](examples/showcase/stage3prime_rereview_report.pdf) | 修訂後驗證審查 |
| [同儕審查第二輪](examples/showcase/stage3_review_report_r2.pdf) | 追蹤審查 |
| [回覆審查意見](examples/showcase/response_to_reviewers_r2.pdf) | 逐點回覆 |
| [出版後稽核報告](examples/showcase/post_publication_audit_2026-03-09.pdf) | 獨立全引用稽核：發現 21/68 篇問題，通過了 3 輪誠信審查仍漏網 |

---

## 搭配工具：Experiment Agent

如果你的研究需要在寫作前跑實驗（程式碼或人工研究），[Experiment Agent](https://github.com/Imbad0202/experiment-agent) 技能填補 ARS Stage 1（研究）和 Stage 2（寫作）之間的空缺。

```
ARS Stage 1 研究      →  RQ Brief + Methodology Blueprint
        ↓
  experiment-agent     →  執行/管理實驗 → 驗證結果
        ↓
ARS Stage 2 寫作      →  用驗證過的實驗結果撰寫論文
```

**功能**：執行程式碼實驗（Python、R 等）並即時監控、管理人工研究 protocol 與 IRB 倫理審查、11 種統計謬誤偵測、重現性驗證。

**搭配使用方式**：ARS pipeline 跑完 Stage 1 後暫停，在另一個 experiment-agent session 中跑實驗，完成後將結果（含 Material Passport）帶回 ARS Stage 2。ARS 不需要任何修改。詳見 [experiment-agent README](https://github.com/Imbad0202/experiment-agent)。

---

## 使用方式

### 快速開始

```
# 啟動完整研究 pipeline
你: "我想做一篇關於 AI 對高教品保影響的研究論文"

# 蘇格拉底引導模式
你: "引導我研究 AI 在教育評鑑中的應用"

# 引導式論文撰寫
你: "引導我寫一篇關於少子化影響的論文"

# 審查現有論文
你: "幫我審查這篇論文"（接著提供論文）

# 查看 pipeline 進度
你: "進度" 或 "status"
```

### 個別 Skill 使用

#### Deep Research（深度研究，8 種模式）

```
"研究 AI 對高等教育的影響"                    → full mode（完整研究）
"給我一份 X 的快速摘要"                       → quick mode（快速簡報）
"幫我做 X 的系統性文獻回顧，含 PRISMA"        → systematic-review mode
"引導我研究 X"                                → socratic mode（蘇格拉底引導）
"幫我查核這些說法"                            → fact-check mode（事實查核）
"幫我做文獻回顧"                              → lit-review mode（文獻回顧）
"審查這篇論文的研究品質"                      → review mode（論文審查）
```

#### Academic Paper（學術論文撰寫，11 種模式）

```
"幫我寫一篇論文"                              → full mode（完整撰寫）
"引導我寫論文"                                → plan mode（引導規劃）
"先幫我搭論文大綱"                            → outline-only mode（只做大綱）
"我有初稿，這是審稿意見"                      → revision mode（修訂）
"幫我整理這些審稿意見成修訂路線圖"            → revision-coach mode
"幫我寫這篇的摘要"                            → abstract-only mode（摘要）
"把這批資料寫成文獻回顧論文"                  → lit-review mode（文獻回顧論文）
"轉換成 LaTeX" / "引用格式轉 IEEE"            → format-convert mode（格式轉換）
"檢查引用格式"                                → citation-check mode（引用檢查）
"幫我生成 NeurIPS 的 AI 使用揭露"             → disclosure mode（AI 揭露）
```

#### Academic Paper Reviewer（論文審查，6 種模式）

```
"審查這篇論文"                                → full mode（主編 + R1/R2/R3 + 魔鬼代言人）
"快速評估這篇論文"                            → quick mode（快速評估）
"引導我改進這篇論文"                          → guided mode（引導改進）
"檢查研究方法"                                → methodology-focus mode（方法論聚焦）
"驗收修訂"                                    → re-review mode（再審驗收）
"用我的 gold set 校準 reviewer"               → calibration mode（校準）
```

#### Academic Pipeline（全流程調度器）

```
"我想做一篇完整的研究論文"                    → 從 Stage 1 開始完整 pipeline
"我已經有論文，幫我審查"                      → 從 Stage 2.5 進入（先做誠信審查）
"我收到審稿意見了"                            → 從 Stage 4 進入
```

> Pipeline 結束時自動產出 **Stage 6：過程紀錄** — 含論文創建過程紀錄與 6 維度協作品質評估（1–100 分）。

### 支援語言

- **繁體中文** — 使用者以中文對話時預設使用
- **English** — 使用者以英文對話時預設使用
- 學術論文自動產出雙語摘要（中文 + English）

> **使用其他語言？** 蘇格拉底模式（deep-research）和 Plan 模式（academic-paper）採用**意圖匹配**啟動 — 偵測你的請求含義，而非比對特定關鍵字。這代表它們**支援任何語言**，無需額外設定。
>
> 不過，一般的 `Trigger Keywords` 區塊（決定 skill 是否被啟動）仍以英文和繁體中文為主。如果你發現 skill 在你的語言下觸發不穩定，可以在各 `SKILL.md` 的 `### Trigger Keywords` 區塊中加入你的語言的關鍵字，提高匹配信心。

### 支援引用格式

- APA 7.0（預設，含中文引用規則）
- Chicago（Notes & Author-Date）
- MLA
- IEEE
- Vancouver

### 支援論文結構

- IMRaD（實證研究）
- 主題式文獻回顧
- 理論分析
- 個案研究
- 政策簡報
- 研討會論文

---

## Skill 詳細資訊

各 agent 的職責與各階段產出物現已移至 [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)。版本號保留在此以維持 release metadata 集中管理。

### Deep Research (v2.11.0)

13 個 Agent 的研究團隊。模式：full、quick、review、lit-review、three-way-scan、fact-check、socratic、systematic-review。完整 agent 名單與產出物：見 ARCHITECTURE.md §3。

### Academic Paper (v3.2.0)

12 個 Agent 的論文撰寫 pipeline。模式：full、plan、outline-only、revision、revision-coach、abstract-only、lit-review、format-convert、citation-check、disclosure、rebuttal-audit。輸出：MD + DOCX（Pandoc 可用時）+ LaTeX（APA 7.0 `apa7` class / IEEE / Chicago）→ tectonic 編譯 PDF。完整 agent 名單與各 phase 職責：見 ARCHITECTURE.md §3。

### Academic Paper Reviewer (v1.10.0)

7 個 Agent 的多視角審查，搭配 **0-100 品質量表**。模式：full、re-review、quick、methodology-focus、guided、calibration。**決策對照：** ≥80 接受、65-79 小修、50-64 大修、<50 退稿。第一輪審查團隊 vs. 精簡再審團隊的分界：見 ARCHITECTURE.md §3 Stage 3 / Stage 3'。

### Academic Pipeline (v3.16.0)

10 階段調度器，含誠信驗證、兩階段審查、蘇格拉底指導、協作品質評估。Pipeline 保證：每個階段都需使用者確認 checkpoint；誠信驗證（Stage 2.5 + 4.5）不可跳過；R&R 追溯矩陣（Schema 11）獨立驗證作者修訂宣稱。v3.4 新增 Compliance Agent（PRISMA-trAIce + RAISE）於 Stage 2.5 / 4.5。v3.5 新增 **協作深度觀察員**（`collaboration_depth_agent`，僅諮詢性質、永不阻擋流程）於每一次 FULL/SLIM checkpoint 與 pipeline 完成時。MANDATORY 誠信閘門（2.5 / 4.5）明確跳過觀察員，避免稀釋合規檢查。理論基礎：Wang & Zhang (2026), IJETHE 23:11。逐階段矩陣（agent、產出物、閘門）：見 ARCHITECTURE.md §3。

---

## v3.0 優化：我們發現了 AI 的哪些結構性限制

在使用 ARS 撰寫一篇關於 AI 與高教的反思文章時，我們遇到了三個結構性問題：

1. **框架鎖定**：AI 在給定框架內越來越精緻，但無法質疑框架本身
2. **諂媚傾向**：每次挑戰魔鬼代言人的攻擊，它都讓步得太快
3. **意圖偵測錯誤**：蘇格拉底模式在使用者仍在探索時就急著收束

### 改了什麼

- **魔鬼代言人讓步門檻**：反駁必須評分 1-5，≥4 才允許讓步。不允許連續讓步。框架鎖定偵測。
- **蘇格拉底意圖偵測**：偵測使用者是「探索型」還是「目標型」。探索型模式停用自動收束。
- **對話健康度指標**：每 5 輪靜默自檢，偵測持續同意、迴避衝突、過早收束。
- **跨模型驗證**：設定 `ARS_CROSS_MODEL` 啟用第二 AI 模型獨立審查。詳見 [docs/SETUP.zh-TW.md](docs/SETUP.zh-TW.md)。
- **AI 自我反思報告**：Pipeline 結束後自動產出 AI 行為自評。

這些優化不能完全解決 AI 的結構性限制——它們讓限制變得可見、可追蹤、可被人類介入。

---

## 授權條款

本作品採用 [CC-BY-NC 4.0](https://creativecommons.org/licenses/by-nc/4.0/) 授權。

**你可以自由：**
- 分享 — 複製及散布本作品
- 改作 — 重混、轉換、以本作品為基礎進行創作

**惟須遵守以下條件：**
- **姓名標示** — 你必須給予適當的標示
- **非商業性** — 你不得將本作品用於商業目的

**標示格式：**
```
Based on Academic Research Skills by Cheng-I Wu
https://github.com/Imbad0202/academic-research-skills
```

---

## 貢獻者

**吳政宜** (Cheng-I Wu) — 作者與維護者

**[aspi6246](https://github.com/aspi6246)** — 貢獻者。v3.1 優化靈感來自 [Claude-Code-Skills-for-Academics](https://github.com/aspi6246/Claude-Code-Skills-for-Academics)：唯讀約束模式、Anti-Pattern 作為一等公民設計、認知框架方法（教「如何思考」而非只有步驟）、精簡 skill 尺寸哲學。

**[mchesbro1](https://github.com/mchesbro1)** — 貢獻者。最初提出並撰寫了 IS Basket of 8 期刊清單（[Issue #5](https://github.com/Imbad0202/academic-research-skills/issues/5)）。

**[cloudenochcsis](https://github.com/cloudenochcsis)** — 貢獻者。將 IS 章節從 *Basket of 8* 擴充為完整的 *Senior Scholars' Basket of 11*，補上 *Decision Support Systems*、*Information & Management*、*Information and Organization*（[Issue #7](https://github.com/Imbad0202/academic-research-skills/issues/7)、[PR #8](https://github.com/Imbad0202/academic-research-skills/pull/8)）。資料來源：[AIS Senior Scholars' List of Premier Journals](https://aisnet.org/research/seniorscholarsbasket/)。

**[eltociear](https://github.com/eltociear)**（Ikko Eltociear Ashimine）— 貢獻者。翻譯了日文版 README（[`README.ja-JP.md`](README.ja-JP.md)）（[PR #161](https://github.com/Imbad0202/academic-research-skills/pull/161)）。

**[xpfo-go](https://github.com/xpfo-go)**（xpfo）— 貢獻者。翻譯了簡體中文版 README（[`README.zh-CN.md`](README.zh-CN.md)）（[PR #181](https://github.com/Imbad0202/academic-research-skills/pull/181)）。

---

## 更新紀錄

### v3.16.0（2026-07-12）— 模型分層、跨模型閘門強化、WP 提示語銳化

> **新增：**選用型模型分層（#517）— 新 `ARS_MODEL_TIERING` 開關含兩個方向（`economy` 讓 13 個執行型 agent 以低於 session 模型一階派工、下限 Opus 級；`quality-boost` 讓完整性閘門與最終審查面的判斷型 agent 升到前沿階）；未設定時逐位元組等同舊行為，凍結的 39-agent 分類由新 manifest + lint 釘死。跨模型閘門強化（#518）— 風險分層抽驗（HIGH-IMPACT 參考文獻在兩道閘門 100% 驗證）、兩個不可逆決策點（設計凍結 + 最終編輯決定）的盲測分歧檢查、驗證模型 id 狀態白名單、升格 bakeoff 協定；原規劃的通用第 6 位審查者確定除役、非延期。GPT-5.6 Sol 列為暫定跨模型驗證者並增設明確 reasoning-effort 控制（#515）。devCharlotte 提案的韓文觸發詞 + 路由邊界 fixture（#452/#509）。論文寫作端新增 CARS 導論修辭 + 標題設計參考檔（#500）。**變更：**WP 研究問題提示語經名詞替換測試泛化到 20 殼表之外（#501）並銳化豁免條款、抓到裝飾型標題殼（#505）— held-out 漏判率 0.34–0.38 → 0.094、誤觸 0/16 維持；審查者校準協定記載 LLM 評審偏寬方向（FARS 錨點，#484）；OpenAlex API key 認證 + 預算感知 429 處理 + arXiv ToU 對齊退避（#495/#496）。**文件：**THIRD_PARTY.md 社群目錄（#497/#498）。`academic-pipeline` 跟隨套件版本至 v3.16.0；其他三個 skill 版本不變。

### v3.15.0（2026-07-04）— 發版閘門強化、prompt 債務清理第二輪、防漂移鎖

> 以發版紀律與品質衛生為主的版本；skill 行為無變更。**新增：**三道 CI 閘門 — CHANGELOG-covers-merges tag 前閘門（#483）、版本一致性 invariant 9-11 加 tag 時重跑閘門（#487）、把 SessionStart announce 清單釘到實際 16 個指令清單的 command-invariants 閘門（#486）— 以及兩道防漂移鎖：Phase Boundary enforcement 句在全部 23 個 Bucket A agent 區塊逐字釘死、SETUP 跨模型範例與 canonical 型號表互相釘死（#491 → #492）。**變更：**prompt 債務清理第二輪深掃第一輪延後的 17 個 agent（#489 → #490）：修正兩個 socratic_mentor 的活矛盾（過期的 15 輪勸退規則 vs 文件明載的典型 20-30 輪）、修正全 repo 29 處過期的 enforcement 狀態句、修剪 7 個 agent 的 few-shot 與重複流程鷹架 — 經 4 批平行稽核 + 獨立 codex 跨模型挑戰驗證；稽核報告在 `audits/`。**修復：**DOI 徽章改由 shields.io 提供（#482）。`academic-pipeline` 跟隨套件版本至 v3.15.0；其他三個 skill 版本不變。

### v3.14.0（2026-07-02）— Claude Science 可匯入性、eval comment 呈現、prompt 債務清理

> 一個以可移植性與打磨為主的 release，skill 行為無變更。**新增：** Claude Science 可匯入性——marketplace manifest 明列 skill 路徑，讓無法穿越 symlink `skills/` 目錄的 GitHub-API 匯入器（Claude Science「Import from GitHub」、Windows checkout）能找到全部四個 skill；已在 Claude Science 端對端驗證，README + SETUP 新增匯入指南（#480）。eval-harness 的 PR comment 改為一行結論 + 逐任務表格、原始 JSON 摺疊進 `<details>`，取代裸貼整份報告——僅顯示層，gate 邏輯位元組不變（#479）。**變更：** 依 2026-07 harness-retirement 稽核，自四個寫作面 agent 移除過期的 writing-harness scaffold（#476/#477 → #478，淨 −111 行 prompt）；remind-don't-block 的 Platform Port Reminder 在 PR 新增頂層目錄時提示 platform-ports 政策（#473）。**文件：** devCharlotte 母語審校的韓文 README（#469/#471）；GitHub Copilot repository instructions（#465）；建議 auto permission mode 取代 Skip Permissions（#464）。累積於 `[Unreleased]` 的 16 條積壓條目（程式碼皆在 v3.13.0 tag 前已上——diff/patch revision mode #390、submission-package verifier #394、eval gold sets #215/#216 等）併入版本紀錄；詳見 `CHANGELOG.md`。`academic-pipeline` 隨 suite 至 v3.14.0；其餘三個 skill 版本不變。

### v3.13.0（2026-06-18）— Hook 可移植性、provider-agnostic 驗證、guard 正確性

> 一個 minor release，強化安裝／執行面並擴展跨模型範圍。**修正：** 寫入範圍 guard 在 git-clone + symlink 安裝佈局下不再誤擋使用者自己的 `CLAUDE.md`（#459，收掉 #448/#449 的殘餘一半——`CLAUDE.md` 是文件而非承載 enforcement 的檔案，故移出 infra 保護清單，所有承載檔案仍受保護）；Windows Python hook 可移植性 + 無 Python 時優雅降級，改由跨平台 `hooks/run_guard.sh` launcher 啟動，會拒絕 0-byte 的 Microsoft Store `python3` stub 且不再洗 hook log（#454）；`draft_writer` dual-phase static union 文件化 + Windows POSIX-safe 路徑匹配（#451）。**新增：** provider-agnostic 跨模型驗證，接受 OpenAI 相容端點（MiMo、DeepSeek、自架）與 grounded first-party OpenAI 並存，且後者絕不被靜默降級（#455）；opt-in 的 Socratic 鄰近 framing probe（借自 STORM 的視角擴展，`ARS_SOCRATIC_ADJACENT_PROBE=1`，預設 OFF，純 prose-layer——`deep-research` 2.10.0 → 2.11.0）（#461）。`academic-pipeline` 隨 suite 至 v3.13.0；`academic-paper` 與 `academic-paper-reviewer` 不變。逐 issue 細節見 `CHANGELOG.md`。

### v3.12.1（2026-06-15）— 審稿回覆分流模式（PR #433 整合）

> 一個 patch release，依 ARS 的模式化架構，把一份外部貢獻中真正具新意的部分收進既有 skill 成為模式。**新模式：** `deep-research` `three-way-scan` —— 介於 `quick` 與 `lit-review` 之間的輕量 WHY/HOW/WHAT 論文比較分流，產出逐論文短清單加跨論文統合（`deep-research` 2.9.4 → 2.10.0）；`academic-paper` `rebuttal-audit` —— 對作者既有的 rebuttal／回覆草稿，比對審稿意見做獨立的諮詢式 QA（逐條覆蓋表 + 缺口清單 + 語氣／證據／誤讀風險旗標），它不產生任何內容，且獨立呼叫時明確抑制 Schema 11／Material Passport 寫入／`ready_to_submit`（由帶 mutation 覆蓋的 `check_rebuttal_audit_guard()` lint 強制）；另含 `revision-coach` 範圍擴展到反駁／不同意姿態與非期刊情境，以及 `/ars-3w` + `/ars-rebuttal-audit` 斜線指令。依輸入形狀路由：審稿意見加草稿 → `rebuttal-audit`；僅意見 → `revision-coach`。整合自 [@Yaobin29](https://github.com/Yaobin29) 的 [PR #433](https://github.com/Imbad0202/academic-research-skills/pull/433)。Suite 模式數 25 → 27（仍 4 個 skill）。逐 issue 細節見 `CHANGELOG.md`。

### v3.12.0（2026-06-08）— Kong 自動研究功能線：實驗來源、圖表保真、跨論文矛盾、部分證據拆解

> 一個 minor release，落地 Kong et al.（2026，arXiv:2605.18661）自動研究功能線，以及部分證據陷阱的拆解工作，每項都已各自審查並 merge。**新功能：** 實驗來源登錄 + 宣稱對實驗對齊 —— 為實驗支撐的宣稱建立 schema-first 的證據帳本層，只做登錄與對齊（學者在外部跑實驗，ARS 從不執行）（#260）；圖表保真 gate，查驗 caption 的詮釋是否從資料推得、論文是否拿該圖表佐證它真正支撐的宣稱（#261）；結構化的跨論文矛盾盤點，把已評估的論文對列舉出來供學者確認（#262）；以及在引用判定（#213）與編輯統合（#214）兩層都先做子宣稱拆解再判定，於兩層收斂 §F.3.2 部分證據陷阱。**引導與詮釋層：** 對產報告的審稿人加上精簡輸出 + 抗壓邊界強化（#274）；同源／rubric-aware 校準的認識論註記（#273）；把檢索內容的指令／資料邊界訂為常設原則（#367）。**負面範圍：** Kong META（#255）收尾，在 `POSITIONING.md` 加「拒絕機制」段落列舉 ARS 不做的五種自主機制，外加兩份 Tier D 設計教訓文件。**發版紀律 lint：** version-consistency 不變量 5–7（#357）與 ARCHITECTURE 元件版號稽核（#345）。另含跨模型 grounding guard（#346 / #349 / #351）、引用 gate 快取鍵與 rationale 上界（#359 / #360 / #361）、eval 黃金集（#250）、ACL/EMNLP 揭露重新接地（#242）等正確性修正。新增的 schema、manifest 欄位與所有不變量皆為增量、向後相容。`academic-pipeline` 隨 suite 升至 v3.12.0；其餘三個 skill 版號不變。逐 issue 細節見 `CHANGELOG.md`。

### v3.11.1（2026-06-06）— 出貨後正確性、強化與來源修正彙整

> 一個 patch release，彙整 v3.11.0 出貨後浮現的修正，每項都已各自審查並 merge：把跨模型同意 gate 擴展到 integrity-verification + collaboration-depth 路徑（#322）、每筆 entry 的 OpenAlex + Crossref backfill 平行化（#138），以及橫跨引用存在性 gate、v3.10 政策層、eval harness、領域證據 profile、#310 安全邊界邊角案例的七項正確性/強化修正（#323 / #327 / #328 / #329 / #331 / #332 / #333）—— 其中兩項是 P1（#327 no-handoff 路徑上的領域 profile 啟動、#328 eval harness 的 per-class 門檻 gate）。無新功能、無破壞性 schema 變更。逐 issue 細節見 `CHANGELOG.md`。

### v3.11.0（2026-06-04）— 確定性引用查驗 gate（#182）

> 新增一道**確定性的引用存在性查驗 gate**，獨立於 LLM 同儕審查運作。每筆引用都會比對最多四個書目索引（Semantic Scholar、OpenAlex、Crossref，以及新增的 **arXiv resolver**，`scripts/arxiv_client.py`，不需 API key），把每筆引用的 `lookup_verified` 狀態（`{true, false, unresolvable}`）寫進統一彙整。捏造、帶著查不到的 DOI/arXiv ID 的引用，因此被 lookup 偵測標示出來（在使用者選用 strict 時才升級為終止），而非寄望審查 agent 注意到。這道 gate **沿用 v3.10 `terminal_policies` 的 opt-in 模型**：偵測一律執行，但 `lookup_verified == false` 的列只有在使用者選用 `terminal_policies.citation_existence == strict` 時才是終止性的；預設行為是 advisory、可用 `/ars-mark-read` 認可。`false` 的定義刻意**收窄到 ID-keyed unmatched**（一次以精確 DOI/arXiv 查驗、卻證實查不到），因此正當但未被索引的人文 / 非英語 / 區域期刊引用會落在 `unresolvable`、永不阻擋（這是文件中載明的「精確優先於召回」取捨）。本版另含持久化 SQLite 查驗 cache（`~/.cache/ars/verification.db`，90 天 TTL）搭配 `/ars-cache-invalidate` 指令、獨立的 `verification_gate` API 與 `verify_passport.py` CLI，以及把 v3.9.0 污染三角驗證矩陣擴成四索引（k=0..4，全屬 advisory）。`academic-pipeline` 追 suite 至 v3.11.0，其餘三個 skill 版號不變。規格：`docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md`（§0 amendment + C-V6）。

### v3.10.0（2026-06-01）— 三角驗證政策層、Kong 綜述採納、評測 harness、scoped-write guard

> Minor release，打包數項工作：可選用的污染三角驗證 **terminal 政策層**（#127，預設引用行為與 v3.9.0 byte-equivalent）；**Kong et al. 2026 綜述採納**，包含 Rebuttal Commitment Ledger（#256/#266/#268/#269）與依學門的 domain evidence profile（#259）；**v3.10 量測基建**，通用化評測 gold set 加 ranking-lift CI gate（#184）；**scoped-write guard MVP**（#134），一個 deterministic `PreToolUse` hook，把 23 個單一 phase 的 subagent 圍進各自的 phase 目錄、並禁用它們的 Bash（改用 Grep/Glob 與結構化編輯工具）；`/ars-mark-read` plugin 指令（#190）加一個 broken-on-arrival 修正（#195）；簡體中文 README（#185）；以及 CI 強化（#156/#155）。`academic-paper` 升至 v3.2.0、`academic-paper-reviewer` 升至 v1.10.0，反映 Commitment Ledger 與 domain profile 的新增功能；`academic-pipeline` 追 suite 至 v3.10.0。預設 skill 行為不變，除非使用者選用 strict 政策模式；唯一 default-on 的改動是 #134 guard，它約束的是被圍起來的 subagent，不是面向使用者的產出。

### v3.9.4.2（2026-05-19）— PR #149 CI 紀律 gate post-ship hotfix（codex post-ship）

> Codex post-ship review 對 PR #149（7 道 CI 紀律 gate）抓到 4 個 P2 finding；v3.9.4.2 修齊其中 3 個。F1：`harness-retirement-monthly.yml` 補 `GH_REPO`，讓排程跑能取到 repo context 給 `gh issue create`。F2：`release-cooldown.yml` 把 `PREV_TAG` 查詢 filter 到 `v*` tag，避免非 release tag（如舊 plugin tag）繞過 cooldown gate。F3：`release-cooldown.yml` 加讀 annotated tag subject + 接受 `hot-fix` 拼寫變體（v3.9.2 在舊偵測器下是 false-negative hotfix）。PR #157 follow-up：`[skip-cooldown]` override 改從 commit message 跟 annotated tag message 雙處讀取（self-bootstrapping fix — 本 tag 的 cooldown 繞過正好證明 F2+F3 端到端可用）。F4（test-count-monotonic 強化）被 revert，因為它 surface 了 `scripts/` package 預存問題，追蹤為 #154（已由 PR #158 修復）+ 再次嘗試 #155。Closes #152。Follow-ups：#155、#156。

### v3.9.4.1（2026-05-19）— v3.9.4 時序驗證 post-ship hotfix（#135 codex post-ship）

> Codex post-ship review 抓到 4 個 per-task subagent reviewer 漏掉的真 bug。Hotfix 一次修齊：(1) `audit()` 把 `citation_provenance` 接到 P2 + P4，遇到 ref slug 在 provenance.yaml 是 `confidence: low` 或 `conflict` 時，驗證器改發 `TEMPORAL-METADATA-MISSING` 而不是直接用 timeline 日期當算術 ground truth（spec §3.4 第一手 safety check 原本沒接線）。(2) `_date_to_interval` 補齊全部 schema-valid 日期形狀，包括 `YYYY-MM`（Crossref 月精度）和 `YYYY-MM-DD..YYYY-MM-DD`（interval），v3.9.4 對這兩種 silently `ValueError` 跳過。(3) P4 在 ref marker 缺席時可 bind 直接 prose 日期 — 「The 2026 policy enabled the 2020 rollout」這種句現在會 trigger。(4) `citation_provenance.schema.json` `confidence:high` allOf 加 `then.required`，補 absent-property bypass 漏洞。1561 passed（+12 新測試、0 regression）。ARCHITECTURE.md 同步補齊（先前停在 v3.8.0）。

### v3.9.4（2026-05-18）— #135 時序驗證層（advisory）

> Phase 4 → 5 邊界新增決定性 advisory verifier，涵蓋 5 種時序失效模式（P1 回顧算術、P2 時代錯置引用、P3 比較基準未實體化、P4 因果倒置、P5 現在式指示語）。新 Phase 2 sibling `timeline_extraction_agent` 擁有 `phase2_investigation/timeline.yaml` + `phase2_investigation/citation_provenance.yaml`。驗證腳本 `scripts/temporal_integrity_audit.py` 執行 5 道確定性 pass。M3 時序完整性鐵律加入 `report_compiler_agent` + `draft_writer_agent`。M6-minimal：Crossref `issued` + pdftotext cover 第一手驗證。M7-minimal：日期出處 + 比較基準實體化。M5-stub：僅使用者宣告的 `version_family_id`。`literature_corpus_entry`、`claim_audit_result`、`claim_intent_manifest` 零修改。`bibliography_agent` 未改動（F2 不變量）。3 個新 sidecar schema。覆蓋率估計：55-70% 基準 / 含 M7 minimal 65-75%。1549 passed（+44 新測試、0 regression）。

### v3.9.3（2026-05-18）— #128 housekeeping（client utility 抽出 + resolver dedup）

> 純 refactor + 一個 latent bug fix，從 v3.9.0 `/simplify` review backlog 結清。抽出 `scripts/_text_similarity.py`（3-way client dedup：normalize / similarity / threshold / retry 常數）+ `scripts/_passport_yaml.py`（2-way migration tool dedup：ruamel.yaml round-trip config）+ 私有 `_resolve_by_doi_then_title` helper（2-way resolver body dedup、§3.4 / §3.5 API surface 不變）。OpenAlex + Crossref 的 throttle 量測從 `time.time`（NTP 不安全）統一改用 `time.monotonic`，與 Semantic Scholar 對齊。5 個 module-level cross-import 都加 dual-path try/except（sibling-first、namespace-package fallback）保持 class identity；額外順手修了 2 個 latent-broken 的 `import scripts.X` 路徑。1505 passed（+23 新測試、0 regression）。#128 §4（OA + CR 平行化）carry-over 到 #138。

### v3.9.2（2026-05-18）— #133 phase boundary 熱修

> #133 收尾（hot-fix 層）。長期架構修正以 v3.10 active conductor 在 #134 追蹤。新增：CLAUDE.md routing 釐清閘（跨 phase 素材 → 以 a-d 選項釐清，不靜默 dispatch）、22 個 single-phase agent 加 prompt 硬 fence（`## Phase Boundary (v3.9.2)`）、16 個 multi-phase / phase-orthogonal / cross-phase-meta agent 刻意不加 fence（誠實 framing：純 prose placebo 會造成假性 enforce 錯覺）、advisory verifier `scripts/check_pipeline_integrity.py` 事後偵測 #133 pattern。Behavioral smoke test 含 cross-model spot-check（Opus 4.7 100% / Sonnet + GPT-5.5 ≥75%）。

### v3.9.1（2026-05-18）— #129 + #130 client hardening

> v3.9.0 hot-fix。包 OpenAlex / Crossref response-read 失敗為 `*Unavailable`（#129）；`check_claim_audit_consistency` 對非字串 `manifest_id` 加 guard（#130）。無 spec 變動。

### v3.9.0（2026-05-17）— #102 跨索引三角測量

> #102 收尾。v3.7.3 已完成單索引（Semantic Scholar）污染偵測；v3.9.0 延伸至三索引三角測量（S2 + OpenAlex + Crossref），定位為**純 advisory**。`contamination_signals` 新增兩個 optional boolean（`openalex_unmatched`、`crossref_unmatched`）；manual-entry not-rule 對稱延伸。Finalizer 加入 4-tier advisory matrix（k=0/1/2/3，計算範圍為現有 `*_unmatched` 欄位），v3.7.3 的 legacy `CONTAMINATED-UNMATCHED`（k=1/k_max=1、S2-only case）保留。Formatter pass-through allowlist 從 3 條延伸至 9 條；refusal rules 1-10 依 R-L3-2-E 不變。Policy layer（strict modes、hard-block tier、`venue_type` / `triangulation_policy`）依 spec §2.3 延至 v3.10。k=3 marker 為 `CONTAMINATED-TRIANGULATION-UNMATCHED`（描述可觀測現象，不推斷成因）。新增 3 條 firm rules：R-L3-2-C（k 計算範圍為現有欄位）、R-L3-2-D（不得 API 推斷分類）、R-L3-2-E（refusal list 不擴充；pass-through allowlist 須與 finalizer 同步延伸）。

**遷移：** v3.7.3 corpus — 跑 `python scripts/migrate_literature_corpus_to_v3_9_0.py PATH` 補齊兩個新欄位。pre-v3.7.3 corpus — **先**跑 `migrate_literature_corpus_to_v3_7_3.py`，再跑 v3.9.0 遷移工具（spec §3.7 daisy-chain；v3.9.0 工具只動已有 `contamination_signals.semantic_scholar_unmatched` 的 entries）。

### v3.8.2（2026-05-17）— #118 uncited audit_tool_failure 補面

> #118 收尾。`ARS_CLAIM_AUDIT=1` 的 uncited 約束判斷路徑原本碰到 `JudgeInvocationError` 會靜默替換成 `{"judgment": "NOT_VIOLATED"}`，把 HIGH-WARN 的 constraint check 在 transient judge 中斷時直接吞掉。v3.8.2 改走新的 `uncited_audit_failures[]` aggregate，MED-WARN advisory tier 對應 cited 路徑 INV-14 row，但用獨立 schema 因為 `claim_audit_result.ref_slug` 必填、uncited 路徑沒 ref 可綁。#118 issue body 四個 option 最後選了 option 2（新 aggregate）；option 4（re-raise 並 abort 整段 audit）因會嚴重折損 audit coverage（特別是 judge endpoint 不穩時）被否決。

- **新 `uncited_audit_failure.schema.json` aggregate**（spec §3.6）：每筆 uncited sentence × manifest pair 一個 entry，記錄 constraint judge raise `JudgeInvocationError` 的情況。Fault-class enum 與 cited 路徑 INV-14 相同（`judge_timeout` / `judge_api_error` / `judge_parse_error` / `cache_corruption` / `retrieval_api_error` / `retrieval_timeout` / `retrieval_network_error`）。`rule_version: D4-c-v1-uaf-v1`。
- **UAF-INV-1..UAF-INV-6 lint**（spec §6 rule 4d）：`finding_id` 唯一性、scoped_manifest_id 跨 aggregate integrity、(M, C) pair integrity（manifest_claim_id non-null 時）、per-(sentence, manifest) dedup、rationale fault_class 前綴、與 `constraint_violations[]` cross-aggregate exclusivity。
- **Finalizer §5 MED-WARN advisory row**：annotation `[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — <fault-class>]`，gate 通過（retry-next-pass 為補救手段）。Formatter REFUSE list 不變 — UAF 是 advisory。
- **Pipeline 整合**（`scripts/claim_audit_pipeline.py`）：line 1211-1224 的 swallow site 移除；`JudgeInvocationError` 改 emit UAF row + `continue` 到下個 (sentence, manifest) pair。`constraint_violations[]` 不會再被假 NOT_VIOLATED 污染。
- **Tests**：新增 18 筆（15 筆 schema/lint TSUAFUncitedAuditFailureInvariants + 3 筆 pipeline integration TP23UncitedJudgeOutageEmitsUAF）。Baseline 694 → 712 tests、0 regression。
- **Agent doc**（`academic-pipeline/agents/claim_ref_alignment_audit_agent.md`）：Output emission 表格新增第七列；Error handling 表格從 3 種 surface 擴成 4 種，新增 uncited 路徑 UAF 列。

### v3.8.0（2026-05-16）— L3 Claim-Faithfulness Locator + Audit（配對 milestone）

> v3.7.3 + v3.8 端到端關閉 L3（claim-faithfulness）缺口。v3.7.3 鋪 locator 基礎建設（每筆引用都帶三層 anchor，給未來的稽核抓得到原文位置）；v3.8 在這之上加一道稽核 pass，判斷引用來源是否真的支撐論文的 claim，違反者在 formatter terminal hard gate 直接攔下。本次 release 也合併了從 v3.7.0 後累積的 5 個 audit-trail-shipped feature PR（#104 / #105 / #108 / #111 / #115）。

- **#103 — `claim_ref_alignment_audit_agent`**（v3.8 PR #121）：opt-in（`ARS_CLAIM_AUDIT=1`，預設 OFF）的 Stage 4→5 audit agent。對每筆抽樣引用判斷與原文段落是否一致，emit `claim_audit_results[]` + `claim_intent_manifests[]` + `claim_drifts[]` + `uncited_assertions[]` + `constraint_violations[]` 五個 aggregate。Finalizer 8 列 matrix 把 HIGH-WARN 類別（CLAIM-NOT-SUPPORTED / NEGATIVE-CONSTRAINT-VIOLATION / FABRICATED-REFERENCE / ANCHORLESS / CONSTRAINT-VIOLATION-UNCITED）導去 formatter REFUSE rules 6-10。Calibration runner 隨 release 出 20 筆 gold set（T-C1 FNR<0.15 + FPR<0.10、T-C2 per-class、T-C3 shape integrity）。共 8 輪 dual-track review（R1 codex + Gemini 3.1-pro-preview、R2-R8 在 Gemini quota 用完後改 codex-only）；trajectory R1 4P1+2P2 → R8 0P1+4P2 ship gate。
- **v3.7.3 — Three-Layer Citation Emission + contamination signals**（PR #98）：`synthesis_agent` / `draft_writer_agent` / `report_compiler_agent` 加上 `## Three-Layer Citation Emission (v3.7.3)` H2。每個 `<!--ref:slug-->` 都帶 `<!--anchor:<kind>:<value>-->`，`<kind> ∈ {quote, page, section, paragraph, none}`（quote anchor 限 25 字以內、值需 URL-encode）。`pipeline_orchestrator_agent` finalizer 升 5 cell 並加 precedence-zero NO-LOCATOR 檢查。`formatter_agent` 在 hard gate 加上對 `[UNVERIFIED CITATION — NO QUOTE OR PAGE LOCATOR]` 的明確 refusal。`literature_corpus_entry.schema.json` 新增 optional 的 `contamination_signals: { preprint_post_llm_inflection, semantic_scholar_unmatched }` 物件，`bibliography_agent` 在 ingest 時計算兩個訊號。11 輪 review trajectory（Codex×10 + Gemini cross-model×1）收斂 22 個 finding。Spec：`docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md`。外部動機：Zhao 等人 arXiv:2605.07723（2026-05）。
- **#108 — AI disclosure policy-anchor renderer**（2026-05-14）：在原本的 venue-track renderer 之外，新增 PRISMA-trAIce / ICMJE / Nature / IEEE 四條 policy-anchor disclosure 路徑。
- **#111 — `slr_lineage` emission on systematic-review → academic-paper handoff**（2026-05-15）：Schema 9 新增 optional 的 boolean `slr_lineage` 欄位。Producer 是 `pipeline_orchestrator_agent`（每次 handoff transition 寫入），consumer 是 `disclosure` mode（讀到後按 §4.3 G2 invariant 路由到 `--policy-anchor=prisma-trAIce`）。
- **#104 — README motivation：Zhao 等人 corpus-scale 證據錨點**（2026-05-15）：README + `README.zh-TW.md` 動機段以 Zhao 等人 146,932 筆幻覺引用的發現作為 v3.7.x 線設計動機的證據錨點。
- **#105 — v3.7.3 contamination_signals 回填遷移工具**（2026-05-15）：`scripts/migrate_literature_corpus_to_v3_7_3.py` 對 v3.7.3 前的 passport 反向計算兩個 contamination signals 並補上。
- **#115 — Semantic Scholar client 成熟度**（2026-05-15）：`scripts/semantic_scholar_client.py` 加 1 req/s throttle（偵測到 `S2_API_KEY` 時降到 0.1s）、URLError 觸發的 outage latch、以及 `reset_outage_latch()` 給跨 passport 的長執行批次清算用。

### v3.7.0（2026-05-05）— Claude Code Plugin 打包

> Plugin 打包升級：ARS 現可在 Claude Code CLI / VS Code / JetBrains 一行裝（`/plugin marketplace add Imbad0202/academic-research-skills` + `/plugin install academic-research-skills`）。原本的 `git clone + symlink 到 ~/.claude/skills/` 安裝流程不變、繼續支援；雙軌都是一級公民。

- **Plugin manifest 與 marketplace metadata**（Phase 1，PR #68）：`.claude-plugin/plugin.json` 宣告整個 suite（4 個 skill 透過 `skills/` 目錄相對 symlink 自動探索）；`.claude-plugin/marketplace.json` 註冊 plugin，使單一 GitHub-hosted endpoint 同時提供 marketplace listing 與 plugin 來源。README、`README.zh-TW.md`、`docs/SETUP.md` 都加入雙軌安裝指引。
- **10 個 slash command** 在 `commands/ars-*.md`（Phase 2.1，PR #69）將 `MODE_REGISTRY.md` 的條目對映到 `/ars-<mode>` 觸發。每個 command frontmatter 釘住模型路由：`opus` 給 `full` 與 `revision-coach`（架構與審稿解讀深度），`sonnet` 給其他 8 個。任何情境不用 Haiku。
- **3 個 plugin-shipped agent** 在 `agents/*_agent.md`（Phase 2.1，PR #69）以相對 symlink 指向 `deep-research/agents/` 內 v3.6.7 已 hardened 的下游 agent：`synthesis_agent`、`research_architect_agent`、`report_compiler_agent`。底線檔名保留以對齊 `scripts/check_v3_6_7_pattern_protection.py` hard-pin 路徑與 INV-3 manifest-confined Clause 1 不變式。Symlink（不複製）維持 single source of truth，避免 v3.6.7 §6 inversion sweep + INV-1/2/3 lint 已關閉的 Pattern C3 攻擊面再開。（#413 起改為真實 byte-identical 複本：相對 symlink 在無 `core.symlinks` 的 Windows checkout 與 zip 下載安裝會壞；single-source 保證改由 `scripts/check_agents_mirror_sync.py` byte-equality CI lint 承接。）
- **`model: inherit`** 加在這三個 source agent frontmatter 上。選 inherit 而非 pin `sonnet` 是為了讓 Opus session 跑 ARS full pipeline 時 agent 仍是 Opus（不被降）。使用者的 `~/.claude/hooks/warn-agent-no-model.sh` PreToolUse hook 在派工邊界已 gate Haiku，所以 inherit 解析到的是已經沒 Haiku 的模型。
- **SessionStart announce hook** 在 `hooks/hooks.json` + `scripts/announce-ars-loaded.sh`（Phase 2.2，PR #70）。Plugin 載入時，hook 把 10 個 slash command、3 個 plugin agent、token 預算指引以 `additionalContext` 注入 LLM 第一輪。`startup` 與 `clear` 拿完整 announce；`resume` 與 `compact` 只拿一行確認，避免每次 resume 都燒 context。Bash 3.2 兼容 — macOS stock `/bin/bash` 直接跑，不需 `brew install bash`。
- **Phase 2.2 範圍縮減**：原本規劃的 `SubagentStop → run_codex_audit.sh` codex audit hook 在 v3.7.0 被排除，因為 (a) contract gap：SubagentStop payload 沒帶 stage / deliverable，wrapper 必要參數無法從 hook 推出；(b) invoker 邊界：`run_codex_audit.sh` lines 4–7 明禁同 session in-LLM 呼叫，PostToolUse 在產出 deliverable 的 LLM session 內觸發。真正的 audit-hook 整合留到後續版本，等 ARS 有 stage / deliverable propagation contract 再做。詳見 `docs/design/2026-04-30-ars-v3.7.0-plugin-packaging-roadmap.md` Update note 2026-05-05（Phase 2.2 scope reduction）。
- **`docs/PERFORMANCE.md` + `.zh-TW.md`** 新增「v3.7.0 Plugin agent 與模型路由」節，說明 inherit 語意與目前 3-agent scope 邊界。
- **跨三個 PR 的 codex review chain**：8 輪 inline iterative review + 3 輪 fresh PR-level review，全部在 merge 前收斂到 0 個 P0/P1/P2 finding。Phase 2.2 fresh PR review 抓到一個 P2（`${CLAUDE_PLUGIN_ROOT}` 沒 quote，含空白的安裝路徑會 break）— inline 輪次抓不到，證實「實作 review（inline）」與「contract review（fresh）」分離的價值。
- **沒動的東西**：4 個 skill 目錄、25 個 mode、agent prompt、schema 檔案、lint contract 全不變。Plugin 打包只**新增**頂層介面（`commands/`、`agents/`、`hooks/`、`.claude-plugin/`、`skills/` symlink dir、3 個 source agent frontmatter 加 `model: inherit`）。既有 4.3k clone 安裝用戶完全不破。

### v3.6.8（2026-05-03）— Generator-Evaluator Contract Gate（v3.6.6 spec ship）

> 命名說明：本次發行交付 **v3.6.6 generator-evaluator contract** spec 與實作。
> v3.6.6 因專案排序晚於 v3.6.7 才落地；design doc 內仍保留 v3.6.6 內部命名作為
> contract gate 版本，suite release 標 v3.6.8 維持 CHANGELOG 單調遞增。

- **Schema 13.1**（`shared/sprint_contract.schema.json`）在 Schema 13 之上加兩個 `mode` enum 值（`writer_full` + `evaluator_full`）、兩個新 optional top-level 欄位（`pre_commitment_artifacts` writer-only、`disagreement_handling` evaluator-only）、12 條 `allOf` branch 強制 reviewer- / writer- / evaluator-conditional gate。既有 reviewer contract 在 Schema 13.1 下 byte-equivalent validate（§3.6 zero-touch promise）。
- **兩個新 shipped contract template**：`shared/contracts/writer/full.json`（D1–D7、F1/F4/F2/F3/F0）+ `shared/contracts/evaluator/full.json`（D1–D5、F1/F2/F3/F6/F4/F5/F0）。Spec branch 上原是 design-time artefact，本次發行 atomically promote 為 live shipped。
- **`academic-paper full` 模式內加入 two-phase orchestration**：Phase 4 拆成 Phase 4a（writer paper-blind 預先承諾）+ Phase 4b（writer paper-visible 撰稿 + 自評）；Phase 6 拆成 Phase 6a（evaluator paper-blind 預先承諾）+ Phase 6b（evaluator paper-visible 評分 + 決策）。phase-numbered `<phase4a_output>` / `<phase6a_output>` data delimiter 沿用 v3.6.2 reviewer pattern。Lint count summary：writer 3+4 / evaluator 5+5 / reviewer 5+6（reviewer 維持 zero-touch）。
- **`academic-paper` SKILL + agent file 新增 `## v3.6.6 Generator-Evaluator Contract Protocol` 區塊**（SKILL.md 101 行 + `draft_writer_agent.md` 47 行 + `peer_reviewer_agent.md` 57 行）。SKILL.md 另加 `## Known limitations` 區塊承載 graceful-degradation + cross-session resume v3.6.7+ forward note。
- **Validator 擴充**：`scripts/check_sprint_contract.py` 做 SC-* mode-gating audit（SC-5 + SC-11 reviewer-only；SC-9 跨三個 mode family 各讀對應欄位）。validator 單元測試從 54 條增加到 71 條（4 positive + 5 schema-branch negative + 2 §3.6 reviewer regression + 6 mode-gating）。
- **Manifest CI lint**：`scripts/check_v3_6_6_ab_manifest.py` 強制 `tests/fixtures/v3.6.6-ab/manifest.yaml` 的 §6.2 manifest schema + §6.5 git-tracked invariant。`.github/workflows/spec-consistency.yml` 把 sprint contract validation loop 擴成同時跑 reviewer + writer + evaluator 三個 template directory，並加入新的 manifest CI lint 步驟。
- **A/B evidence fixture stub**（`tests/fixtures/v3.6.6-ab/`，30 個檔案）：manifest + README + 6 paper-A inputs/baseline + 1 paper-C inputs/baseline + Stage 3 reviewer excerpt + 6 codex-judge baseline placeholder。真實 fixture data 在後續 commit populate。

### v3.6.7（2026-04-30）— 下游 agent pattern protection（Step 1+2）

- **三個下游 agent 收緊 13 / 18 個已知幻覺與漂移 pattern**：`synthesis_agent`（A1–A5 敘事側）、`research_architect_agent` survey-designer 模式（B1–B5 工具側）、`report_compiler_agent` abstract-only 模式（C1–C3 出版側）。三個 agent prompt 各自加上 `PATTERN PROTECTION (v3.6.7)` 區塊。
- **`shared/references/` 增加四份 reference 文件**：`irb_terminology_glossary.md`、`psychometric_terminology_glossary.md`、`protected_hedging_phrases.md`、`word_count_conventions.md`。protection 條款引用這些檔案路徑做為 operational contract。
- **跨模型 audit prompt 模板** 在 `shared/templates/codex_audit_multifile_template.md`，含七個 audit dimension 與 `report_compiler_agent` bundle 必跑的三段式 Section 4(f) 檢查。任一 sub-check 失敗即 P1 finding。
- **靜態 lint + 29 條 mutation 測試**：`scripts/check_v3_6_7_pattern_protection.py` 強制 protection 條款存在性與 obligation phrase 形狀；`scripts/test_check_v3_6_7_pattern_protection.py` 把 codex review 的 mutation 證據封存為 unit test，未來 lint 退化會在 CI 浮上來。兩者都接進 `.github/workflows/spec-consistency.yml`。
- **Codex review 紀錄**：七輪 `gpt-5.5` + `xhigh` 跨模型 review 收斂到 0 P1+P2 finding 才 SHIP。Step 6（orchestrator runtime hook）與 Step 8（合成 eval case）走 follow-up PR。

### v3.6.5（2026-04-27）— Material Passport `literature_corpus[]` Consumer 整合

- **Phase 1 兩個文獻 consumer** 接上：`deep-research/agents/bibliography_agent.md` 與 `academic-paper/agents/literature_strategist_agent.md`。當 passport 帶有非空 `literature_corpus[]` 時，兩者都走相同的五步 **corpus-first、search-fills-gap** 流程，並遵守相同的四條 Iron Rule（Same criteria / No silent skip / No corpus mutation / Graceful fallback on parse failure）。
- **PRE-SCREENED 可重現區塊** 進 Search Strategy 報告：列出已納入／排除／略過的 corpus entry，附 F3 zero-hit 註解與 F4a–F4f provenance 報告（針對 `obtained_via` / `obtained_at` 部分宣告情境）。`final_included = pre_screened_included[] ∪ external_included[]` 維持 neutral — bibliography entry 與 literature matrix row 不掛 provenance 標籤。
- **Consumer 協定參考文件** 在 `academic-pipeline/references/literature_corpus_consumers.md`，包含 PRE-SCREENED 模板、BAD/GOOD 範例、四條 Iron Rule 與 per-consumer 讀取指示。
- **CI lint** `scripts/check_corpus_consumer_protocol.py` 透過 manifest 驅動的 consumer 清單（`scripts/corpus_consumer_manifest.json`）強制九條協定不變式。
- **Schema 9 caveat 退役**：`shared/handoff_schemas.md` 移除 v3.6.4「Consumer-side integration deferred to v3.6.5+」一行，改成指向 consumer 協定的 backpointer。
- 採 presence-based 啟動，不變更 schema、不引入新 env flag。Parse 失敗 fallback 到 external-DB-only flow，並 surface `[CORPUS PARSE FAILURE]`。`citation_compliance_agent` 的 corpus 整合延後（目標版本將於 v3.8 後再訂）。
- 無破壞性變更，既有使用者 adapter 不需修改。

### v3.6.4（2026-04-25）— Material Passport `literature_corpus[]` 輸入埠

- **Schema 9 新增 `literature_corpus[]`** 選填欄位作為使用者文獻的輸入埠。每筆 entry 符合 `shared/contracts/passport/literature_corpus_entry.schema.json`（CSL-JSON authors / year / title / source_pointer，加上 PRIVATE 選填的 `abstract` / `user_notes`）。
- **語言中性的 adapter 契約** 放在 `academic-pipeline/references/adapters/overview.md`：任何語言寫的程式都能讀使用者自己的 corpus source 並產出符合契約的 `passport.yaml` + `rejection_log.yaml`。Entry-level 錯誤 fail-soft、adapter-level 錯誤 fail-loud、輸出順序確定。
- **三個 reference Python adapter** 在 `scripts/adapters/`：`folder_scan.py`（檔案系統的 PDF 資料夾）、`zotero.py`（Better BibTeX JSON export）、`obsidian.py`（vault frontmatter）。僅供起點參考；非 reference source 預期使用者自行實作 adapter。
- **Rejection log 契約** 在 `shared/contracts/passport/rejection_log.schema.json`，採用封閉 enum 的 categorical reason 值；永遠輸出（無 rejection 時為空）。
- **CI 把關**：`scripts/check_literature_corpus_schema.py` 驗 schemas + adapter examples；`scripts/sync_adapter_docs.py --check` 防 schema→docs drift；新 `pytest.yml` workflow 在 path-filtered 觸發跑 `scripts/adapters/tests/`。
- **僅輸入埠**：v3.6.4 只定義 schema 與 adapter 契約，consumer 整合到 v3.6.5 才接上 `bibliography_agent` 與 `literature_strategist_agent`。
- 無破壞性變更。

### v3.6.3（2026-04-23）— 選用式 Passport 重置邊界

- **Opt-in passport 重置邊界**（`ARS_PASSPORT_RESET=1`）。把每個 FULL checkpoint 提升為 context 重置邊界。新增 `resume_from_passport=<hash>` 模式，讓使用者在新的 Claude Code session 單憑 Material Passport ledger 就恢復 pipeline，不重播先前對話。`systematic-review` 模式 flag ON 時，每個 FULL checkpoint 一律強制重置；其他模式視重置為 flag 開啟後的強預設。Flag OFF 時 byte-for-byte 維持 pre-v3.6.3 行為。
- Schema 9 新增 append-only `reset_boundary[]` ledger，兩種 entry kind（`kind: boundary` + `kind: resume`）。Hash 用 JSON Canonical Form + SHA-256，搭配 canonical placeholder 處理自我參照問題。選填 `pending_decision` 負責 MANDATORY 分支決策。
- 新 CI lint `scripts/check_passport_reset_contract.py`：任何提到 flag 的檔案都必須指向權威協議文件。
- 協議文件：`academic-pipeline/references/passport_as_reset_boundary.md`。
- `docs/PERFORMANCE.zh-TW.md` 更新 long-running session 指引。
- 無破壞性變更，flag 預設關閉。

### v3.6.2（2026-04-23）— 審稿 Sprint Contract Hard Gate

v3.6.2 引入 Schema 13 sprint contract 與 hard-gate 編排，強制審稿人在閱讀論文前先承諾評分準則。本次只動審稿端（reviewer-only first test case）；writer/evaluator 留到 v3.6.4。詳見 CHANGELOG。

- **Schema 13 sprint contract**：`panel_size`、`acceptance_dimensions`、`failure_conditions`（含 `severity` 優先序 + 隨 panel 變動的 `cross_reviewer_quantifier`）、`measurement_procedure`、選用 `override_ladder`、限定 `agent_amendments`。驗證器：`scripts/check_sprint_contract.py`。
- **兩段 hard gate**：審稿人先在「論文內容盲」Phase 1 預先承諾評分計畫，Phase 2 才看到論文；Phase 1 輸出包在 `<phase1_output>...</phase1_output>` 資料分隔符內，縮窄 self-injection 面。
- **合成者三步機械協議**：建構跨審稿矩陣 → 依 panel-relative quantifier + 認可表達式詞彙評估每條 `failure_condition` → 用 `severity` 決優先。禁止操作清單寫在 `editorial_synthesizer_agent`。
- **出貨兩份審稿模板**：`shared/contracts/reviewer/full.json`（panel 5）與 `shared/contracts/reviewer/methodology_focus.json`（panel 2）。`reviewer_re_review`、`reviewer_calibration`、`reviewer_guided` 三個 mode 在 schema enum 中保留，但 v3.6.2 不出 template，繼續沿用 pre-v3.6.2 行為；`reviewer_quick` 完全排除於 enum 外。
- `academic-paper-reviewer` SKILL 版本：`1.8.1 → 1.9.0`。`academic-pipeline` SKILL 版本：`3.5.1 → 3.6.2`（suite-version invariant）。Suite 版本升至 `3.6.2`。
- 詳見設計稿 [`docs/design/2026-04-23-ars-v3.6.2-sprint-contract-design.md`](docs/design/2026-04-23-ars-v3.6.2-sprint-contract-design.md) 與協定 [`academic-paper-reviewer/references/sprint_contract_protocol.md`](academic-paper-reviewer/references/sprint_contract_protocol.md)。

### v3.5.1（2026-04-22）— 選用式 Socratic 誠實探測

v3.5.1 新增 Socratic Mentor 的選用式誠實探測（設定 `ARS_SOCRATIC_READING_PROBE=1` 啟用）。預設關閉。詳見 CHANGELOG。

- **選用式閱讀誠實探測**：設定 `ARS_SOCRATIC_READING_PROBE=1` 後，Socratic Mentor 在目標導向 session 中引用特定論文時，觸發一次性誠實探測，請使用者摘述一段文字。拒絕回答僅記錄，不扣分。探測結果寫入研究計畫摘要，並帶入 Stage 6 AI 自我反思報告。不新增 agent，不變更 schema。
- `deep-research` SKILL 版本：`2.9.0 → 2.9.1`。`academic-pipeline` SKILL 版本：`3.5.0 → 3.5.1`。Suite 版本升至 `3.5.1`。

### v3.5.0（2026-04-21）— 協作深度觀察員（Collaboration Depth Observer）

- **新增 agent**：`academic-pipeline` 新增 `collaboration_depth_agent`（Agent Team 從 3 成長為 4）。每個 FULL/SLIM checkpoint 與 pipeline 完成後（Stage 6 之後）觸發，依 4 維度 rubric 對使用者與 AI 的協作模式評分。**純觀察建議，永不阻擋流程**。MANDATORY checkpoints（Stages 2.5 / 4.5 的完整性檢查）**不**觸發 observer，完整性閘門完全保留。
- **新增 rubric**：[`shared/collaboration_depth_rubric.md`](shared/collaboration_depth_rubric.md) v1.0。四個維度：Delegation Intensity、Cognitive Vigilance、Cognitive Reallocation、Zone Classification（Zone 1 / Zone 2 / Zone 3）。理論依據為 Wang, S., & Zhang, H. (2026). "Pedagogical partnerships with generative AI in higher education: how dual cognitive pathways paradoxically enable transformative learning." *International Journal of Educational Technology in Higher Education*, 23:11. DOI [10.1186/s41239-026-00585-x](https://doi.org/10.1186/s41239-026-00585-x)。
- **Cross-model 分歧顯式標示，不默默平均**：當 `ARS_CROSS_MODEL` 設定時，observer 於兩個模型同時執行；若任一維度分差 > 2 分即標記為 `cross_model_divergence`。另提供 `ARS_CROSS_MODEL_SAMPLE_INTERVAL` 調控成本。
- **Short-stage guard**：stage 內使用者 turn < 5 時注入靜態 `insufficient_evidence` 區塊，不派發全模型 observer call。
- **反諂媚規範**：分數 ≥ 7 必須附具體對話 turn 引用；Zone 3 觸發 re-audit；禁止鼓勵性語言。
- `academic-pipeline` SKILL 版本：`3.3.0 → 3.4.0`。Suite 版本升至 `3.5.0`。新增 lint `scripts/check_collaboration_depth_rubric.py` 加 10 個測試。

### v3.4.0（2026-04-20）— Compliance Agent + Schema 12

- **Compliance Agent（shared）**：單一 mode-aware agent，同時跑 PRISMA-trAIce 17 項（限 SR mode）+ RAISE 四原則 + 8-role matrix。掛載既有 Stage 2.5 / 4.5 Integrity Gate；tier-based block（Mandatory → block、HR → warn、R/O → info）。非 SR 入口只跑原則、warn-only。
- **Schema 12 compliance_report** 附加到 Material Passport 的 `compliance_history[]`（append-only）。
- **三回合 user-override 階梯**，自動注入 `disclosure_addendum` 到 manuscript。無法規避揭露。
- **Calibration 以透明公布取代硬門檻**，與 `task_type: open-ended` 自洽。
- **Upstream freshness CI** 偵測 PRISMA-trAIce 上游漂移（non-blocking）。
- **長時間 session 文件**：Material Passport 作為跨 session 續跑機制。

### v3.3.6 (2026-04-15) — README 精簡 + ARCHITECTURE 文件

- 新增 `docs/ARCHITECTURE.md` 作為 pipeline 結構的單一來源（流程、矩陣、資料存取、依賴圖、品質閘門、模式）。透過 PR #18 合併入 main。
- 新增 `docs/SETUP.md` / `docs/SETUP.zh-TW.md`（前置需求、API key、Pandoc/tectonic、跨模型驗證、四種安裝方式），以及 `docs/PERFORMANCE.md` / `docs/PERFORMANCE.zh-TW.md`（token 預算、建議 Claude Code 設定）。README 以連結取代內嵌。
- 精簡 README：移除 ASCII pipeline 圖與 16 項 key-feature 清單（已被 ARCHITECTURE.md 取代）；Skill 詳細資訊維持版本號錨點，讀者跳到 ARCHITECTURE.md §3 看各 agent 名單。
- 註記：沒有任何 skill 的功能變動，純文件重構。suite version 升級至 `3.3.6`。

### v3.3.5 (2026-04-15)
- 新增 `benchmark_report.schema.json` 與 Material Passport 的 `repro_lock` 可選區塊。兩者都附 pattern 文件、lint、範例。首次引入正式的 Python 開發依賴清單（`requirements-dev.txt`）。

### v3.3.4 (2026-04-15) — README 更新紀錄同步修補

- 同步 `README.md` 與 `README.zh-TW.md` 內嵌的 changelog 區塊，補上原本缺漏的 `v3.3.3` 與 `v3.3.2` 發版摘要。
- 擴充 `scripts/check_spec_consistency.py`，之後 README changelog 若再漂移，CI 會直接 fail。
### v3.3.3 (2026-04-15) — Release Prep + Lint 強化

- 強化 SKILL frontmatter lint：缺少 closing `---` fence 時，現在會明確報錯，不再把整份檔案後半段誤當成合法 YAML。
- frontmatter 若可被 YAML 解析但不是 mapping，現在會回報可讀錯誤，而不是直接 crash。
- 修正中英文 README 中 post-publication audit showcase 連結失效的問題。
- 在 spec consistency check 補上 README 相對連結驗證，之後 dead link 會直接讓 CI fail。
- 將 DOCX 輸出契約在文件中統一：直接產出 `.docx` 依賴 Pandoc，否則回退為 Markdown + 轉換說明。
- 完成 `v3.3.3` 發版準備：suite version bump，`academic-paper` -> v3.0.2，`academic-pipeline` -> v3.2.2。

### v3.3.2 (2026-04-15) — Data Access Level + Task Type Metadata

- 所有頂層 `SKILL.md` 新增 `metadata.data_access_level`，並以 `raw`、`redacted`、`verified_only` 為強制詞彙。
- 所有頂層 `SKILL.md` 新增 `metadata.task_type`，並以 `open-ended`、`outcome-gradable` 為強制詞彙。
- 為兩個 metadata 欄位新增 lint script 與單元測試，並接到 GitHub Actions spec consistency workflow。
- 新增 `shared/ground_truth_isolation_pattern.md`，並在 `shared/handoff_schemas.md` 中補上對新詞彙的說明入口。

### v3.3.1 (2026-04-14) — 規格一致性修補

- 同步 README、`.claude/CLAUDE.md`、`MODE_REGISTRY.md` 與各 `SKILL.md` 的 mode 數量與公開版本標示。
- 修正跨模型敘述：目前已實作的是誠信抽樣查核與獨立 DA critique；同儕審查第六位 reviewer 仍在規劃中。
- 釐清 adaptive checkpoint 語意：SLIM checkpoint 仍然必須等待使用者明確確認。
- 再次明確化 Stage 2.5 與 Stage 4.5 誠信關卡不可跳過。
- 新增輕量 spec consistency 檢查與 GitHub Actions workflow，避免後續再發生文件漂移。

### v3.3 (2026-04-09) — PaperOrchestra 啟發的強化

整合 [PaperOrchestra](https://arxiv.org/abs/2604.05018)（Song, Song, Pfister & Yoon, 2026, Google）的技術。

- **Semantic Scholar API 驗證** — Tier 0 程式化引用存在性查核。Levenshtein >= 0.70 標題比對、DOI 不符偵測、S2 ID 去重。API 不可用時優雅降級。
- **反洩漏協議** — 知識隔離指令優先使用 session 內材料，缺少的內容標記 `[MATERIAL GAP]` 而非用 LLM 記憶填補。降低 Mode 5/6 失敗風險。
- **VLM 圖表驗證**（可選）— 用視覺模型閉環檢查生成圖表。10 項檢核清單，最多 2 輪修正。
- **分數軌跡協議** — 跨修訂輪次的逐維度評分差異追蹤（7 個維度）。偵測退步（delta < -3）觸發強制 checkpoint。
- **Stage 2 並行化** — 視覺化與論證建構可在大綱完成後並行執行。
- 新版本：deep-research v2.8、academic-paper v3.0、academic-pipeline v3.2

### v3.2 (2026-04-09) — Lu 2026 Nature 整合

整合 Lu 等人（2026，*Nature* 651:914-919）的研究洞見——第一個通過盲審的端到端全自動 AI 研究系統。

- **7 類 AI 研究失敗模式檢查清單** — 在 Stage 2.5/4.5 阻斷管線：偵測實作錯誤、幻覺實驗結果、取巧特徵依賴、錯誤包裝為發現、方法偽造、框架鎖定。擴充現有 5 類引用幻覺分類。
- **Reviewer 校準模式**（academic-paper-reviewer v1.8）— opt-in 的 FNR/FPR/balanced accuracy 測量，使用者提供 gold set。5 次集成、跨模型預設開啟、session 內強制附加信心揭露。
- **揭露模式**（academic-paper v2.9）— 針對特定期刊/會議的 AI 使用聲明生成器。v1 涵蓋 ICLR、NeurIPS、Nature、Science、ACL、EMNLP。
- **提前停止機制**（academic-pipeline v3.1）— 收斂檢查 + pipeline 開始時的 token 預算透明化。
- **忠實度-原創性模式光譜** — 按 Lu 2026 Fig 1c 分類所有 3 個 skill 的模式。
- 新版本：academic-paper v2.9、academic-paper-reviewer v1.8、academic-pipeline v3.1

### v3.1.1 (2026-04-09) — 資訊系統 Senior Scholars' Basket of 11

外部貢獻：[@mchesbro1](https://github.com/mchesbro1) 最初提出並撰寫了 IS Basket of 8 期刊清單（[Issue #5](https://github.com/Imbad0202/academic-research-skills/issues/5)）；[@cloudenochcsis](https://github.com/cloudenochcsis) 將其擴充為完整的 Senior Scholars' Basket of 11（[Issue #7](https://github.com/Imbad0202/academic-research-skills/issues/7)、[PR #8](https://github.com/Imbad0202/academic-research-skills/pull/8)）。更新 `academic-paper-reviewer/references/top_journals_by_field.md` 第 7 節，補上 *Decision Support Systems*、*Information & Management*、*Information and Organization*。資料來源：[AIS Senior Scholars' List of Premier Journals](https://aisnet.org/research/seniorscholarsbasket/)。

### v3.1 (2026-04-06) — 抗 Context Rot + 認知框架 + 精簡尺寸

靈感來自 [aspi6246/Claude-Code-Skills-for-Academics](https://github.com/aspi6246/Claude-Code-Skills-for-Academics)。

**Wave 1：抗 Context Rot 錨定**
- 4 個 skill 共 29 條 Anti-Patterns（每個 7-8 條，表格含「為何失敗」+「正確行為」）
- 22 個 IRON RULE 標記，確保長對話中關鍵規則不被遺忘
- 審查者唯讀約束（reviewer 不可修改論文原稿）

**Wave 2：追溯性 + 認知框架 + 中途強化**
- R&R 追溯矩陣（Schema 11）：Re-Review 新增「作者聲稱」+「已驗證？」欄位，獨立核實修訂宣稱
- 3 個認知框架 reference 檔案，教 agent「如何思考」而非只是「做什麼」：
  - 論證與推理框架（Toulmin 模型、Bradford Hill 因果推理、最佳解釋推論、認知狀態分類）
  - 審查品質思維框架（三鏡頭法、常見審查陷阱、校準問題）
  - 寫作判斷力框架（清晰度測試、讀者旅程、學科語態、修訂決策矩陣）
- 中途強化機制：每次 stage 轉換注入對應 IRON RULE + Anti-Pattern 提醒
- FULL checkpoint 前的 5 題自我檢查（引用完整性、諂媚讓步、品質軌跡、範圍紀律、完整性）

**Wave 3：精簡 Skill 尺寸**
- SKILL.md 總大小從 142KB 降至 85KB（-40%），詳細協議移至 `references/` 按需載入
- 新增 ~15 個 reference 檔案（re-review protocol、guided mode、systematic review、process summary 等）
- 所有 IRON RULE 保留在 SKILL.md；詳細內容按需載入
- 新版本：deep-research v2.7、academic-paper v2.8、academic-paper-reviewer v1.7、academic-pipeline v3.0

### v3.0 (2026-04-03) — 反諂媚 + 意圖偵測 + 跨模型驗證 + AI 自我反思
- **魔鬼代言人讓步門檻**（deep-research + academic-paper-reviewer）：反駁必須評分 1-5。≥4 才允許讓步。不允許連續讓步。讓步率追蹤。框架鎖定偵測。
- **攻擊強度保持**（academic-paper-reviewer）：DA 不因被反駁而軟化。反駁評估協議含偏移偵測。
- **意圖偵測層**（deep-research socratic）：偵測探索型 vs. 目標型。探索模式停用自動收束，最大輪數提升至 60。每 5 輪重新評估。
- **對話健康度指標**（deep-research socratic）：每 5 輪靜默自檢，偵測持續同意、迴避衝突、過早收束。偵測到模式時自動注入挑戰性問題。
- **跨模型驗證協議**（shared，可選）：用 GPT-5.4 Pro 或 Gemini 3.1 Pro 做誠信驗證 30% 抽樣跨模型檢查與獨立 DA critique。同儕審查第六位 reviewer 仍在規劃中，尚未實作。設定 `ARS_CROSS_MODEL` 環境變數啟用——未設定時零開銷。完整設定指南見 `shared/cross_model_verification.md`。
- **AI 自我反思報告**（academic-pipeline Stage 6）：Pipeline 結束後 AI 行為自評——DA 讓步率、健康警報、諂媚風險評級（LOW/MEDIUM/HIGH）、框架鎖定事件。
- 來源：四輪辯證實驗中發現 DA 讓步太快、蘇格拉底模式過早收束、整個辯論鎖定在人類設定的框架中。
- 版本：deep-research v2.5、academic-paper-reviewer v1.5、academic-pipeline v2.8

### v2.9.1 (2026-04-03) — Skill Metadata
- 為 4 個 SKILL.md 加入 `status: active` 和 `related_skills` 交叉引用
- 支援 skill 探索工具及跨技能導航

### v2.9 (2026-03-27) — 風格校準 + 寫作品質檢查
- **風格校準**（academic-paper intake Step 10，可選）：提供 3+ 篇過去論文，pipeline 會學習你的寫作風格 — 句子節奏、詞彙偏好、引用整合方式。寫作時作為軟性指引；學科規範永遠優先。優先級系統：學科規範（硬性）> 期刊慣例（強）> 個人風格（軟性）。見 `shared/style_calibration_protocol.md`
- **寫作品質檢查**（`academic-paper/references/writing_quality_check.md`）：寫作品質 checklist，於初稿自我審查時套用。5 大類：AI 高頻詞彙警告（25 個詞）、標點模式控制（em dash ≤3）、開頭廢話偵測、結構模式警告（三項列舉強迫症、均勻段落、同義詞循環）、句子長度變化檢查。這是好寫作規則 — 不是逃避偵測
- **Style Profile** 透過 academic-pipeline Material Passport 攜帶（`shared/handoff_schemas.md` Schema 10）
- **deep-research** report compiler 也可選地消費這兩個功能
- 版本：academic-paper v2.5、deep-research v2.4、academic-pipeline v2.7

### v2.8 (2026-03-22) — SCR Loop Phase 1：State-Challenge-Reflect 反思機制
- **Socratic Mentor Agent**（deep-research + academic-paper）：整合 SCR（表態-挑戰-反思）協議
  - **Commitment Gate**：在每個層級/章節轉換前收集使用者預測，再呈現資料
  - **Certainty-Triggered Contradiction**：偵測高信心語句（「顯然」「毫無疑問」），自動引入反面觀點
  - **Adaptive Intensity**：追蹤 commitment 準確率，動態調整挑戰頻率
  - **Self-Calibration Signal (S5)**：新收斂訊號，追蹤使用者在對話中是否展現自我校準能力
  - **SCR Switch**：使用者可隨時說「跳過預測」關閉 SCR，或「恢復預測」重新開啟，蘇格拉底式提問不受影響
- `deep-research/references/socratic_questioning_framework.md`：新增 SCR Overlay Protocol，對映 SCR 三階段到蘇格拉底功能
- 新增 `CHANGELOG.md`

### v2.7 (2026-03-09) — 誠信驗證 v2.0：反幻覺全面改版
- **integrity_verification_agent v2.0**：Anti-Hallucination Mandate（禁止靠 AI 記憶驗證）、消除灰色地帶分類（僅 VERIFIED/NOT_FOUND/MISMATCH）、強制 WebSearch audit trail、Stage 4.5 獨立全面驗證、Gray-Zone Prevention Rule
- **已知引用幻覺 Pattern**：5 類分類法（TF/PAC/IH/PH/SH，來自 GPTZero × NeurIPS 2025 研究）、5 種複合欺騙模式、實戰案例、文獻統計
- **出版後稽核**：對全部 68 篇引用做 WebSearch 逐一驗證，發現 21 篇有問題（31% 錯誤率），證明外部查證的必要性
- **論文修正**：移除 4 篇捏造引用、修正 6 篇作者錯誤、修正 7 篇書目細節、修正 2 篇格式問題

### v2.6.2 (2026-03-09) — 意圖匹配模式啟動
- **deep-research**：蘇格拉底模式改為**意圖匹配**啟動，取代關鍵字比對。支援任何語言 — 偵測含義（如「使用者想要引導式思考」）而非比對特定字串。
- **academic-paper**：Plan 模式改為**意圖匹配**啟動。偵測意圖信號如「使用者不確定如何開始」「使用者想要逐步引導」，不限語言。
- 兩個模式新增**預設規則**：當意圖模糊時，偏好 `socratic`/`plan` 而非 `full` — 先引導比較安全。
- 雙層架構：Layer 1（skill 啟動）用雙語關鍵字提高匹配信心；Layer 2（mode 路由）用語言無關的意圖信號。

### v2.6.1 (2026-03-09) — 雙語觸發關鍵字
- **deep-research**：新增繁體中文觸發關鍵字，涵蓋一般啟動和蘇格拉底模式。
- **academic-paper**：新增繁體中文觸發關鍵字及 Plan Mode 觸發區塊。
- 兩份 mode selection guide 加入雙語範例及中文專屬誤選情境。

### v2.6 / v2.4 / v1.4 (2026-03-08) — 15+ 項改進
- **deep-research v2.3**：新增系統性文獻回顧 / PRISMA 模式（第 7 模式）；3 個新 agent（risk_of_bias、meta_analysis、monitoring）；PRISMA 協議/報告模板；蘇格拉底收斂準則（4 訊號 + 自動結束）；快速模式選擇指南
- **academic-paper v2.4**：2 個新 agent（visualization、revision_coach）；修訂追蹤模板含 4 種狀態；引用格式轉換（APA↔Chicago↔MLA↔IEEE↔Vancouver）；統計視覺化標準；蘇格拉底收斂準則；修訂復原範例；**LaTeX 輸出強化** — 強制 `apa7` document class、`ragged2e` + `etoolbox` 文字對齊修正、表格欄寬公式、雙語摘要置中、標準字體集（Times New Roman + 思源宋體 VF + Courier New）、僅 tectonic 編譯 PDF
- **academic-paper-reviewer v1.4**：0-100 品質量表含行為指標；決策對照（≥80 接受、65-79 小修、50-64 大修、<50 退稿）；快速模式選擇指南
- **academic-pipeline v2.6**：自適應 checkpoint（FULL/SLIM/MANDATORY）；Phase E 宣稱驗證；素材護照（Material Passport）支援中途進入；跨 skill 模式顧問（14 情境）；團隊協作協議；強化銜接 schema（9 個含驗證規則）；誠信審查失敗復原範例

### v2.4 / v1.3 (2026-03-08)
- **academic-pipeline v2.4**：新增 Stage 6 過程紀錄 — 自動生成結構化論文創建過程紀錄（MD → LaTeX → PDF，中英雙語）；必含最後一章：**協作品質評估**，6 個維度各計 1–100 分（方向設定、智識貢獻、品質把關、迭代紀律、委派效率、後設學習），含誠實回饋與改進建議；pipeline 從 9 階段擴展為 10 階段

### v2.3 / v1.3 (2026-03-08)
- **academic-pipeline v2.3**：Stage 5 定稿階段現在會先詢問格式風格（APA 7.0 / Chicago / IEEE）；PDF 必須從 LaTeX 經 `tectonic` 編譯（禁止 HTML-to-PDF）；APA 7.0 使用 `apa7` document class（`man` 模式）+ XeCJK 支援中英雙語；字體：Times New Roman + 思源宋體 VF + Courier New

### v2.2 / v1.3 (2025-03-05)
- **跨 Agent 品質對齊**：統一定義（同儕審查、時效規則、CRITICAL 嚴重度、來源分級）橫跨所有 agent
- **deep-research v2.2**：synthesis 反模式、蘇格拉底自動結束條件、DOI+WebSearch 驗證、強化倫理誠信審查、模式轉換矩陣
- **academic-paper v2.2**：4 級論證強度評分、抄襲篩查、2 個新失敗路徑（F11 退稿復活、F12 研討會轉期刊）、Plan→Full 模式轉換
- **academic-paper-reviewer v1.3**：DA vs R3 角色邊界、CRITICAL 判定標準、共識分類（4/3/SPLIT/DA-CRITICAL）、信心分數加權、亞洲與區域期刊參考
- **academic-pipeline v2.2**：checkpoint 確認語意、模式切換矩陣、技能失敗降級策略、狀態所有權協議、素材版本控制

### v2.0.1 (2026-03)
- **精簡 4 個 SKILL.md**（-371 行, -16.5%）：移除跨 skill 重複、內嵌模板改為檔案引用、冗餘路由表、重複模式選擇區塊
- 修復 academic-paper 與 academic-pipeline 之間修訂迴圈上限的矛盾

### v2.0 (2026-02)
- **academic-pipeline v2.0**：5→9 階段、強制誠信驗證、兩階段審查、蘇格拉底修訂指導、可重現性保證
- **academic-paper-reviewer v1.1**：+魔鬼代言人審查者（第 7 agent）、+re-review 模式（驗收）、+審後蘇格拉底指導
- 新增 agent：`integrity_verification_agent` — 100% 引用/數據驗證，含稽核軌跡
- 新增 agent：`devils_advocate_reviewer_agent` — 8 維度論點挑戰
- 輸出順序：MD → Pandoc 可用時產出 DOCX（否則提供說明）→ 詢問 LaTeX → 確認 → PDF

### v1.0 (2026-02)
- 初版發布
- deep-research v2.0（10 agents、6 模式含 socratic）
- academic-paper v2.0（10 agents、8 模式含 plan）
- academic-paper-reviewer v1.0（6 agents、4 模式含 guided）
- academic-pipeline v1.0（調度器）
