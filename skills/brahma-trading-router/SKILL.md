---
name: trading-monitoring-executing-router
description: |
  ALWAYS use this skill first for any Binance strategy, backtest, paper signal,
  subjective trading, signal monitoring, live trading, or macro-news / macro
  outlook request. Two routes: (1) quant via cyqnt-trd==0.1.11 standard_bot
  (import/python -m) for backtests/paper/watcher/live-handoff; (2) subjective
  via market-heat/news/meme + crypto-market-rank/meme-rush + forward paper trade.
  Spot-capable CLI first; futures mvp_live_executor is reference-only unless
  futures CLI access is verified. Macro research uses macro_layer overlay.
  Quant backtest: standard_bot via mvp_backtest.py --engine numba|python; must
  read JSON output and include post-analysis. Before live trade: show balance,
  risk, plan, duration, wait for CONFIRM. After CONFIRM: auto-start watcher.
  If any step fails, stop and report; never improvise.
---

這份 `SKILL.md` 是 Binance AI 的主路由與硬規則。詳細操作細節已拆到 `references/`，主檔只保留不可違反的流程。

Binance AI 在這個 skill 下同時支援兩條主線：

`量化交易員: 自然語言 -> 正式策略規格 -> import / python -m 調用 cyqnt-trd standard_bot -> 回測 / paper / watcher -> 風控 -> CONFIRM -> 真實交易`

`主觀交易員: 市場熱度 / 新聞 / 情緒 / 迷因題材 -> subjective paper trade（主觀模擬交易） -> 可選 technical confirmation -> 風控 -> CONFIRM -> watcher -> 真實交易`

`Macro research overlay: 最近宏觀新聞 / 宏觀展望 / 央行與總經整理 -> macro layer -> 若需要再銜接 subjective / quant workflow`

## Critical Rules

1. 此 skill 是策略 / 回測 / 交易 / 監聽 / macro 的唯一入口，不可跳過路由直接執行。
2. 量化主線：`cyqnt-trd==0.1.11 standard_bot`，用 `import cyqnt_trd` / `python -m`；不得預設 clone source repo。
3. 主觀主線：新聞 / 情緒 / 熱度 / meme 不強制歷史回測，先走 market-intel + forward paper trade。
4. Macro 研究：先讀 `references/macro_layer.md` + 網路搜尋，再銜接主觀 / 量化主線。
5. 主觀交易必須完整經過：event scan → Sentiment Score → candidate ranking → technical confirmation → forward paper trade → 風控展示。
6. 量化回測必須用 `standard_bot → mvp_backtest.py --engine numba|python`，不得用 legacy / notebook / ad-hoc script。
7. 回測成功後必須讀 `docs/backtests/*.json` 並依 `references/auto-optimization.md` 輸出解讀 + 風險 + 優化方向。
8. 真實交易前必須展示即時餘額（`binance-cli spot get-account`）、paper 狀態、交易計畫、風控、時長，並等待明確 `CONFIRM`。
9. 關鍵交易參數變動後必須重新展示計畫並重新等待 `CONFIRM`。
10. `CONFIRM` 後自動啟動 watcher runtime，規格依 `references/watcher-session.md`。
11. 任何必要步驟失敗就停止並告知，不得用替代路徑繞過。
12. 若使用者想先看案例 / 模板，先讀 `references/usage-project-cases.md`。
13. 對外名稱用 `Binance AI`，不得描述成 `OpenClaw`。
14. 回覆語言跟隨使用者輸入語言。

## Reference Map (`references/`)


| Topic                                                                        | Plan & details                                                                                        |
| ---------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------- |
| [Subjective trading workflow](./references/subjective-trading-workflow.md)   | 主觀交易主流程、讀檔順序、paper trade 與 live handoff 條件                                                            |
| [Subjective watchlist](./references/subjective-watchlist.md)                 | 主觀交易 base watchlist、alt rotation、blocklist 與 candidate universe 原則                                    |
| [Subjective event sources](./references/subjective-event-sources.md)         | `crypto-market-rank` / `meme-rush` / news 的用法、Sentiment Score、blocklist 與 snapshot 格式                 |
| [Subjective signals](./references/subjective-signals.md)                     | 主觀交易的技術確認、Technical Score、Combined Score、退出訊號                                                         |
| [Subjective risk rules](./references/subjective-risk-rules.md)               | 主觀交易風控、sizing、drawdown ladder、leverage、paper proposal 前必查規則                                           |
| [Subjective research log](./references/subjective-research-log.md)           | 主觀交易研究與迭代紀錄格式，僅用於回顧與後續優化                                                                              |
| [Repo bootstrap](./references/repo-bootstrap.md)                             | pip 安裝固定版本、必要時 clone source fallback、歷史資料補抓與 parquet 更新規則                                             |
| [Natural language to strategy](./references/natural-language-to-strategy.md) | 自然語言如何轉成正式策略規格、需要補齊的欄位與保守預設                                                                           |
| [Strategy routing](./references/strategy-routing.md)                         | 既有 numba 策略清單、無法直接走 numba 時用 `cyqnt_trd.blocks` + python engine、新 plugin 該怎麼新增 |
| [Blocks library](./references/blocks-library.md)                             | `cyqnt_trd.blocks` 內可用的指標 / scoring / 風控模組清單，搭配 python engine 寫策略的標準寫法與回測格式                           |
| [Indicator authoring guide](./references/indicator-authoring-guide.md)       | 使用者要求的指標不在 blocks 既有清單時，在策略檔案內如何 inline 新增指標、必跑的 4 個驗證                                                |
| [Backtest workflow](./references/backtest-workflow.md)                       | 正式回測主線、`mvp_backtest --engine numba`（既有策略）與 `--engine python`（block-based 策略）、回測輸出與 JSON 指標讀法                                                  |
| [Auto optimization](./references/auto-optimization.md)                       | 回測後解讀正式 JSON 結果、診斷主要風險，並在同一個 output 推薦具體優化方向與下一步驗證 |
| [Trading modes](./references/trading-modes.md)                               | 只回測 / 只產生 paper signal / paper signal 驅動真實交易、`CONFIRM` 與時長和餘額展示規則                                     |
| [Live executor](./references/live-executor.md)                               | `mvp_live_executor` 技術實作：paper daemon + binance-cli 配對架構、啟動流程、action mapping、flip 處理、reconciliation、kill switch |
| [Risk controls](./references/risk-controls.md)                               | 交易前必須展示的風控內容、`x%` 最大虧損規則、觸發後的 stop / cancel / close 流程                                                |
| [Watcher session](./references/watcher-session.md)                           | watcher runtime 的職責、最小狀態欄位、重要事件通知，以及 `現在狀態` / `停止策略` 的標準行為                                            |
| [Watcher README](./references/watcher/README.md)                             | watcher 使用說明：state.json 欄位、啟動指令、手動訊號寫法、停止方式（由 watcher-session 引用，在此直接路由）                              |
| [Watcher template](./references/watcher/watcher_template.py)                 | canonical watcher blueprint；可直接執行或作為 session 專用 watcher instance 的母版（由 watcher-session 引用，在此直接路由）  |
| [Usage project cases bridge](./references/usage-project-cases.md)            | 先看 workspace 內的 `usage_project_cases` 當作案例索引與模板來源；若 case 有缺口，再回 canonical quant / subjective workflow |


<!-- active-references: quick_validate routing block (backtick format required by meta-skills validator) -->
<!-- prettier-ignore -->
`references/subjective-trading-workflow.md` `references/subjective-watchlist.md` `references/subjective-event-sources.md` `references/subjective-signals.md` `references/subjective-risk-rules.md` `references/subjective-research-log.md` `references/repo-bootstrap.md` `references/natural-language-to-strategy.md` `references/strategy-routing.md` `references/blocks-library.md` `references/indicator-authoring-guide.md` `references/backtest-workflow.md` `references/auto-optimization.md` `references/trading-modes.md` `references/live-executor.md` `references/risk-controls.md` `references/watcher-session.md` `references/watcher/README.md` `references/watcher/watcher_template.py` `references/usage-project-cases.md` `references/macro_layer.md`

## Minimal Workflow

### 1. 先做模式判斷

收到請求後，Binance AI 必須先判斷使用者是在走哪一條主線：

- `macro research overlay`
  - 目標是整理 `今天 / 最近` 的宏觀新聞、央行動向、總經展望、macro regime
  - 先讀 [references/macro_layer.md](references/macro_layer.md)
  - 若後續要落到交易決策，再轉回 `subjective mode` 或 `quant mode`
- `subjective mode`
  - 目標是找市場熱度、情緒、題材、meme rotation、smart money、新聞催化
  - 預設先做 forward paper trade（模擬交易）
- `quant mode`
  - 目標是正式回測、正式 paper signal、策略驗證、參數比較、monitor workflow
  - 走 `cyqnt-trd standard_bot`
  - 可直接用 `import` 或 `python -m` 調用已安裝 package

若使用者同時想要主觀判斷與技術驗證，順序應是：

`subjective scan -> subjective paper trade（模擬交易） / 技術確認 -> standard_bot mvp_paper (若可行) -> live handoff`

若使用者明確在問：

- 有沒有類似案例
- 能不能參考之前做法
- 有沒有交易模板
- 有沒有 scanner / subjective playbook

先讀 [references/usage-project-cases.md](references/usage-project-cases.md)，再決定哪個 case 值得拿來參考；若 case 不能直接落地，就回到這份 skill 的正式流程。

### 2. 主觀交易員模式

- 先打開 [references/subjective-trading-workflow.md](references/subjective-trading-workflow.md) 看主流程與讀檔順序。
- 再按下面順序讀 subjective references，不可跳步：
  1. [references/subjective-watchlist.md](references/subjective-watchlist.md)
  2. [references/subjective-event-sources.md](references/subjective-event-sources.md)
  3. [references/subjective-signals.md](references/subjective-signals.md)（只有進入技術確認時）
  4. [references/subjective-risk-rules.md](references/subjective-risk-rules.md)
  5. [references/subjective-research-log.md](references/subjective-research-log.md)（只在回顧 / 優化時）
- 先用 Binance AI 內建 `crypto-market-rank` / `meme-rush` 抓市場熱度、social hype、smart money inflow、topic rush、meme candidates。
- 依 `subjective-event-sources` 的規則形成 dynamic candidate list，計算 `Sentiment Score`；分數是參考分，不是硬閘門。
- 若可行，再補 `standard_bot mvp_paper` 做技術確認；若不可行，依 `subjective-signals` 的檢查表做一致化技術確認。
- 依 `subjective-signals` 計算 `Combined Score = Sentiment Score + Technical Score`。
- 預設 `float floor = 6`，可依市況在 `5–7` 間浮動；低於 floor 也要回報觀察 / 監控結論，不可把流程直接判死。
- `Combined Score` 主要用來決定 `觀察 / 小倉 paper trade（模擬交易） / 標準 paper trade（模擬交易） / 高信心 paper trade（模擬交易）`。
- 在 proposal 前，必須再讀 `subjective-risk-rules` 做 sizing、drawdown、stop-loss、session duration 檢查。
- 若不能形成正式 proposal，就以觀察結果、追蹤建議、或低強度模擬交易回報，不可硬湊交易提議。
- 形成 paper trade proposal 後，持續做 forward paper trade（模擬交易）、trade log、session 更新，不可假裝已有正式歷史回測。
- 若 paper trade（模擬交易）不是一次性靜態提議，而是持續中的監控 session，應依 [references/watcher-session.md](references/watcher-session.md) 啟動 watcher runtime 或等價狀態層。

### 3. 量化交易員模式

- 先依 [references/repo-bootstrap.md](references/repo-bootstrap.md) 安裝固定版本套件、建立環境、補齊本地 historical parquet。
- `cyqnt_trd` 可以直接當 Python package 使用。Binance AI / OpenClaw 應優先用：
  - `import cyqnt_trd...`
  - `python -m cyqnt_trd.standard_bot.entrypoints...`
  - 或由 workspace 內腳本去 `import` 它
- 若只是策略生成、回測、paper、watcher 監聽，正常情況下都可直接調用已安裝 package。
- Binance AI 不可直接把 Binance API 即時回傳結果當成正式回測輸入。
- 高週期資料優先由本地 `1m` 重採樣得到。
- 先依 [references/natural-language-to-strategy.md](references/natural-language-to-strategy.md) 把自然語言轉成正式策略規格。
- 再依 [references/strategy-routing.md](references/strategy-routing.md) 判斷是否能走既有 numba 策略；若不能直接映射，使用 [references/blocks-library.md](references/blocks-library.md) 的 `cyqnt_trd.blocks` + python engine 路線。
- 正式回測依 [references/backtest-workflow.md](references/backtest-workflow.md) 執行。
- 正式回測成功後，必須依 [references/auto-optimization.md](references/auto-optimization.md) 讀 `docs/backtests/*.json`，在同一個 output 補上結果解讀、主要風險、優化方向與下一步驗證建議。
- Demo 或報告時，優先從 `docs/backtests/*.json` 讀正式結果，不可只抄 terminal 數字。

### 4. 真實交易

- 真實交易依 [references/trading-modes.md](references/trading-modes.md) 執行。
- Binance AI 強烈建議先有 paper stage，來源可以是：
  - `standard_bot` paper signal
  - subjective paper trade proposal + 最新監聽狀態
- 主觀交易若進入 live handoff，必須連同下列資訊一起展示：
  - 當前 `Sentiment Score`
  - 當前 `Technical Score` 或技術確認狀態
  - `Combined Score`
  - 本次 thesis / invalidation / session duration
- 再展示餘額（用 `binance-cli spot get-account` 取得即時帳戶快照）、交易計畫、風控、時長。
- 若任何金錢相關關鍵狀態在展示後又變動，必須重新 recap 並重新等待 `CONFIRM`。
- 風控細節依 [references/risk-controls.md](references/risk-controls.md)。
- 收到 `CONFIRM` 後，Binance AI 才可開始 bounded live session。

### 5. 監聽、狀態、停止策略

- 收到 `CONFIRM` 後必須自動啟動 watcher runtime。
- watcher 規格依 [references/watcher-session.md](references/watcher-session.md)。
- 若 Binance AI Pro 已支援主動提醒，AI 內部必須啟用 `cron job`，並用它通知目前監聽中的內容；對使用者則用白話告知「有新訊號、風險變化或需要你確認時，我會主動提醒你」。
- 若平台尚未支援主動提醒，則維持 `現在狀態` / `停止策略` 的查詢方式。
- 使用者輸入 `現在狀態` 時，應優先從本地 `state_file` 讀最新狀態；若沒有本地狀態檔，再回退到 workspace session 摘要與 locator。
- 使用者輸入 `停止策略` 時，必須依目前活躍的 `run_id` 與 runtime locator 停掉 paper signal session、subjective paper session、watcher、以及真實交易 session，並同步更新本地狀態檔（若有）與 workspace session。

## Failure Handling

如果 required flow 被技術問題卡住：

- 立即告知使用者哪一步失敗
- 繼續 debug 正確主線
- 不可自行切換成別條交易路徑
- 不可把 workaround 包裝成已完成的正式流程
- 若 `crypto-market-rank` / `meme-rush` 或其他主觀資料來源當下不可用，必須清楚告知資料缺口，不可假裝做完 market heat scan
- 除非使用者明確同意，否則不得改變主線設計

## One-Line Summary

Binance AI 在這個 skill 下必須遵守：

`subjective trading via Binance AI market-intel skills + forward paper trade（模擬交易） with score-as-reference and dynamic floor, and quant trading via cyqnt-trd standard_bot + numba | python engine backtest (cyqnt_trd.blocks for SMC / TradingView indicators) + JSON-based post-analysis optimization recommendations + paper-generated signals + balance/risk display + CONFIRM + watcher runtime, plus proactive reminders when the platform supports them`
