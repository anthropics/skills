# ARS 效能說明

> **建議模型：當前最新一代 Claude 模型**（撰寫當下為 Fable 5），搭配 **Max plan**（或同等配置）。現行 Claude 模型採用 adaptive thinking，不需要手動指定 thinking budget。
>
> 完整學術 pipeline（10 階段）會消耗**大量 token** — 單次完整執行可能超過 200K 輸入 + 100K 輸出 token，視論文長度和修訂輪數而定。請依預算斟酌使用。
>
> 單獨使用個別 skill（如只用 `deep-research` 或 `academic-paper-reviewer`）的消耗明顯較少。

## 各模式 Token 消耗估算

| Skill / 模式 | 輸入 Token | 輸出 Token | 估算費用 |
|---|---|---|---|
| `deep-research` socratic | ~30K | ~15K | ~$0.60 |
| `deep-research` full | ~60K | ~30K | ~$1.20 |
| `deep-research` systematic-review | ~100K | ~50K | ~$2.00 |
| `academic-paper` plan | ~40K | ~20K | ~$0.80 |
| `academic-paper` full | ~80K | ~50K | ~$1.80 |
| `academic-paper-reviewer` full | ~50K | ~30K | ~$1.10 |
| `academic-paper-reviewer` quick | ~15K | ~8K | ~$0.30 |
| **完整 pipeline（10 階段）** | **~200K+** | **~100K+** | **~$4-6** |
| + 跨模型驗證 | +~10K（外部）| +~5K（外部）| +~$0.60-1.10 |

*以 ~15,000 字論文、~60 篇引用為基準估算。實際消耗隨論文長度、修訂輪數、對話深度而異。費用以 Opus 4.x 實測、Anthropic API 2026 年 4 月定價計算；換用更新模型時請當成數量級參考，不是精確報價。*

> **v3.11 引用查驗（#182）。** 確定性引用存在性 gate 呼叫的是外部書目 API（Semantic Scholar / OpenAlex / Crossref / arXiv），不是 LLM，因此**不增加上表的 Claude token 成本**——只在首次查詢時有網路延遲。持久化 SQLite cache（`~/.cache/ars/verification.db`，90 天 TTL）讓每篇論文只查驗一次、跨草稿重用；對已 cache 的書目重跑不做任何網路請求。見 [SETUP](SETUP.zh-TW.md#引用查驗-cachev3.11182)。

## 建議 Claude Code 設定

| 設定 | 功能說明 | 啟用方式 | 官方文件 |
|---|---|---|---|
| **Agent Team**（選用） | 啟用 `TeamCreate` / `SendMessage` tools 做手動多 agent 協作。**ARS 內部平行化不需要這個 flag** — skills 透過內建 `Agent` tool 直接 spawn subagent。僅在你想手動跨 session 協作持久 team 時有用。 | 設定 `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`（研究預覽） | 實驗性功能 — 尚無穩定文件 |
| **Auto 模式**（建議） | 自動接受大多數工具動作，讓長時間 pipeline 大幅減少中斷；同時由伺服器端 classifier 擋下超出你請求範圍的危險動作（例如部署到 production、force-push 或直接 push main、資料外洩）。明確的 ask 規則與 classifier 攔截仍可能跳出確認。是「手動逐項確認」與「完全不檢查」之間的折衷。 | 啟動時加上 `claude --permission-mode auto`（若可用），或在 `~/.claude/settings.json` 設定 `"permissions": { "defaultMode": "auto" }`；啟動後確認當前模式（研究預覽） | [Permission modes](https://code.claude.com/docs/en/permission-modes) |
| **Skip Permissions** | 跳過例行的工具使用確認，且不做任何安全檢查。比 auto 模式更快，但移除所有護欄。設計用途是用完即拋、無網路連線的隔離沙箱，不適合真實開發機器。 | 啟動時加上 `claude --dangerously-skip-permissions`（等同 `--permission-mode bypassPermissions`） | [Permission modes](https://code.claude.com/docs/en/permission-modes) |

> **⚠️ 模式選擇**：大多數無人值守的 pipeline，建議使用 auto 模式。它讓長時間執行大幅減少中斷，同時由 classifier 擋下超出你請求範圍的危險動作，但 ask 規則與 classifier 攔截仍可能跳出確認。auto 模式是研究預覽：它不保證安全，也不能取代敏感操作的人工審查，且行為可能變動。Skip Permissions 則完全移除這層安全網，僅應在無網路連線的隔離沙箱中使用，且你要確定可以接受 Claude 在無檢查的情況下執行檔案讀寫與 shell 指令。

### v3.7.0 Plugin agent 與模型路由

當 ARS 以 Claude Code plugin 方式安裝（`/plugin install academic-research-skills`）時，會把三個下游 worker agent 暴露為 plugin-shipped subagent：`synthesis_agent`、`research_architect_agent`、`report_compiler_agent`。三個 agent frontmatter 都標 `model: inherit`，意思是它們**繼承派工 session 的模型**而非寫死特定 floor：

- Opus session 跑完整 pipeline 時 agent 是 Opus，保留這三個 agent 設計的整合深度。
- Sonnet session 取得 Sonnet agent，跟主 session cost / latency 對齊。
- Agent 永遠不會默默掉到 Haiku — `inherit` 走的是主 session 模型，主 session 本身又被「ARS 全程不用 Haiku」政策守住。

意涵：**plugin agent 的 token 成本完全跟著上表各模式估算走，沒有額外加減**（`ARS_MODEL_TIERING` 未設定時）。dispatched agent 跟主 session 同一個模型，主 session 已經付的成本沒有再多一層 plugin agent 收費。設定 `ARS_MODEL_TIERING=economy` 時，plugin 暴露的 execution 型 agent（如 `report_compiler_agent`）改走分層規則——比 session model 低一階、樓地板 Opus 級（見 `shared/model_tiering.md`）。如果 pipeline 中途換模型（例如 revision pass 改用 Sonnet 省成本），下一輪 agent 派工自動跟上。

其他 ARS agent（`bibliography_agent`、`literature_strategist_agent` 等）在 v3.7.0 不暴露為 plugin agent；它們仍是 in-skill prompt template，由主 session 內聯執行，**預設**沒有獨立的模型路由層。Opt-in 的 `ARS_MODEL_TIERING`（#517）在其上加了一層 dispatch 時的路由規則：當分層方向適用於某角色時，session 會把該角色以子代理形式派發、鎖定目標層級（內聯角色也一樣——「派發為子代理」正是其機制）；flag 未設定時，本段描述的行為完全不變。見 `shared/model_tiering.md`。更廣的 plugin agent 覆蓋留到後續版本。

## 長時間 session 管理

完整 pipeline 設計為 human-in-the-loop，每個階段都需使用者確認。實務上一次完整執行會跨越數小時到數天，遠長於 Anthropic 的 prompt cache TTL（5 分鐘）。兩項結果：

1. **階段間 cache miss 是常態。** 當 stage checkpoint 停留超過 5 分鐘，下一階段會以未快取狀態讀取 context。這是 human-paced pipeline 不可避免的成本。
2. **跨 session 續跑依賴 Material Passport。** ARS 本身不跨 session 保留 orchestrator 狀態。要在新 session 續跑，把 Material Passport YAML 貼回即可；orchestrator 讀取 `compliance_history[]` 與階段完成標記定位中斷點。

### v3.6.2 Sprint Contract 審稿成本（`full` / `methodology-focus` 模式必跑）

Schema 13 sprint contract 把每個 reviewer agent 切成 Phase 1（不見論文、先承諾評分準則）+ Phase 2（看論文做審稿）兩階段。已 ship template 的兩個模式（`full` panel 5 + `methodology-focus` panel 2）下，每位 reviewer 約等於跑兩個 LLM turn。保留模式（`re-review` / `calibration` / `guided` / `quick`）維持 pre-v3.6.2 行為。

| Skill / 模式 | Token 影響 | 備註 |
|---|---|---|
| `academic-paper-reviewer full` | 每位 reviewer 約 +30-40% input + 小幅 output × 5 位 | Phase 1 讀 contract template + 論文 metadata；Phase 2 讀完整論文 |
| `academic-paper-reviewer methodology-focus` | 同上 shape，panel 2 | EIC + methodology 兩位 reviewer 各跑兩階段 |
| Synthesizer（固定一個）| +~2-3K input | 讀 contract + 各 reviewer 輸出，跑三步機械協議 |

實測待真實大規模審稿後校準。兩階段架構是 gated mode 的不可選 overhead，不是 tunable。

### v3.4.0 compliance agent 成本

在 Stage 2.5 與 Stage 4.5 加上 mode-aware `compliance_agent` 會讓 SR 全 pipeline token 多出：

| Skill / 模式 | 輸入 Token | 輸出 Token | 估算費用 |
|---|---|---|---|
| `deep-research systematic-review`（僅 2.5）| +~5–8K | +~3–5K | +~$0.15 |
| 全 pipeline SR（2.5 + 4.5）| +~10–15K | +~5–8K | +~$0.30 |
| `academic-paper full`（pre-finalize）| +~3–5K | +~2–3K | +~$0.08 |

以上為既有 per-skill 成本之上的額外增量（與上表共用 15,000 字 / 60 篇引用基準，見上表下方 footnote）。跨模型驗證成本（若啟用）維持不變。

### v3.6.3 Passport 重置邊界（opt-in）

設定 `ARS_PASSPORT_RESET=1` 後，每個 FULL checkpoint 變成 context 重置邊界。預期工作流程：

1. Session A 跑完一個 stage 到 FULL checkpoint。
2. 從 checkpoint 通知抄下 `[PASSPORT-RESET: hash=<hash>, stage=<completed>, next=<next>]` tag。
3. 開新的 Claude Code session（session B），貼入 `resume_from_passport=<hash>`。支援可選覆蓋：`resume_from_passport=<hash> stage=<n> mode=<m>`。
4. Session B 只讀 passport ledger，不重播 session A 的對話。Orchestrator 找到相符的 `kind: boundary` entry，append 一個 `kind: resume` entry 完成消費，然後繼續。繼續的 stage 由以下順序決定：使用者在 resume 指令附上 `stage=` 時以其為準，否則當 boundary 帶 `pending_decision` 時由 orchestrator 先重新詢問使用者再用對應選項的 `next_stage`，否則才採用記錄的 `next` 欄位。所有選項都終止時，`next` 可以是 `null`。

**何時重置比延續划算：**

- 長 pipeline，session A 累積 >100K input token，下個 stage 不需要這些上下文。
- `systematic-review` 模式，stage 獨立性由 Material Passport 精確界定。
- 撞到 5 分鐘 prompt cache TTL：重置讓下個 stage 重新起算，不用在臃腫 context 上付 cache miss。

**何時延續仍然比較好：**

- 短 pipeline（end-to-end < 30K input token）。
- Stage 有 in-session 隱含狀態、passport 沒帶的情況（例如使用者想保溫的 Socratic 對話分支）。
- Flag OFF 時，延續是不變的 pre-v3.6.3 預設。

**Passport 檔案位置規約：**

Orchestrator 預設在目前工作目錄下尋找 `./passports/<slug>/` 或 `./material_passport*.yaml`。將 hash 解析到磁碟上的 passport 檔案是整合方的責任，orchestrator 載入呼叫端工具提供的 passport。預設位置見上方 `./passports/<slug>/` 規約。

Resume 指令只定義 hash 與可選的 stage/mode 覆蓋：

```
resume_from_passport=<hash> [stage=<n>] [mode=<m>]
```

Resume 指令本身沒有路徑語法。客製 passport 位置在專案的 `CLAUDE.md` 設定，或由整合方的工具在呼叫 orchestrator 前處理。

**實測 token 節省：** 尚待真實 `systematic-review` 搭配儀器化測量。取得實測資料後會回填本節。目前不做任何數值宣稱。完整協議見 [`../academic-pipeline/references/passport_as_reset_boundary.md`](../academic-pipeline/references/passport_as_reset_boundary.md)。

## 文獻語料庫導入（v3.6.4+）

Material Passport 的 `literature_corpus[]` 欄位由**使用者自行撰寫的 adapter** 產出，不是 ARS 本身。v3.6.4 附三個 reference adapter：`scripts/adapters/folder_scan.py`、`scripts/adapters/zotero.py`、`scripts/adapters/obsidian.py`。執行方式與自行撰寫 adapter 的指引見 [`scripts/adapters/README.md`](../scripts/adapters/README.md)。

### 效能定位

- Adapter 在 ARS session 之外執行（跑 ARS 前跑）；執行時間由使用者自行負責，不進 ARS 的時間預算。
- Adapter 必須具備 determinism：同一份 input 重跑產出 byte-identical 輸出（時間戳除外）。
- `literature_corpus[]` 依 `citation_key` 排序；`rejection_log.rejected[]` 依 `source` 排序。
- Adapter 輸出大小與語料庫大小線性成長。500 筆 Zotero 書目約產出 300 KB 的 passport YAML。大型語料庫建議 ARS 消費端採 lazy load。

### 導入層邊界

- 不讀 PDF 內容、不做文字抽取、不跑 OCR。
- 不呼叫 Zotero Web API、Notion API 或任何遠端服務。
- 不抓付費牆後內容、不用使用者憑證連線機構圖書館。

這些邊界是刻意的，反映 ARS 的 data-layer 定位：ARS 是 writing / review layer 的框架，語料整合留在 user-owned code。如需 API-based live-sync adapter，由使用者以三個 reference adapter 為起點自行撰寫。

### 消費端整合

v3.6.5 起，Phase 1 兩個文獻 agent 透過 **corpus-first、search-fills-gap** 流程讀取 `literature_corpus[]`：`deep-research/agents/bibliography_agent.md` 與 `academic-paper/agents/literature_strategist_agent.md`。兩者走相同的五步流程與四條 Iron Rule（Same criteria / No silent skip / No corpus mutation / Graceful fallback on parse failure）。Search Strategy 報告新增 PRE-SCREENED 可重現區塊，列出已納入／排除／略過的 corpus entry，並含 F3 zero-hit 與 F4 provenance 報告。消費端啟動採 presence-based — passport 帶非空 `literature_corpus[]` 且解析成功時自動進入；解析失敗時 fallback 到 external-DB-only flow，並 surface `[CORPUS PARSE FAILURE]`。

完整 consumer 協定見 [`academic-pipeline/references/literature_corpus_consumers.md`](../academic-pipeline/references/literature_corpus_consumers.md)。`citation_compliance_agent` 的 corpus 整合留到 v3.6.6+。

### v3.6.5 corpus consumer 成本（presence 觸發）

Material Passport 帶非空 `literature_corpus[]` 時，Phase 1 讀取量隨 corpus 大小線性增長。PRE-SCREENED block 的 emit 本身屬 prompt-layer（成本可忽略）；LLM 成本來自 Step 1 pre-screening — 對每筆 corpus entry 套用當前 Inclusion / Exclusion 條件，比對 `title`（一定有）與已填的選填欄位（`abstract` / `tags`）。

| Corpus 規模 | Step 1 pre-screening（每位 consumer）| 備註 |
|---|---|---|
| 空 / 不存在 | 0 | external-DB-only flow 維持原樣 |
| ~50 筆（典型 Zotero 子集）| +~3-5K input + ~1-2K output | title + abstract 掃描 |
| ~200 筆 | +~10-15K input + ~3-5K output | title-only 掃描為主，abstract 視填充情況 |
| ~500 筆（大型文獻庫）| +~25-40K input + ~8-12K output | passport emit 前考慮先精簡 corpus |

Step 2 search-fills-gap 在 `uncovered_topics` 小（case A）時會降低 external-DB 成本，可部分抵銷 Step 1。淨效應實測待真實 SR run instrumentation 後校準；目前不下總體數字結論。Parse 失敗約一個短 turn 成本（parse + emit `[CORPUS PARSE FAILURE]` + fallback）。
