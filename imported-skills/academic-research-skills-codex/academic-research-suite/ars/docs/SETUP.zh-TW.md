# ARS 安裝設定

Academic Research Skills 的前置需求與選用設定。只需要 Markdown 輸出與預設 Claude pipeline（繼承 session 模型）的人，大部分內容可以略過。請見下方「最小可行設定」。

---

## 最小可行設定

1. 安裝 Claude Code（見下方）。
2. 設定 `ANTHROPIC_API_KEY`。
3. 在這個 repo（或任何把 ARS 放在 `.claude/skills/` 下的專案）執行 `claude`。

這樣就夠了。可得到 Markdown 輸出與 DOCX 轉換說明。以下其他內容都是選用。

---

## 安裝 Claude Code

**建議：原生安裝程式**（不需要 Node.js，自動更新）：

```bash
# macOS / Linux
curl -fsSL https://claude.ai/install.sh | bash

# Windows (PowerShell)
irm https://claude.ai/install.ps1 | iex
```

<details>
<summary>替代方案：npm 安裝（已棄用）</summary>

需要 Node.js 18+。

```bash
npm install -g @anthropic-ai/claude-code
```

</details>

## 設定 API Key

你需要一個 Anthropic API key，請至 <https://console.anthropic.com/> 取得。

```bash
# Claude Code will prompt for your API key on first run
claude
```

或設定環境變數：

```bash
export ANTHROPIC_API_KEY=sk-ant-xxxxx
```

## DOCX 輸出（選用）

若要直接產出 `.docx`，需要安裝 [Pandoc](https://pandoc.org/)。若系統沒有 Pandoc，formatter 會回退為提供 Markdown 與 DOCX 轉換說明。

```bash
# macOS
brew install pandoc

# Linux (Debian/Ubuntu)
sudo apt-get install pandoc

# Windows — download from https://pandoc.org/installing.html
```

## LaTeX / PDF 輸出（選用）

PDF 輸出需要 [tectonic](https://tectonic-typesetting.github.io/) 和特定字型。**這是選用的**。Markdown 輸出與 DOCX 轉換說明不需要這些。

```bash
# macOS
brew install tectonic

# Linux (Debian/Ubuntu)
curl --proto '=https' --tlsv1.2 -fsSL https://drop-sh.fullyjustified.net | sh

# Windows — download from https://tectonic-typesetting.github.io/en-US/install.html
```

**所需字型**（APA 7.0 中文輸出）：

- **Times New Roman**：macOS/Windows 通常已內建；Linux 安裝 `ttf-mscorefonts-installer`
- **Source Han Serif TC VF**（思源宋體）：從 [Google Fonts](https://fonts.google.com/specimen/Noto+Serif+TC) 或 [Adobe GitHub](https://github.com/adobe-fonts/source-han-serif) 下載
- **Courier New**：通常已內建

> 如果只需要 Markdown 輸出或 DOCX 轉換說明，可完全跳過此步驟。直接產出 `.docx` 需要 Pandoc，PDF 需要 `tectonic`。

---

## Material Passport `literature_corpus[]` adapters（v3.6.4+，選用）

如果你已經維護一個策展過的文獻語料（Zotero、Obsidian、PDF 資料夾等），可以先把它打包進 Material Passport，讓 Phase 1 ARS agent 在去外部資料庫搜尋之前先讀你的文獻庫。此功能採 opt-in 與 presence-based 設計。沒提供語料時，ARS 走 external-DB-only flow，行為不變。

v3.6.4 附三個 reference Python adapter，位於 `scripts/adapters/`：

```bash
# 1. Install adapter dependencies (PyYAML + jsonschema, already in requirements-dev.txt)
pip install -r requirements-dev.txt

# 2. Run a reference adapter (pick one that matches your corpus source).
#    Both --passport and --rejection-log are required.
python scripts/adapters/folder_scan.py --input /path/to/pdfs               --passport passport.yaml --rejection-log rejection_log.yaml
python scripts/adapters/zotero.py      --input my-zotero-export.json       --passport passport.yaml --rejection-log rejection_log.yaml
python scripts/adapters/obsidian.py    --input ~/Obsidian/Lit\ Notes       --passport passport.yaml --rejection-log rejection_log.yaml

# 3. Pass the resulting passport.yaml into your ARS session
#    (concrete invocation depends on which skill you're running — see scripts/adapters/README.md)
```

每個 adapter 產兩個檔案：`passport.yaml`（Schema 9，已填 `literature_corpus[]`）與 `rejection_log.yaml`（永遠輸出，無 rejection 時為空，採 categorical reason 封閉 enum）。Reference 之外的語料來源預期由使用者自行撰寫 adapter，遵循 [`academic-pipeline/references/adapters/overview.md`](../academic-pipeline/references/adapters/overview.md)。

v3.6.5 接上 `bibliography_agent`（deep-research, Phase 1）與 `literature_strategist_agent`（academic-paper, Phase 1）作為 consumer。兩者在 passport 帶非空 corpus 且解析成功時走 corpus-first / search-fills-gap flow。完整 consumer 協定見 [`academic-pipeline/references/literature_corpus_consumers.md`](../academic-pipeline/references/literature_corpus_consumers.md)。

## 選用環境變數（v3.5.1+）

ARS 暴露若干 opt-in flag，全部預設 OFF；設定後僅影響當前 session。

| Flag | 起始版本 | 作用 | 參考 |
|---|---|---|---|
| `ARS_CROSS_MODEL` | v3.0 | 啟用跨模型驗證（見下節） | [§「跨模型驗證」](#跨模型驗證選用) |
| `ARS_SOCRATIC_READING_PROBE=1` | v3.5.1 | 啟用 `socratic_mentor_agent` 的讀書檢查 probe layer。僅 goal-oriented intent；使用者引用過具體論文時最多觸發一次；婉拒不留紀錄懲罰。 | `deep-research/agents/socratic_mentor_agent.md` |
| `ARS_PASSPORT_RESET=1` | v3.6.3 | 把每個 FULL checkpoint 提升為 context 重置邊界。**emit** boundary entry 必須設此 flag；新 session 用 `resume_from_passport=<hash>` 續跑**不需要** flag。`systematic-review` 模式下 flag ON 時，每個 FULL checkpoint 一律強制重置。 | `academic-pipeline/references/passport_as_reset_boundary.md` |
| `ARS_CROSS_MODEL_SAMPLE_INTERVAL` | v3.5.0 | 跨模型完整性抽查的取樣間隔（advisory） | `shared/cross_model_verification.md` |
| `ARS_VERIFICATION_CACHE_PATH` | v3.11 | 覆寫引用查驗 cache 的位置（見下節）。不是 on/off flag——cache 預設開啟，此變數只改位置。 | `scripts/verification_cache.py` |
| `ARS_MODEL_TIERING` | Unreleased (#517) | Opt-in 模型分層：`economy`（frontier session——execution 型 agent 降一階，樓地板 Opus 級）或 `quality-boost`（低於 frontier 的 session——judgment 型 agent 在檢查點表面跳升到 frontier 級：Stage 2.5/4.5 關卡、opt-in 的 Stage 4→5 claim–ref audit、最終審查）。未設定 = 全部用 session model；未知值警告一次後視同未設定。 | `shared/model_tiering.md` |

---

## 引用查驗 cache（v3.11，#182）

確定性引用存在性 gate（#182）會對每筆引用比對 Semantic Scholar、OpenAlex、Crossref、arXiv。為避免跨草稿重複查同一篇論文，結果存進本機 SQLite。

- **無需設定。** Cache 首次使用時自動建在 `~/.cache/ars/verification.db`，條目 90 天後過期。arXiv resolver 不需 API key。
- **改位置**：匯出 `ARS_VERIFICATION_CACHE_PATH=/your/path.db`（例如跨專案共用一份 cache，或放在較快的磁碟）。
- **作廢單筆引用**：`/ars-cache-invalidate <citation_key>`——移除該 key 的所有 cache 列（四個 resolver、所有 query form）；若無 cache 則為冪等 no-op。

Cache 為單一 process（SQLite WAL）；多使用者共用同一 cache 檔案不在範圍內。

---

## 跨模型驗證（選用）

ARS 使用繼承的 Claude session 模型即可完整運作。想要更高信心，可選擇啟用第二 AI 模型來獨立驗證完整性檢查，並挑戰魔鬼代言人。

### 快速設定

```bash
# Step 1: Set your API key (choose one or both)
export OPENAI_API_KEY="sk-your-key-here"        # For GPT-5.5 / GPT-5.5 Pro
export GOOGLE_AI_API_KEY="AIza-your-key-here"    # For Gemini 3.1 Pro

# Step 2: Choose your cross-verification model
export ARS_CROSS_MODEL="gpt-5.5"                # Recommended pair (gpt-5.5-pro = strongest reasoning, ~6x cost)
# or: export ARS_CROSS_MODEL="gemini-3.1-pro-preview"  # Strong at factual verification
# or: export ARS_CROSS_MODEL="gpt-5.6-sol"      # Frontier, provisional pending ARS validation (same rates as gpt-5.5)

# Optional: reasoning effort for OpenAI verifier calls (unset = provider default)
# export ARS_CROSS_MODEL_REASONING_EFFORT="medium"

# Step 3: Run Claude Code as normal — cross-verification activates automatically
claude
```

### 啟用後的差異

| 功能 | 未啟用跨模型 | 啟用跨模型 |
|---|---|---|
| 完整性驗證 | 單模型 100% 檢查 | + 第二模型風險分層驗證：高影響引用 100%（最終關卡再加新增/變更主張的引用 100%）+ 其餘抽樣 |
| 魔鬼代言人 | 單模型 DA | + 跨模型產生獨立 critique，新發現自動加入 |
| 同儕審查 | 5 位審稿人（同模型） | 同樣 5 位審稿人 + 跨模型 DA critique / calibration 支援 |
| 不可逆檢查點 | 單模型決策 | + 設計凍結與最終編輯決定各加一次盲判跨模型決策；分歧上報給你，絕不平均 |

### 費用

完整 pipeline 會增加約 $0.60-1.10 的跨模型 API 費用（數量級估計；以 GPT-5.4 Pro 定價量測）。現行模型陣容與詳細拆解見 [`shared/cross_model_verification.md`](../shared/cross_model_verification.md)。

### 沒有 API key？沒問題

沒有設定 `ARS_CROSS_MODEL` 時，一切照舊運作。跨模型功能不會出現，也不會增加任何額外開銷。

---

## 安裝方式

Claude 會在 `<install-root>/<skill-name>/SKILL.md` 尋找 skills。這個 repo 包含四個獨立 skills，每個都有自己的 `SKILL.md`：

- `deep-research`
- `academic-paper`
- `academic-paper-reviewer`
- `academic-pipeline`

不要把整個 repository 當成單一巢狀 skill 資料夾安裝到 `.claude/skills/academic-research-skills/`。那會讓四個 `SKILL.md` 比 Claude 可發現的位置多埋一層。請參考 Anthropic 的 [Claude Code Skills documentation](https://code.claude.com/docs/en/skills)。

### 方法零：Claude Code Plugin（v3.7.0+，Claude Code CLI / IDE 用戶推薦）

如果你用的是 Claude Code CLI、VS Code extension 或 JetBrains extension，可以一行指令安裝 ARS：

```text
/plugin marketplace add Imbad0202/academic-research-skills
/plugin install academic-research-skills
```

四個 skill（`deep-research`、`academic-paper`、`academic-paper-reviewer`、`academic-pipeline`）會從 plugin 的 `skills/` 目錄自動載入。

**強烈建議開啟 auto-update。** 進 `/plugin` UI 找到 `academic-research-skills`，把 auto-update 開起來。ARS 大約 1–2 週發新版，開了之後會自動同步。手動更新已安裝的 plugin：`/plugin update academic-research-skills`。（`/plugin marketplace update academic-research-skills` 只重新拉 marketplace 來源，不會更新已裝 plugin。）

**Plugin 平台支援範圍：**
- ✅ Claude Code CLI / VS Code extension / JetBrains extension — 完整支援
- ❌ claude.ai 網頁版 / Claude for Work / Anthropic API 直呼 — 不支援 plugin，請改用方法一 / 二 / 三
- ➡️ Codex CLI — 改裝姊妹版 [`Imbad0202/academic-research-skills-codex`](https://github.com/Imbad0202/academic-research-skills-codex)（同一套 workflow 內容、Codex 原生包裝）

### 方法一：作為專案 Skills（推薦）

當你希望 ARS 可在既有 Claude Code 專案內使用時，請用此方式。

先將 repo clone 到穩定的本機路徑，再把每個 skill 資料夾複製到專案的 `.claude/skills/` 目錄：

```bash
git clone https://github.com/Imbad0202/academic-research-skills.git ~/academic-research-skills

cd /path/to/your/project
mkdir -p .claude/skills
cp -R ~/academic-research-skills/deep-research .claude/skills/deep-research
cp -R ~/academic-research-skills/academic-paper .claude/skills/academic-paper
cp -R ~/academic-research-skills/academic-paper-reviewer .claude/skills/academic-paper-reviewer
cp -R ~/academic-research-skills/academic-pipeline .claude/skills/academic-pipeline
```

預期路徑形狀：

```text
/path/to/your/project/.claude/skills/deep-research/SKILL.md
/path/to/your/project/.claude/skills/academic-paper/SKILL.md
/path/to/your/project/.claude/skills/academic-paper-reviewer/SKILL.md
/path/to/your/project/.claude/skills/academic-pipeline/SKILL.md
```

接著將 `.claude/CLAUDE.md` 的內容複製到你專案的 `.claude/CLAUDE.md`（若已有則合併）。

> **全域 Claude Code 安裝：** 若希望所有 Claude Code 專案都能使用這些 skills，請改安裝四個資料夾到 `~/.claude/skills/`：
>
> ```bash
> git clone https://github.com/Imbad0202/academic-research-skills.git ~/academic-research-skills
>
> mkdir -p ~/.claude/skills
> cp -R ~/academic-research-skills/deep-research ~/.claude/skills/deep-research
> cp -R ~/academic-research-skills/academic-paper ~/.claude/skills/academic-paper
> cp -R ~/academic-research-skills/academic-paper-reviewer ~/.claude/skills/academic-paper-reviewer
> cp -R ~/academic-research-skills/academic-pipeline ~/.claude/skills/academic-pipeline
> ```

### 方法二：作為獨立專案

當你想直接在 ARS repository 內工作時，請用此方式。

```bash
git clone https://github.com/Imbad0202/academic-research-skills.git
cd academic-research-skills
claude
```

<details>
<summary><strong>沒有安裝 Git？</strong>改下載 ZIP</summary>

1. 前往 <https://github.com/Imbad0202/academic-research-skills>
2. 點擊綠色 **Code** 按鈕 → **Download ZIP**
3. 解壓縮 ZIP 到你想要的位置
4. 方法一：將解壓後的四個 skill 資料夾（`deep-research`、`academic-paper`、`academic-paper-reviewer`、`academic-pipeline`）複製到你專案內的 `.claude/skills/`
5. 獨立使用：在解壓後的資料夾中開啟終端機，執行 `claude`

</details>

### 方法三：Claude Cowork（桌面版）

當你想在 [Claude Cowork](https://support.claude.com/en/articles/13345190-get-started-with-claude-cowork) 使用四個 ARS skills 時，請用此方式。Cowork 是 Claude Desktop 的 agentic workspace。

> **Cowork 不會讀取 `~/.claude/skills/`。** 該目錄屬於 Claude Code（CLI / IDE），Cowork 不會掃描它。Cowork 讀取的是你透過 **Settings → Capabilities → Skills** 上傳的 skill，每個 skill 各自打包成一個 zip。把 skill 資料夾 symlink 或複製到 `~/.claude/skills/`，無論重啟幾次都不會讓它們出現在 Cowork。

#### 前置需求

- macOS 或 Windows 的最新版 Claude Desktop。請從 Anthropic 的 [Claude Desktop page](https://claude.ai/download) 下載。
- 可用的網路連線；Cowork tasks 會呼叫 Anthropic API。
- Cowork tasks 執行時，請保持 Claude Desktop 開啟。Cowork 在 Desktop process 內執行。
- 具備 Cowork 存取權的付費方案。目前方案可用性請參考 Anthropic 的 [Cowork requirements](https://support.claude.com/en/articles/13345190-get-started-with-claude-cowork)。
- **必須在 Settings → Capabilities 啟用 code execution / file creation**，否則 Skills 區段不會出現。參見 Anthropic 的 [Use Skills in Claude](https://support.claude.com/en/articles/12512180-use-skills-in-claude)。
- Team 或 Enterprise 方案中，組織管理員可能停用了 Skills。若啟用 code execution 後 Skills 區段仍未出現，請管理員檢查組織層級設定。

#### 步驟 1：每個 skill 各打一個 zip

clone repo 後，把四個 skill 資料夾各自打包成 zip，讓每個 zip 的頂層都是它自己的 `SKILL.md`（不要多包一層資料夾）。`-x "*.DS_Store"` 用來排除 macOS metadata。

```bash
git clone https://github.com/Imbad0202/academic-research-skills.git
cd academic-research-skills

for s in deep-research academic-paper academic-paper-reviewer academic-pipeline; do
  (cd "$s" && zip -r "../$s.zip" . -x "*.DS_Store")
done
```

這會在 repo 根目錄產生四個 zip：`deep-research.zip`、`academic-paper.zip`、`academic-paper-reviewer.zip`、`academic-pipeline.zip`。每個 zip 的頂層結構如下：

```text
SKILL.md
agents/
examples/
references/
templates/
```

#### 步驟 2：逐一上傳每個 zip

1. 在 Claude Desktop（或 claude.ai，上傳的 skill 會同步到同一個帳號）中，前往 **Settings → Capabilities → Skills**。
2. 用 Skills 面板的 **+** 上傳 skill，選擇其中一個 zip。四個 zip 各上傳一次，一次一個。
3. 每個 skill 上傳後會出現在 **Personal skills** 下，已自動啟用，**Trigger 為 Slash command + auto**。以相同名稱重新上傳會覆蓋既有的 skill（更新到新版 ARS 時很方便）。

已在 Claude Desktop 驗證（2026 年 6 月）：用此方式打包的 `deep-research.zip` 可乾淨安裝，完整 skill description 保留（不會被截到 200 字元），且 `/deep-research` 會出現在 Cowork command palette。

#### 步驟 3：在 Cowork Task 中使用

在 Cowork Task 中輸入 `/` 開啟 command palette 選取 skill，或直接用白話描述意圖（例如「幫我對 X 做深度文獻回顧」），Cowork 會依 skill 的 `description` 自動路由。

#### 與 Claude Code 的一個取捨

用此方式上傳的每個 skill 各自獨立運作，是一份 standalone 的指令集，體驗與 Claude Code 不同。在 Claude Code 中，四個 skill 是協作團隊：`academic-pipeline` 會把它們串起來（research → write → review → revise），每個 skill 各自驅動自己那組 sub-agent。Cowork 的 uploaded-skill runtime 不提供這種 sub-agent orchestration，所以個別 skill 會回應，但完整的 end-to-end pipeline 不會像在 Claude Code 那樣運作。想要完整的協作體驗，請用上方的方法零（plugin）或方法一（project skills）在 Claude Code 安裝 ARS。

### 方法四：使用 claude.ai（網頁版）

ARS 是為 Claude Code 設計的 skill suite。四個 skill 各自是 12-13 個 agent 組成的工作團隊，仰賴多 agent 協作、`scripts/` 下可執行的轉接器，以及 Material Passport 的檔案交接。claude.ai 網頁版的執行環境跟 Claude Code 不同，要把這個 repository 接進 claude.ai 有兩條路徑，差別很大：

- **方法 4b — Project + GitHub integration**（推薦給 claude.ai 使用者）：把 repository 接進 claude.ai Project 當成可檢索的知識庫。Claude 可以讀取 skill 主體、references、schemas 與範例輸出，並依此回答問題或起草。不是 Skill 安裝 — 不會自動載入、不會做 skill routing，但內容可完整讀取與引用。
- **方法 4a — Custom Skill upload**：claude.ai 標準的 Skill 安裝路徑（Settings → Capabilities → Skills，每個 skill 各一個 zip）。**不推薦給本 suite 使用** — 使用前請先看下方原因。

#### 前置需求

- claude.ai 帳號。可用方案因 sub-method 不同（見下）。
- **方法 4b**：claude.ai Projects 各方案皆可使用，詳見 Anthropic 的 [What are Projects?](https://support.claude.com/en/articles/9517075-what-are-projects)；付費方案（Pro、Max、Team、Enterprise）有更大的知識庫容量與更強的檢索能力。需要透過 Anthropic connector 進行 GitHub 驗證 — 請參考 [Using the GitHub integration](https://support.claude.com/en/articles/10167454-using-the-github-integration) 與 [Set up Claude integrations](https://support.claude.com/en/articles/10168395-set-up-claude-integrations)。Private repositories 需要在 repo 或 organization 上授權 Anthropic GitHub App。Team 與 Enterprise 方案則需要 owner 層級先啟用 connector，使用者才能加入 GitHub 來源的檔案。
- **方法 4a**：Custom Skills 在 Free、Pro、Max、Team、Enterprise 方案皆可使用，詳見 Anthropic 的 [Use Skills in Claude](https://support.claude.com/en/articles/12512180-use-skills-in-claude)。同篇文件也說明 Skills 需要在 Settings → Capabilities 啟用 **code execution**。方法 4a 不需要 GitHub 驗證 — 你要在本機將每個 skill 資料夾各自壓成 zip，再透過 Settings → Capabilities → Skills 逐一上傳。Zip 結構錯誤與 200 字元 `description` 上限會在上傳時顯示錯誤；請參考 Anthropic 的 [Custom Skills packaging documentation](https://claude.com/docs/skills/how-to) 與 [How to create custom Skills](https://support.claude.com/en/articles/12512198-how-to-create-custom-skills)。

#### 方法 4b：Project + GitHub integration（推薦給 claude.ai）

claude.ai Projects 會把內容當成靜態知識提供給 Claude 檢索與引用。請參考 Anthropic 的 [What are Projects?](https://support.claude.com/en/articles/9517075-what-are-projects)。這不是 Skill 安裝。Skill 不會自動載入，trigger phrases 不會路由。Claude 可以讀取 repo 內容、針對它回答問題或進行引用，但不會把 skills 當成 agentic workflows 執行。

當你希望 claude.ai 能存取 repo 內容（包含 agent 定義、references、範例輸出）以便閱讀與引用，但不需要 agentic skill execution 時，使用此方式。若要做 agentic execution，請改用方法 3（Cowork）的桌面環境，或方法 1、方法 2 在 Claude Code 內執行。

1. 登入 [claude.ai](https://claude.ai)。
2. 建立新 Project：**Projects** → **Create Project**。
3. 從 GitHub 匯入：在 Project 中，點擊 **Files** → **+** → **GitHub** → 選擇 `Imbad0202/academic-research-skills`。
4. 選取以下資料夾與檔案。

   | 選取 | 目錄 / 檔案 | 原因 |
   |---|---|---|
   | ✅ | `deep-research/` | 核心 skill 內容，可供閱讀 |
   | ✅ | `academic-paper/` | 核心 skill 內容，可供閱讀 |
   | ✅ | `academic-paper-reviewer/` | 核心 skill 內容，可供閱讀 |
   | ✅ | `academic-pipeline/` | 核心 skill 內容，可供閱讀 |
   | ✅ | `shared/` | 跨模型驗證、handoff schemas、共用 protocols |
   | ✅ | `scripts/` | `literature_corpus[]` adapters（`folder_scan`、`zotero`、`obsidian`）與 schema validators；Material Passport corpus mode 與 CI-style validation 需要 |
   | ✅ | `MODE_REGISTRY.md` | Mode definitions |
   | Optional | `.claude/` | Project-level routing rules。若你在下方步驟 5 設定 Project Instructions，建議跳過；只有在你偏好把 routing rules 作為 Project files 顯示時才納入。 |
   | Optional | `examples/` | 可作為參考範例；若想縮小 Project 知識庫，請跳過 |
   | Optional | `.github/`、READMEs、LICENSE 等 | Repository metadata；核心閱讀 context 不需要 |

5. （建議）將 `.claude/CLAUDE.md` 的內容設為 Project 的 **Instructions**，以獲得更好的 routing。
6. 開始對話："Guide my research on X" 或 "Help me write a paper about Y"。

Anthropic 目前的 [Project file limits](https://support.claude.com/en/articles/8241126-upload-files-to-claude) 說明：Project 並未刻意設定 200 檔上限，但每個檔案有 30 MB 大小限制，總可用內容仍受 runtime context-window 影響。請讓 Project 保持聚焦，Claude 才能穩定擷取相關檔案。

#### 方法 4a：Custom Skill upload（不推薦給本 suite）

方法 4a 是 claude.ai 標準的 Custom Skill 安裝路徑：把每個 skill 資料夾壓成 zip、透過 Settings → Capabilities → Skills 上傳，Claude 會把它當成已安裝的 Skill，提供自動載入與 routing。claude.ai Custom Skills 確實支援多檔 skill 套件，包含 `scripts/`（請見 Anthropic 的 [How to create custom Skills](https://support.claude.com/en/articles/12512198-how-to-create-custom-skills) 對 supporting files 與 code execution 的說明），所以方法 4a 在機制上是可以 host 帶可執行檔的 skill 的。但**不推薦給本 suite 使用**，原因如下，且兩者疊加：

1. **ARS 仰賴 Claude Code 專屬的編排功能**。每個 ARS skill 透過 Claude Code 的 Task / subagent 工具驅動 12-13 個專責 agent，並透過 Material Passport 在跨 session 之間交接檔案。Anthropic 文件描述的 claude.ai Custom Skill runtime（每個 session 一個 containerised code-execution 環境，[Use Skills in Claude](https://support.claude.com/en/articles/12512180-use-skills-in-claude) 說明 skill 啟動，但沒提到 multi-agent dispatch）並不包含 Claude Code 的 Task / subagent 控制面。可預期方法 4a 會把 ARS 呈現為 SKILL.md body 的 instructions，但缺少實際產出 suite 結果的 multi-agent dispatch。我們未實際 live upload 量測這項；本建議是基於 ARS agent 編排對 Claude Code 的依賴推論而成，並非實測失敗。
2. **會降低 Claude Code 與 Cowork 的 routing 精度**。claude.ai 在 [Custom Skills 文件](https://claude.com/docs/skills/how-to) 把每個 skill 的 `description` 限制在 200 字元，但 [Agent Skills specification](https://agentskills.io/specification) 與 [Claude Code Skills 文件](https://code.claude.com/docs/en/skills) 都允許到 1,024 字元。本 suite 四個 description 目前在 440-842 字元區間，前段 front-load 了 Claude Code 與 Cowork 用來區分研究、寫作、審查、orchestration 的 routing 關鍵字。為了 fit 方法 4a 而砍 description，會削弱 ARS 實際運作平台（Claude Code 與 Cowork）上的 routing，換到的只是 claude.ai 上未經實測的部分相容。

**建議的替代路徑：**

- 桌面端做 agentic skill execution，請用方法 3（Cowork）。四個 skill 都會在 Cowork 註冊為 capabilities，多 agent 協作完整保留。
- claude.ai 網頁端要存取 repo 內容，請用方法 4b（Project + GitHub integration，本節稍前說明）。Claude 可以讀取 skill 主體、references 與範例，你可以在 claude.ai 一般對話中提問或起草。
- Claude Code 專案請用方法 1（project skills）或方法 2（standalone）。

如果你看完上述限制後仍想試方法 4a，每個 zip 都必須把 skill 資料夾放在最上層，所以 zip 內容應包含 `<skill-name>/SKILL.md`，而不是 `<skill-name>/<skill-name>/SKILL.md`（多包一層會把 discovery 檔案藏到下一層）。下面的 `zip -r` 指令會產出正確的 zip 結構：

```bash
git clone https://github.com/Imbad0202/academic-research-skills.git
cd academic-research-skills

zip -r deep-research.zip deep-research
zip -r academic-paper.zip academic-paper
zip -r academic-paper-reviewer.zip academic-paper-reviewer
zip -r academic-pipeline.zip academic-pipeline
```

接著在 claude.ai：

1. 登入 [claude.ai](https://claude.ai)。
2. 開啟 **Settings**。
3. 開啟 **Capabilities**。
4. 開啟 **Skills**。
5. 上傳 `deep-research.zip`。
6. 上傳 `academic-paper.zip`。
7. 上傳 `academic-paper-reviewer.zip`。
8. 上傳 `academic-pipeline.zip`。

每個 zip 都會被 upload UI 以 description 過長拒絕，因為 ARS 所有 description 都超過 claude.ai 200 字元上限。Description 維持原狀並非疏忽，原因見上方說明。

**claude.ai 與 Claude Code 的差異：**

- 方法 4b 用於內容閱讀，不是主動 Skill execution。若需要 agentic skill execution，請優先使用方法一、方法二、方法三。
- claude.ai 不支援本機 shell commands；結果可能不如依賴本機 scripts 的 Claude Code workflows 完整。
- 跨模型驗證（`ARS_CROSS_MODEL`）需要 Claude Code 與 API keys。
- 直接產出 `.docx` 需要 Pandoc，LaTeX/PDF 輸出需要 Claude Code 搭配 `tectonic`；claude.ai 仍可產出 Markdown 與 DOCX 轉換說明。
### 方法五：Claude Science 匯入（v3.14.0+）

Claude Science 可直接從 GitHub 匯入四個 ARS skill：

1. 開啟 **Customize → Capabilities → Skills → Import from GitHub**。
2. 貼上 `https://github.com/Imbad0202/academic-research-skills`，按 **Preview**。
3. 四個 skill（`academic-paper`、`academic-paper-reviewer`、`academic-pipeline`、`deep-research`）全部出現——按 **Import 4 skills**。

**注意事項：**

- 需要 repo 狀態為 v3.14.0+——匯入器讀取 `.claude-plugin/marketplace.json` 中明列的 skill 路徑。更早的 tag 只透過 symlink 的 `skills/` 目錄暴露 skill，GitHub-API 匯入器無法穿越（會回報「no skills/ dirs with SKILL.md」）。
- 匯入是**單次快照**：Claude Science 不會追蹤 repo。ARS 發版後需重新匯入才能取得更新。
- **會轉移的**：方法論層——各 skill 的 `SKILL.md` 與其協定（研究／寫作／審查），Claude Science 的 agent 會在相關時讀取。
- **不會轉移的**：Claude Code 專屬機制——`/ars-*` slash commands、hooks（含 write-scope guard）、跨模型驗證 scripts、Task-tool subagent 編排。Claude Science 有自己的 specialist agent 系統與內建引用查核 reviewer；把 Claude Science 上的執行視為「ARS 方法論 + Claude Science 自家機制」，而非 1:1 的 pipeline 移植。
