# ARS Setup

Prerequisites and optional setup for Academic Research Skills. If you only need Markdown output and the default Claude pipeline (the inherited session model), you can skip most of this — see "Minimum viable setup" below.

---

## Minimum viable setup

1. Install Claude Code (see below).
2. Export `ANTHROPIC_API_KEY`.
3. `claude` in this repo (or any project that has ARS in `.claude/skills/`).

That is enough for Markdown output + DOCX conversion instructions. Everything else in this document is optional.

---

## Install Claude Code

**Recommended: Native installer** (no Node.js required, auto-updates):

```bash
# macOS / Linux
curl -fsSL https://claude.ai/install.sh | bash

# Windows (PowerShell)
irm https://claude.ai/install.ps1 | iex
```

<details>
<summary>Alternative: npm install (deprecated)</summary>

Requires Node.js 18+.

```bash
npm install -g @anthropic-ai/claude-code
```

</details>

## Set up API key

Get an Anthropic API key at <https://console.anthropic.com/>.

```bash
# Claude Code will prompt for your API key on first run
claude
```

Or set it as an environment variable:

```bash
export ANTHROPIC_API_KEY=sk-ant-xxxxx
```

## DOCX output (optional)

Direct `.docx` generation uses [Pandoc](https://pandoc.org/). If Pandoc is unavailable, the formatter falls back to Markdown + DOCX conversion instructions.

```bash
# macOS
brew install pandoc

# Linux (Debian/Ubuntu)
sudo apt-get install pandoc

# Windows — download from https://pandoc.org/installing.html
```

## LaTeX / PDF output (optional)

PDF output requires [tectonic](https://tectonic-typesetting.github.io/) and specific fonts. **This is optional** — Markdown output and DOCX conversion instructions work without any of this.

```bash
# macOS
brew install tectonic

# Linux (Debian/Ubuntu)
curl --proto '=https' --tlsv1.2 -fsSL https://drop-sh.fullyjustified.net | sh

# Windows — download from https://tectonic-typesetting.github.io/en-US/install.html
```

**Required fonts** (for APA 7.0 CJK output):

- **Times New Roman** — usually pre-installed on macOS/Windows; on Linux install `ttf-mscorefonts-installer`
- **Source Han Serif TC VF** (思源宋體) — download from [Google Fonts](https://fonts.google.com/specimen/Noto+Serif+TC) or [Adobe GitHub](https://github.com/adobe-fonts/source-han-serif)
- **Courier New** — usually pre-installed

> If you only need Markdown output or DOCX conversion instructions, skip this entirely. Direct `.docx` generation requires Pandoc, and PDF generation requires `tectonic`.

---

## Material Passport `literature_corpus[]` adapters (v3.6.4+, optional)

If you maintain a curated literature corpus (Zotero, Obsidian, a folder of PDFs, etc.), you can pre-load it into a Material Passport so Phase 1 ARS agents read your library *before* searching external databases. This is opt-in and presence-based — when no corpus is supplied, ARS runs the external-DB-only flow unchanged.

Three reference Python adapters ship with v3.6.4 at `scripts/adapters/`:

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

Each adapter emits two files: `passport.yaml` (Schema 9 with `literature_corpus[]` populated) and `rejection_log.yaml` (always emitted, empty when no rejections — closed enum of categorical reasons). Users with non-reference corpus sources are expected to write their own adapters following [`academic-pipeline/references/adapters/overview.md`](../academic-pipeline/references/adapters/overview.md).

v3.6.5 wires `bibliography_agent` (deep-research, Phase 1) and `literature_strategist_agent` (academic-paper, Phase 1) as the consumers — both run the corpus-first / search-fills-gap flow when a non-empty corpus is present and parses cleanly. See [`academic-pipeline/references/literature_corpus_consumers.md`](../academic-pipeline/references/literature_corpus_consumers.md) for the consumer protocol.

## Optional environment flags (v3.5.1+)

ARS exposes a few opt-in flags. All default to OFF; setting them changes behaviour for the current session only.

| Flag | Since | What it does | Reference |
|---|---|---|---|
| `ARS_CROSS_MODEL` | v3.0 | Enable cross-model verification (see next section) | [§"Cross-model verification"](#cross-model-verification-optional) |
| `ARS_SOCRATIC_READING_PROBE=1` | v3.5.1 | Activate the Socratic reading-check probe layer in `socratic_mentor_agent`. Goal-oriented intent only; fires at most once per session when user has cited a specific paper; decline logged without penalty. | `deep-research/agents/socratic_mentor_agent.md` |
| `ARS_PASSPORT_RESET=1` | v3.6.3 | Promote every FULL checkpoint to a context-reset boundary. Required to *emit* boundary entries; **not** required to invoke `resume_from_passport=<hash>` in a fresh session. With the flag ON in `systematic-review` mode, reset is mandatory at every FULL checkpoint. | `academic-pipeline/references/passport_as_reset_boundary.md` |
| `ARS_CROSS_MODEL_SAMPLE_INTERVAL` | v3.5.0 | Sampling interval for cross-model integrity checks (advisory) | `shared/cross_model_verification.md` |
| `ARS_VERIFICATION_CACHE_PATH` | v3.11 | Override the citation-verification cache location (see below). Not an on/off flag — the cache is on by default; this only relocates it. | `scripts/verification_cache.py` |
| `ARS_MODEL_TIERING` | Unreleased (#517) | Opt-in model tiering: `economy` (frontier session — execution-type agents step down one tier, floor Opus-class) or `quality-boost` (below-frontier session — judgment-type agents jump up to the frontier tier at the checkpoint surfaces: Stage 2.5/4.5 gates, the opt-in Stage 4→5 claim–ref audit, and final review). Unset = session model everywhere; unknown values warn once and behave as unset. | `shared/model_tiering.md` |

---

## Citation verification cache (v3.11, #182)

The deterministic citation-existence gate (#182) cross-checks each reference against Semantic Scholar, OpenAlex, Crossref, and arXiv. To avoid re-querying the same paper across drafts, results are cached in a local SQLite store.

- **No setup required.** The cache is created automatically at `~/.cache/ars/verification.db` on first use; entries expire after 90 days. The arXiv resolver needs no API key.
- **Relocate it** by exporting `ARS_VERIFICATION_CACHE_PATH=/your/path.db` (e.g. to share one cache across projects, or to keep it on a faster disk).
- **Invalidate one citation** with `/ars-cache-invalidate <citation_key>` — removes every cached row for that key (all four resolvers, all query forms); idempotent no-op if nothing is cached.

The cache is single-process (SQLite WAL); concurrent multi-user access to one cache file is out of scope.

---

## Cross-model verification (optional)

ARS works with the inherited Claude session model alone. For higher confidence, you can optionally enable a second AI model to independently verify integrity checks and challenge the devil's advocate.

### Quick setup

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

### What changes when enabled

| Feature | Without cross-model | With cross-model |
|---|---|---|
| Integrity verification | Single-model 100% check | + risk-stratified verification by 2nd model: 100% of high-impact references (final gate adds 100% of new/changed-claim references) + a sampled remainder |
| Devil's Advocate | Single-model DA | + Cross-model generates independent critique, novel findings added |
| Peer Review | 5 reviewers (same model) | Same 5 reviewers + cross-model DA critique/calibration support |
| Irreversible checkpoints | Single-model decision | + Blind cross-model decision at design freeze + final editorial decision; divergence escalated to you, never averaged |

### Cost

Full pipeline adds ~$0.60-1.10 in cross-model API costs (order-of-magnitude; measured at GPT-5.4 Pro pricing). See [`shared/cross_model_verification.md`](../shared/cross_model_verification.md) for the current model lineup and detailed breakdown.

### No API key? No problem

Without `ARS_CROSS_MODEL` set, everything works exactly as before. The cross-model features are invisible and add zero overhead.

---

## Installation methods

Claude discovers skills at `<install-root>/<skill-name>/SKILL.md`. This repo contains four separate skills, each with its own `SKILL.md`:

- `deep-research`
- `academic-paper`
- `academic-paper-reviewer`
- `academic-pipeline`

Do not install the whole repository as one nested skill folder under `.claude/skills/academic-research-skills/`; that buries the four `SKILL.md` files one level too deep for discovery. See Anthropic's [Claude Code Skills documentation](https://code.claude.com/docs/en/skills).

### Method 0: Claude Code Plugin (v3.7.0+, recommended for Claude Code CLI / IDE users)

If you use Claude Code CLI, VS Code extension, or JetBrains extension, install ARS as a plugin:

```text
/plugin marketplace add Imbad0202/academic-research-skills
/plugin install academic-research-skills
```

The four skills (`deep-research`, `academic-paper`, `academic-paper-reviewer`, `academic-pipeline`) are auto-discovered from the plugin's `skills/` directory.

**Strongly recommended: open auto-update.** Open the `/plugin` UI, find `academic-research-skills`, and toggle auto-update on. ARS releases roughly every 1–2 weeks; auto-update keeps you in sync without manual refreshes. To refresh manually: `/plugin update academic-research-skills`. (`/plugin marketplace update academic-research-skills` only refreshes the marketplace source list, not the installed plugin itself.)

**Plugin platform scope:**
- ✅ Claude Code CLI / VS Code extension / JetBrains extension — full support
- ❌ claude.ai web / Claude for Work / Anthropic API direct calls — plugins not supported; use Method 1 / 2 / 3 below
- ➡️ Codex CLI — install the sibling distribution [`Imbad0202/academic-research-skills-codex`](https://github.com/Imbad0202/academic-research-skills-codex) (same workflow content, Codex-native packaging)

### Method 1: As project skills (recommended)

Use this when you want ARS available inside an existing Claude Code project.

Clone the repo to a stable local path, then copy each skill folder into your project's `.claude/skills/` directory:

```bash
git clone https://github.com/Imbad0202/academic-research-skills.git ~/academic-research-skills

cd /path/to/your/project
mkdir -p .claude/skills
cp -R ~/academic-research-skills/deep-research .claude/skills/deep-research
cp -R ~/academic-research-skills/academic-paper .claude/skills/academic-paper
cp -R ~/academic-research-skills/academic-paper-reviewer .claude/skills/academic-paper-reviewer
cp -R ~/academic-research-skills/academic-pipeline .claude/skills/academic-pipeline
```

Expected path shape:

```text
/path/to/your/project/.claude/skills/deep-research/SKILL.md
/path/to/your/project/.claude/skills/academic-paper/SKILL.md
/path/to/your/project/.claude/skills/academic-paper-reviewer/SKILL.md
/path/to/your/project/.claude/skills/academic-pipeline/SKILL.md
```

Then copy the `.claude/CLAUDE.md` content into your project's `.claude/CLAUDE.md` (merge with existing if you have one).

> **Global Claude Code installation:** To make these skills available across your Claude Code projects, install the four folders to `~/.claude/skills/` instead:
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

### Method 2: As a standalone project

Use this when you want to work directly inside the ARS repository.

```bash
git clone https://github.com/Imbad0202/academic-research-skills.git
cd academic-research-skills
claude
```

<details>
<summary><strong>No Git?</strong> Download as ZIP instead</summary>

1. Go to <https://github.com/Imbad0202/academic-research-skills>
2. Click the green **Code** button → **Download ZIP**
3. Extract the ZIP to your desired location
4. For Method 1: copy the four extracted skill folders (`deep-research`, `academic-paper`, `academic-paper-reviewer`, `academic-pipeline`) into `.claude/skills/` inside your project
5. For standalone use: open a terminal in the extracted folder and run `claude`

</details>

### Method 3: Claude Cowork (desktop)

Use this when you want the four ARS skills available in [Claude Cowork](https://support.claude.com/en/articles/13345190-get-started-with-claude-cowork), Claude Desktop's agentic workspace.

> **Cowork does not read `~/.claude/skills/`.** That directory belongs to Claude Code (the CLI / IDE), and Cowork does not scan it. Cowork loads skills you upload through **Settings → Capabilities → Skills**, each as its own zip. Symlinking or copying the skill folders into `~/.claude/skills/` will not make them appear in Cowork, no matter how many times you restart.

#### Prerequisites

- Claude Desktop latest version on macOS or Windows. Download from Anthropic's [Claude Desktop page](https://claude.ai/download).
- Active internet connection; Cowork tasks call the Anthropic API.
- Keep Claude Desktop open while Cowork tasks run. Cowork runs inside the Desktop process.
- A paid plan with Cowork access. See Anthropic's [Cowork requirements](https://support.claude.com/en/articles/13345190-get-started-with-claude-cowork) for current plan availability.
- **Code execution / file creation must be enabled** in **Settings → Capabilities**, or the Skills section will not appear. See Anthropic's [Use Skills in Claude](https://support.claude.com/en/articles/12512180-use-skills-in-claude).
- On Team or Enterprise plans, your organization admin may have disabled Skills. If the Skills section is missing after enabling code execution, ask your admin to check org-level controls.

#### Step 1: Build one zip per skill

Clone the repo, then zip each of the four skill folders individually so that each zip has its own `SKILL.md` at the top level (not nested under an extra folder). The `-x "*.DS_Store"` flag keeps macOS metadata out of the archive.

```bash
git clone https://github.com/Imbad0202/academic-research-skills.git
cd academic-research-skills

for s in deep-research academic-paper academic-paper-reviewer academic-pipeline; do
  (cd "$s" && zip -r "../$s.zip" . -x "*.DS_Store")
done
```

This produces four zips in the repo root: `deep-research.zip`, `academic-paper.zip`, `academic-paper-reviewer.zip`, `academic-pipeline.zip`. Each zip's top level looks like:

```text
SKILL.md
agents/
examples/
references/
templates/
```

#### Step 2: Upload each zip

1. In Claude Desktop (or claude.ai — uploaded skills sync to the same account), go to **Settings → Capabilities → Skills**.
2. Use the **+** in the Skills panel to upload a skill, and select one of the four zips. Repeat for all four, one at a time.
3. Each skill then appears under **Personal skills**, already enabled, with **Trigger: Slash command + auto**. Re-uploading a skill with the same name replaces the existing one (useful when updating to a new ARS release).

Verified on Claude Desktop (June 2026): `deep-research.zip` built this way installs cleanly, the full skill description is preserved (no 200-character truncation), and `/deep-research` appears in the Cowork command palette.

#### Step 3: Use the skills in a Cowork Task

Type `/` in a Cowork Task to open the command palette and select a skill, or describe your intent in plain language (e.g. "do a deep literature review on X") and Cowork routes by the skill's `description`.

#### One trade-off versus Claude Code

Uploaded this way, each skill runs on its own as a standalone instruction set. This is a different experience from Claude Code. In Claude Code the four skills work as a coordinated team: `academic-pipeline` chains them (research → write → review → revise) and each skill drives its own group of sub-agents. Cowork's uploaded-skill runtime does not provide that sub-agent orchestration, so the individual skills respond, but the full end-to-end pipeline does not run the way it does in Claude Code. For the full orchestrated experience, install ARS in Claude Code via Method 0 (plugin) or Method 1 (project skills) above.

### Method 4: Use with claude.ai (web)

ARS is a Claude Code-native suite. The four skills are 12-13-agent teams that depend on multi-agent orchestration, executable scripts under `scripts/`, and Material Passport file handoffs. claude.ai's web interface delivers a different runtime than Claude Code, and the two access paths it offers reach this repository in different ways:

- **Method 4b — Project + GitHub integration** (recommended for claude.ai users): brings the repository into a claude.ai Project as retrievable knowledge. Claude can read the skill bodies, references, schemas, and example outputs, and answer questions or draft against them. Not a Skill install — auto-loading and skill routing do not happen, but the content is fully available for reading and citation.
- **Method 4a — Custom Skill upload**: claude.ai's standard Skill install path (Settings → Capabilities → Skills, one zip per skill). Not recommended for this suite — see the rationale below before using it.

#### Prerequisites

- A claude.ai account. Plan availability differs by sub-method (see below).
- **For Method 4b**: claude.ai Projects are available across plan tiers per Anthropic's [What are Projects?](https://support.claude.com/en/articles/9517075-what-are-projects); paid plans (Pro, Max, Team, Enterprise) get larger knowledge capacity and stronger retrieval. GitHub authentication is required through the Anthropic connector — see [Using the GitHub integration](https://support.claude.com/en/articles/10167454-using-the-github-integration) and [Set up Claude integrations](https://support.claude.com/en/articles/10168395-set-up-claude-integrations). Private repositories require the Anthropic GitHub App to be authorized on the repo or organization. Team and Enterprise plans require owner-level connector enablement before users can add GitHub-sourced files.
- **For Method 4a**: Custom Skills are available on Free, Pro, Max, Team, and Enterprise per Anthropic's [Use Skills in Claude](https://support.claude.com/en/articles/12512180-use-skills-in-claude). The same article notes that Skills require **code execution to be enabled** in Settings → Capabilities. No GitHub authentication is needed for Method 4a — you zip each skill folder locally and upload one zip per skill through Settings → Capabilities → Skills. Zip structure errors and the 200-character `description` cap surface as upload-time errors; see Anthropic's [Custom Skills packaging documentation](https://claude.com/docs/skills/how-to) and [How to create custom Skills](https://support.claude.com/en/articles/12512198-how-to-create-custom-skills).

#### Method 4b: Project + GitHub integration (recommended for claude.ai)

claude.ai Projects deliver content as static knowledge for Claude to retrieve and cite — see Anthropic's [What are Projects?](https://support.claude.com/en/articles/9517075-what-are-projects). This is NOT a Skill install. Skill auto-loading does not happen. Trigger phrases do not route. Claude can read the repo content for reading and citation, and answer questions about it, but does not execute the skills as agentic workflows.

Use this when you want claude.ai to have access to the repo content — including the agent definitions, references, and example outputs — for reading and citation, without needing agentic skill execution. For agentic execution, use Method 3 (Cowork) on the desktop, or Methods 1-2 in Claude Code.

1. Sign in to [claude.ai](https://claude.ai).
2. Create a new Project: **Projects** → **Create Project**.
3. Import from GitHub: in the Project, click **Files** → **+** → **GitHub** → select `Imbad0202/academic-research-skills`.
4. Select the folders/files below.

   | Select | Directory / file | Why |
   |---|---|---|
   | ✅ | `deep-research/` | Core skill content for reading |
   | ✅ | `academic-paper/` | Core skill content for reading |
   | ✅ | `academic-paper-reviewer/` | Core skill content for reading |
   | ✅ | `academic-pipeline/` | Core skill content for reading |
   | ✅ | `shared/` | Cross-model verification, handoff schemas, shared protocols |
   | ✅ | `scripts/` | `literature_corpus[]` adapters (`folder_scan`, `zotero`, `obsidian`) + schema validators; required for Material Passport corpus mode and CI-style validation |
   | ✅ | `MODE_REGISTRY.md` | Mode definitions |
   | Optional | `.claude/` | Project-level routing rules. Skip if you set Project Instructions in step 5 below (recommended path); include only if you prefer to keep routing rules visible as Project files. |
   | Optional | `examples/` | Useful for reference examples; skip if you want a smaller Project knowledge set |
   | Optional | `.github/`, READMEs, LICENSE, etc. | Repository metadata; not needed for core reading context |

5. (Recommended) Set **Instructions** in the Project to the content of `.claude/CLAUDE.md` for better routing.
6. Start chatting: "Guide my research on X" or "Help me write a paper about Y".

Anthropic's current [Project file limits](https://support.claude.com/en/articles/8241126-upload-files-to-claude) state that Project file count is not artificially capped at 200; files have a 30 MB per-file limit and total usable content is still subject to context-window limits at runtime. Keep the Project focused so Claude retrieves the relevant files reliably.

#### Method 4a: Custom Skill upload (not recommended for this suite)

Method 4a is claude.ai's standard Custom Skill install path: zip each skill folder, upload through Settings → Capabilities → Skills, and Claude treats it as an installed Skill with auto-loading and routing. claude.ai's Custom Skills do support multi-file skill packages including `scripts/` (see Anthropic's [How to create custom Skills](https://support.claude.com/en/articles/12512198-how-to-create-custom-skills) on supporting files and code execution), so Method 4a is mechanically capable of hosting skills with executable assets. The reasons not to recommend it for this specific suite are different and compound:

1. **ARS depends on Claude Code-only orchestration features**. Each ARS skill drives 12-13 specialised agents through Claude Code's Task / subagent tooling and Material Passport file handoffs that resume across sessions. The Anthropic-documented scope of claude.ai's Custom Skill runtime — a containerised code-execution environment per session, with the Skills user guide ([Use Skills in Claude](https://support.claude.com/en/articles/12512180-use-skills-in-claude)) describing skill activation but not multi-agent dispatch — does not include Claude Code's Task / subagent control surface. Method 4a is therefore expected to surface ARS as the SKILL.md body's instructions, without the multi-agent dispatch that produces the suite's actual outputs. We have not run a live upload to characterise this in detail; the recommendation is forward-looking based on the Claude Code-specific assumptions baked into the agent orchestration, not on a measured failure.
2. **Cost to Claude Code and Cowork routing**. claude.ai limits each skill's `description` field to 200 characters per the [Custom Skills documentation](https://claude.com/docs/skills/how-to), while the [Agent Skills specification](https://agentskills.io/specification) and [Claude Code Skills documentation](https://code.claude.com/docs/en/skills) allow up to 1,024 characters. The four ARS descriptions currently sit in the 440-842 range, front-loading routing keywords that Claude Code and Cowork use to discriminate between research, writing, review, and orchestration. Trimming them to fit Method 4a would weaken routing on Claude Code and Cowork — the platforms ARS was built for — in exchange for an unverified partial fit on claude.ai.

**Recommended paths instead:**

- For skill execution on the desktop, use [Method 3 (Cowork)](#method-3-claude-cowork-desktop). The four skills upload as standalone Cowork skills; the multi-agent pipeline orchestration is only available in Claude Code (Methods 0–2).
- For claude.ai web access to the repo content, use [Method 4b (Project + GitHub integration)](#method-4b-project--github-integration-recommended-for-claudeai). Claude reads the skill bodies, references, and examples, and you can ask questions or draft against them in a normal claude.ai chat.
- For Claude Code projects, use [Method 1 (project skills)](#method-1-as-project-skills-recommended) or [Method 2 (standalone)](#method-2-as-a-standalone-project).

If you still want to try Method 4a despite the limitations above, zip each skill folder so the archive's top-level entry is `<skill-name>/SKILL.md` (not `<skill-name>/<skill-name>/SKILL.md` — that nesting buries the discovery file one level too deep). The `zip -r` commands below produce that shape correctly:

```bash
git clone https://github.com/Imbad0202/academic-research-skills.git
cd academic-research-skills

zip -r deep-research.zip deep-research
zip -r academic-paper.zip academic-paper
zip -r academic-paper-reviewer.zip academic-paper-reviewer
zip -r academic-pipeline.zip academic-pipeline
```

Then in claude.ai:

1. Sign in to [claude.ai](https://claude.ai).
2. Open **Settings**.
3. Open **Capabilities**.
4. Open **Skills**.
5. Upload `deep-research.zip`.
6. Upload `academic-paper.zip`.
7. Upload `academic-paper-reviewer.zip`.
8. Upload `academic-pipeline.zip`.

The upload UI will reject each zip with a description-too-long error because every ARS description exceeds claude.ai's 200-character cap. The descriptions are intentionally not trimmed; see the rationale above.

**claude.ai vs Claude Code:**

- Method 4b is for content reading, not active Skill execution. For agentic skill execution, prefer Methods 1-3.
- claude.ai does not support local shell commands; results may be less comprehensive than Claude Code workflows that rely on local scripts.
- Cross-model verification (`ARS_CROSS_MODEL`) requires Claude Code with API keys.
- Direct `.docx` generation requires Pandoc, and LaTeX/PDF output requires Claude Code with `tectonic`; claude.ai can still produce Markdown and DOCX conversion instructions.
### Method 5: Claude Science import (v3.14.0+)

Claude Science imports the four ARS skills straight from GitHub:

1. Open **Customize → Capabilities → Skills → Import from GitHub**.
2. Paste `https://github.com/Imbad0202/academic-research-skills` and click **Preview**.
3. All four skills (`academic-paper`, `academic-paper-reviewer`, `academic-pipeline`, `deep-research`) appear — click **Import 4 skills**.

**Notes:**

- Requires repo state v3.14.0+ — the importer reads the explicit skill paths declared in `.claude-plugin/marketplace.json`. Earlier tags exposed skills only through the symlinked `skills/` directory, which GitHub-API importers cannot traverse (they report "no skills/ dirs with SKILL.md").
- Imports are **point-in-time snapshots**: Claude Science does not track the repo. Re-import after an ARS release to pick up changes.
- **What transfers:** the methodology layer — each skill's `SKILL.md` and its protocols (research / writing / review), which Claude Science's agent reads when relevant.
- **What does not transfer:** Claude Code-specific machinery — the `/ars-*` slash commands, hooks (including the write-scope guard), cross-model verification scripts, and Task-tool subagent orchestration. Claude Science runs its own specialist-agent system and a built-in citation-checking reviewer; treat a Claude Science run as "ARS methodology + Claude Science's own machinery", not a 1:1 pipeline port.
