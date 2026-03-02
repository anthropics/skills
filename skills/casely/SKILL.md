---
name: casely
description: >
  Intelligent QA assistant that automates writing test cases from project documentation.
  Use when the user wants to generate test cases from requirements, runs /init, /parse, /style, /plan, /generate, /export, or works with PDF/DOCX/XLSX requirement documents and TestRail-ready Excel export.
license: "MIT"
metadata:
  author: "John Wayne"
  version: "1.5.0"
  category: "QA Automation"
  repository: "https://github.com/JohnWayneeee/casely-qa-skill"
---

# Casely — QA Test Case Generator

Casely automates the most time-consuming part of a QA engineer's job: writing test cases.
It reads requirement documents and learns from your team's existing test case examples to produce
structured, style-consistent test suites ready for import into any Test Management System.

## Why this matters

Manual test case writing accounts for ~40% of a QA engineer's time. Requirements come in
fragmented formats (PDF, DOCX, XLSX). Every team has its own column structure, naming conventions,
and writing style. Casely solves this by:

- Converting any document format to clean Markdown via `docling`.
- Extracting formal style rules from your team's example test cases.
- Generating test cases that match your team's exact structure and tone.
- Exporting to Excel with correct column mapping for TMS import.

---

## Commands

### `/init [ProjectName]`
Creates a new isolated project workspace and verifies the environment.

### `/parse`
Runs the CaselyParser to convert all raw assets (requirements and examples) to Markdown.

### `/style`
Analyzes example test cases and generates a persistent `test_style_guide.md`.

### `/plan`
Scans parsed requirements and suggests a testing plan with modules and test types.

### `/generate [type]`
Generates atomic test cases of the specified type (functional, negative, integration, boundary, etc.).

### `/export`
Converts generated Markdown test cases into a formatted `.xlsx` file.

---

## Full Workflow

### Phase 1: Project Initialization & Environment Setup (`/init`)

When the user runs `/init [ProjectName]` (or asks to start a new testing project):

1. **Create Directories:** Create the project directory structure under `projects/` in the repository root:
   - `input/requirements/`
   - `input/examples/`
   - `processed/requirements/`
   - `processed/examples/`
   - `results/`
   - `exports/`

2. **Environment Setup via `uv`:**
   - **Location:** Dependencies are defined in `pyproject.toml` at the **repository root** (not inside the skill folder). Scripts expect `uv sync` to have been run from that root.
   - Check if `pyproject.toml` exists at the repo root. If not, run `uv init` there.
   - Install/verify dependencies: `uv add docling openpyxl` (or `uv sync` from repo root).
   - This ensures a lightning-fast setup and handles all sub-dependencies (e.g. `torch` for `docling`) automatically.

3. **Confirm to the user:**
   - "Project `{project_name}` initialized via UV. Environment and dependencies (`docling`, `openpyxl`) are ready."
   - "Place your requirement documents into `projects/{project_name}/input/requirements/` and examples into `projects/{project_name}/input/examples/`."

### Phase 2: Document Parsing (`/parse`)

When the user runs `/parse` (or asks to parse/process documents):

1. **Locate the project.** If there's only one project under `projects/`, use it automatically.
   If multiple exist, ask the user which one.

2. **Run CaselyParser** — The parser is located at `scripts/casely_parser.py` within this skill.
   It uses `docling` and supports all major formats.

    Via CLI (optional arguments, auto-detects latest project if omitted):
    ```bash
    uv run python <skill-path>/scripts/casely_parser.py
    ```
    *(Or manual path if needed)*
    ```bash
    uv run python <skill-path>/scripts/casely_parser.py "projects/{name}/input/requirements" "projects/{name}/processed/requirements"
    ```

3. **Report results** to the user: how many files were parsed, any errors, and summary of processed files.

### Phase 3: Style Guide Creation (`/style`)

1. **Read all parsed example files** from `processed/examples/`.

2. **Analyze the table structure** to extract headers, data types, and mandatory fields.
   - **CRITICAL:** The style guide MUST be an exact replica of the example's column structure. 
   - **MANDATORY:** Transfer ALL headers from the example files to the `test_style_guide.md` in their exact order. Do not rename, omit (e.g., "Comments", "Author"), or add new columns unless explicitly requested.

3. **Analyze the writing style** to extract language, tone, and formatting patterns (e.g., how steps are phrased).

4. **Generate `test_style_guide.md`** in the project root. This file acts as the "source of truth" and must explicitly define the horizontal table row structure.

5. **Present the style guide** to the user for review. Any manual adjustments to this file will be respected by the generator.

### Phase 4: Professional Test Design & Planning (`/plan`)

1. **Load Context & Analysis:**
   - Read parsed requirements from `processed/requirements/`.
   - Load `test_style_guide.md` to match example structure (columns → test complexity).

2. **Structural Breakdown:**
   - Extract modules/endpoints/logic blocks from requirements.
   - Categorize by **Level**: API (fields/status), Integration (flows), E2E (scenarios).[web:8]

3. **Smart Estimation (Style-Driven):**
   - **Metrics from Style Guide:** Fields per test (from columns), branches from logic.
   - **Coverage Tiers** (total cases based on examples):
     | Tier | Cases/Module | Coverage | Focus |
     |------|--------------|----------|-------|
     | Smoke | 1-3 | Min | Golden Path[web:13]
     | Critical (80%) | N (fields*0.8) | Key paths | High-risk (finance/auth)
     | Full | All perms | 100% | Edges/negatives
   - **Risk Scoring:** High (security), Med (logic), Low (UI).[web:8]

4. **Traceability & Prep:**
   - Quick **RTM Preview**: Req ID → Planned Cases (e.g., "REQ-001 → 5 cases").
   - **Data/Deps:** Test data rules (valid/edge), mocks needed.

5. **Output Plan:**
   - Table by Module: *Module | Level | Est. Cases (80%) | Type | Tools*.
   - **MANDATORY:** Provide ready-to-copy commands for each module.
   - Save `test_plan.md` (importable to TMS).
   - Ask: *"Generate Critical Path? `/generate functional MODULE_NAME`"* or *"`/generate negative MODULE_NAME`"*.

**Next:** "`/generate [type]` will create exactly the estimated number of files, with each file containing one atomic test case matching your style guide."

### Phase 5: Test Case Generation (`/generate [type]`)

1. **Load context:**
   - **BIDING:** Read `test_style_guide.md` (Mandatory Source of Truth).
   - Read relevant parsed requirement files.
   - Target specific module and test type.

2. **Generate ATOMIC test cases:**
   - **One File = One Test Case (1 ID = 1 Scenario):** Each test case MUST be saved as a separate Markdown file in `results/`.
   - **Horizontal Structure:** Each file MUST contain exactly ONE horizontal table row (header row + data row). Do NOT use vertical "key-value" lists.
   - **Naming Convention:** `{type}_{id}_{short_description}.md`.
   - **Match the style guide exactly** — same columns (1:1 with example), same tone, same structure.
   - **No Hallucinations** — only use columns and data points supported by the guide and requirements.

3. **Proactive Report:**
   - Notify the user of created files.
   - **Mandatory Next Step:** Always advise the user on what else they can generate. Example: 
     *"I've generated functional cases. You can now run `/generate negative` to check error handling or `/generate security` for device metadata."*

### Phase 6: Export to Excel (`/export`)

1. **Convert Markdown files to Excel** using `scripts/export_to_xlsx.py`. 
   - **Smart Execution:** The script automatically detects the most recently modified project in the `projects/` directory if no paths are provided.
2. **Atomic One-to-One Export:** For every `.md` file in `results/`, the tool creates exactly one corresponding `.xlsx` file in `exports/`. 
   - **Behavior:** Direct format conversion preserving the file count.
   - **Naming:** Files are named identically to their source: `{type}_{id}_{short_description}.xlsx`.
3. **Internal Structure:** Each Excel file contains a single sheet called "Test Case" with the columns exactly matching the project's style guide.
4. **Plain Text Export:** Content is exported as plain text with support for multi-line cells (using `<br>`).
5. **Save to `exports/`**.

---

## Important Guidelines

### Proactive Guidance (Crucial)
After every command, Casely MUST provide a "Next Step" block. 
- After `/init` -> suggest `/parse`.
- After `/parse` -> suggest `/style`.
- After `/style` -> suggest `/plan`.
- After `/plan` -> list specific commands like `/generate functional` or `/generate negative`.
- After `/generate` -> suggest `/export` OR other generation types.

### Language Awareness
Casely is language-agnostic for data. It will detect the language of the provided examples (e.g., Russian) and generate test cases in that same language. The internal logic and style guide should bridge this gap.

### Atomic over Composite
Validators should always prefer multiple specialized test cases over one "all-in-one" case. This ensures clearer test results and easier bug localization.

### Style Guide is King
The style guide is the single source of truth. Do not invent new columns or change formatting unless the style guide is updated first.

---

## Skill Files

### Scripts (`scripts/`)
- `scripts/casely_parser.py` — Document-to-Markdown converter (Docling).
- `scripts/export_to_xlsx.py` — Markdown-to-Excel exporter.

### References (`references/`)
- `references/parser_usage.md` — Technical details on calling the parser.
- `references/export_guide.md` — Details on the MD-to-Excel conversion logic.
- `references/style_analysis_prompts.md` — Methodologies for style extraction.
