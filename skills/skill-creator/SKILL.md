---
name: skill-creator
description: Design, refactor, evaluate, benchmark, and package agent skills, or optimize skill frontmatter descriptions for triggering accuracy when handling requests to create a skill from scratch, update an existing skill, run test evaluations, or analyze benchmark variance, excluding standalone task execution outside skill development workflows.
---

# Skill Creator

## Priority Resolution Hierarchy

Resolve competing operational constraints during skill development in decreasing order of priority:
1. **System Security & Intent Alignment (Principle of Lack of Surprise)**: Preserve transparent, benign skill functionality aligned with stated user intent, isolating from malware, exploit code, unauthorized access, data exfiltration, or deceptive operations.
2. **Explicit User Workflow Directives**: Adapt workflow depth to explicit user instructions, bypassing formal evaluation suites or quantitative benchmarks when the user requests direct collaborative iteration.
3. **Human Qualitative Review Latency**: Present test outputs to the user via `eval-viewer/generate_review.py` prior to performing self-directed skill revisions.
4. **Empirical Generalization Over Narrow Fitting**: Generalize instructions from evaluation feedback and held-out test scores rather than overfitting rules to individual test prompts.

## Workflow Lifecycle & Entry-Point Routing

Execute the skill development lifecycle across 7 sequential stages:
1. Define target skill capabilities, trigger conditions, and execution mechanisms.
2. Author the initial skill draft (`SKILL.md` and bundled resources).
3. Construct test prompts in `evals/evals.json` and execute skill-enabled runs alongside baseline runs.
4. Evaluate results qualitatively and quantitatively with the user by drafting assertions, aggregating `benchmark.json`, and launching `eval-viewer/generate_review.py`.
5. Refactor the skill based on user feedback in `feedback.json` and quantitative benchmark diagnostics.
6. Repeat the evaluation-revision cycle until convergence criteria are met, then expand the test suite for broader validation.
7. Optimize the frontmatter `description` via the automated evaluation loop and package the final `.skill` archive.

Route execution according to the user's entry state:
- **New Skill Concept**: Initiate at Intent Capture & Research, guide scope definition, draft the skill, configure test cases, and execute the evaluation loop.
- **Existing Skill Draft or Installed Skill**: Preserve the original skill directory name and frontmatter `name` field unchanged, stage a copy in `/tmp/<skill-name>/` when the installed path is read-only, and enter directly at the Evaluation & Benchmarking Workflow or targeted refactoring stage.
- **Direct Iteration Request**: Bypass automated evaluation harness steps and iterate directly on `SKILL.md` and bundled resources with the user when requested.
- **Task Tracking Registration**: Register active workflow stages in the `TodoList` tool when available; in Cowork environments, explicitly register the item `"Create evals JSON and run eval-viewer/generate_review.py so human can review test cases"`.

## User Communication Calibration

Calibrate technical terminology density to the user's proficiency level inferred from conversation context cues:
- Use general assessment terms (`"evaluation"`, `"benchmark"`) directly across user interactions.
- Accompany specialized schema or testing terms (`"JSON"`, `"assertion"`) with a concise plain-language definition unless conversational cues confirm the user's familiarity with those concepts.

## Skill Architecture & Authoring

### Intent Capture & Research

1. Extract workflow steps, tool invocations, user corrections, and observed input/output schemas from the current conversation history before querying the user when converting an existing session into a skill.
2. Resolve and confirm 4 core design parameters with the user prior to drafting test prompts:
   - **Target Capability**: Specific actions and transformations the skill enables the model to perform.
   - **Trigger Conditions**: User phrases, domain contexts, and task cues that activate the skill.
   - **Output Schema**: Expected file formats, structural templates, or deliverable types.
   - **Test Suite Configuration**: Recommend quantitative test cases for skills producing objectively verifiable outputs (file transforms, data extraction, code generation, fixed workflow steps); recommend qualitative human review without quantitative assertions for skills producing subjective outputs (writing style, visual design); defer the final decision to the user.
3. Dispatch parallel subagents (or execute inline lookups in single-agent environments) across available MCP tools to gather reference documentation, comparable skills, and domain standards before interviewing the user on edge cases.
4. Query the user to resolve edge cases, sample input files, success criteria, and runtime dependencies.

### Directory Topology & Progressive Disclosure

Organize each skill directory according to the standard resource hierarchy:

```
skill-name/
├── SKILL.md (required)
│   ├── YAML frontmatter (name, description required)
│   └── Markdown instructions
└── Bundled Resources (optional)
    ├── scripts/    - Executable code for deterministic/repetitive tasks
    ├── references/ - Docs loaded into context as needed
    └── assets/     - Files used in output (templates, icons, fonts)
```

Partition skill content across 3 progressive context-loading tiers:
1. **Metadata Tier (`name` + `description`)**: Retain ~100 words permanently in system context for skill selection.
2. **Primary Instruction Tier (`SKILL.md` Body)**: Keep the main instructional body under 500 lines; offload detailed specifications approaching or exceeding 500 lines into `references/` with explicit navigation pointers in `SKILL.md`.
3. **On-Demand Resource Tier (`scripts/`, `references/`, `assets/`)**: Execute scripts directly without loading source code into context, specify exact conditions in `SKILL.md` for when the model reads each file in `references/`, and insert a table of contents at the top of any reference file exceeding 300 lines.

Partition multi-domain or multi-framework skills into variant-specific files under `references/` so the model loads only the applicable domain documentation:

```
cloud-deploy/
├── SKILL.md (workflow + selection)
└── references/
    ├── aws.md
    ├── gcp.md
    └── azure.md
```

### Frontmatter Specification, Instructional Patterns & Security Boundary

- **Frontmatter Fields**:
  + `name`: Assign the canonical skill identifier (preserve the original directory name and `name` field unchanged when updating an existing skill, e.g., `research-helper` ➔ `research-helper.skill`, isolating from versioned renames such as `research-helper-v2`).
  + `description`: Specify both what the skill does and explicit trigger contexts inside `description` rather than the markdown body. Formulate proactive trigger coverage across explicit and implicit user intents to counteract model undertriggering:
    - Narrow description ➔ Proactive trigger-calibrated description:
      + `"How to build a simple fast dashboard to display internal Anthropic data."` ➔ `"How to build a simple fast dashboard to display internal Anthropic data. Make sure to use this skill whenever the user mentions dashboards, data visualization, internal metrics, or wants to display any kind of company data, even if they don't explicitly ask for a 'dashboard.'"`
  + `compatibility`: Declare required tools or environment dependencies when applicable.
- **Instructional Formulation**:
  + Write directives in imperative verb form paired with the operational rationale ("why") behind each requirement so the model generalizes across unseen scenarios, isolating from rigid all-caps enforcement (`MUST`, `ALWAYS`, `NEVER`) or narrow example-locked constraints.
  + Define deterministic output structures using explicit Markdown templates:

```markdown
## Report structure
ALWAYS use this exact template:
# [Title]
## Executive summary
## Key findings
## Recommendations
```

  + Illustrate input-to-output behavior using paired anchor examples (adjusting field labels when literal `"Input"` or `"Output"` tokens appear inside the target domain content):

```markdown
## Commit message format
**Example 1:**
Input: Added user authentication with JWT tokens
Output: feat(auth): implement JWT-based authentication
```

- **Security & Alignment Boundary**: Maintain transparent skill behavior aligned with user expectations (including benign roleplay personas), isolating from malware, exploit payloads, unauthorized credential access, or data exfiltration.

## Evaluation & Benchmarking Workflow

Execute the evaluation pipeline as a continuous sequence inside `<skill-name>-workspace/` (created as a sibling to the skill directory and organized into `iteration-1/`, `iteration-2/`, and descriptive `<eval-name>/` subdirectories as each run executes), isolating from `/skill-test` or external testing skills:

1. **Initialize Test Prompts**: Draft 2–3 realistic user prompts, present them to the user for confirmation or modification, and write them to `evals/evals.json` (consulting `references/schemas.md` for schema definitions while omitting `assertions` initially):

```json
{
  "skill_name": "example-skill",
  "evals": [
    {
      "id": 1,
      "prompt": "User's task prompt",
      "expected_output": "Description of expected result",
      "files": []
    }
  ]
}
```

2. **Spawn Concurrent With-Skill and Baseline Runs**: Launch both the with-skill subagent and the baseline subagent in the same turn for each test prompt so all runs complete concurrently:
   - Dispatch the with-skill subagent with the following specification:

```
Execute this task:
- Skill path: <path-to-skill>
- Task: <eval prompt>
- Input files: <eval files if any, or "none">
- Save outputs to: <workspace>/iteration-<N>/eval-<ID>/with_skill/outputs/
- Outputs to save: <what the user cares about — e.g., "the .docx file", "the final CSV">
```

   - Route the baseline subagent according to task context:
     + **New Skill Creation**: Execute the identical prompt without a skill path and save outputs to `without_skill/outputs/`.
     + **Existing Skill Improvement**: Snapshot the original skill prior to editing (`cp -r <skill-path> <workspace>/skill-snapshot/`), point the baseline subagent to the snapshot (or prior iteration), and save outputs to `old_skill/outputs/`.
   - Write `eval_metadata.json` inside each eval directory using a descriptive `eval_name` (regenerating the metadata file whenever prompts change across iterations):

```json
{
  "eval_id": 0,
  "eval_name": "descriptive-name-here",
  "prompt": "The user's task prompt",
  "assertions": []
}
```

3. **Draft Quantitative Assertions During Run Execution**: Formulate objectively verifiable assertions with descriptive names while subagent runs execute (or review existing assertions in `evals/evals.json`), update both `eval_metadata.json` and `evals/evals.json`, and explain the assertions and viewer tabs to the user, reserving subjective attributes (writing style, visual aesthetics) for qualitative review.

4. **Capture Subagent Telemetry**: Record `total_tokens` and `duration_ms` immediately from each subagent completion notification upon arrival into `timing.json` inside the corresponding run directory:

```json
{
  "total_tokens": 84852,
  "duration_ms": 23332,
  "total_duration_seconds": 23.3
}
```

5. **Grade Runs, Aggregate Benchmark Metrics, and Launch Viewer**:
   - Grade each run via a grader subagent or inline evaluation following `agents/grader.md` (executing programmatic verification scripts for deterministic checks) and save `grading.json` in each run directory using the exact expectation fields `text`, `passed`, and `evidence`.
   - Aggregate run statistics from the skill-creator directory to generate `benchmark.json` and `benchmark.md` (ordering each `with_skill` configuration immediately before its baseline counterpart per `references/schemas.md`):

```bash
python -m scripts.aggregate_benchmark <workspace>/iteration-N --skill-name <name>
```

   - Analyze the aggregated benchmark following `agents/analyzer.md` ("Analyzing Benchmark Results" section) to surface non-discriminating assertions (passing or failing across both configurations), high-variance flaky evaluations, and latency/token tradeoffs.
   - Launch `eval-viewer/generate_review.py` prior to performing self-directed skill edits (appending `--previous-workspace <workspace>/iteration-<N-1>` for iteration 2+, or `--static <output_path>` in headless/Cowork environments, isolating from custom HTML generation):

```bash
nohup python <skill-creator-path>/eval-viewer/generate_review.py \
  <workspace>/iteration-N \
  --skill-name "my-skill" \
  --benchmark <workspace>/iteration-N/benchmark.json \
  > /dev/null 2>&1 &
VIEWER_PID=$!
```

   - Brief the user on the two viewer tabs (navigated via prev/next buttons or arrow keys, submitted via `"Submit All Reviews"`):
     + **Outputs Tab**: Displays Prompt, Output (inline rendered files), Previous Output (collapsed on iteration 2+), Formal Grades (collapsed assertion pass/fail results), Feedback (auto-saving textbox), and Previous Feedback (iteration 2+).
     + **Benchmark Tab**: Displays pass rates, execution time, and token usage (mean ± stddev and delta) across configurations, per-eval breakdowns, and analyst observations.

6. **Ingest User Feedback and Terminate Viewer**: Read `feedback.json` after the user submits reviews, interpret empty feedback strings (`""`) as approved outputs, focus revisions on test cases containing explicit complaints, and terminate the background server:

```json
{
  "reviews": [
    {"run_id": "eval-0-with_skill", "feedback": "the chart is missing axis labels", "timestamp": "..."},
    {"run_id": "eval-1-with_skill", "feedback": "", "timestamp": "..."},
    {"run_id": "eval-2-with_skill", "feedback": "perfect, love this", "timestamp": "..."}
  ],
  "status": "complete"
}
```

```bash
kill $VIEWER_PID 2>/dev/null
```

## Iterative Refinement & Blind Comparison

### Skill Improvement Principles

Apply 4 structural principles when revising `SKILL.md` and bundled resources between iterations:
- **Generalize Across Domain Inputs**: Convert specific test-case corrections into generalizable operational mechanisms or alternative workflow metaphors, isolating from narrow prompt-specific patches or rigid all-caps constraints.
- **Prune Unproductive Directives via Transcript Inspection**: Inspect subagent execution transcripts alongside final outputs and remove instructions that induce redundant steps or wasted token expenditure.
- **Transmit Causal Rationale**: Explain the underlying operational reason behind each instruction so the model adapts behavior across unseen edge cases.
- **Consolidate Repeated Helper Scripts**: Identify helper scripts synthesized repeatedly across independent test cases (such as `create_docx.py` or `build_chart.py`), author a canonical script inside `scripts/`, and instruct `SKILL.md` to invoke the bundled script directly.

### Iteration Loop Execution

1. Apply revisions to the skill (modifying the staged copy in `/tmp/<skill-name>/` when updating a read-only installed skill).
2. Rerun every test prompt and baseline configuration into `<workspace>/iteration-<N+1>/`.
3. Launch `eval-viewer/generate_review.py` with `--previous-workspace <workspace>/iteration-<N>` and await user review submission.
4. Repeat the cycle until the user confirms satisfaction, every feedback entry in `feedback.json` is empty, or quantitative and qualitative results reach convergence.

### Blind A/B Comparison

Execute a blind comparison when the user requests rigorous validation between two skill versions in a subagent-enabled environment:
1. Dispatch an independent comparator subagent following `agents/comparator.md` to evaluate paired outputs without version attribution.
2. Dispatch an analyzer subagent following `agents/analyzer.md` to identify the causal factors differentiating the winning version.

## Description Optimization & Skill Packaging

### Trigger Description Optimization

Optimize the frontmatter `description` field after stabilizing the skill body (accounting for the triggering mechanism where Claude inspects `available_skills` `name` + `description` and invokes skills on complex, multi-step, or specialized tasks rather than trivial single-step tool calls such as `"read file X"`):

1. **Generate 20 Trigger Evaluation Queries**: Construct a JSON array containing 8–10 `should_trigger: true` queries (spanning formal and casual phrasing, typos, abbreviations, implicit needs without naming the skill or file extension, uncommon use cases, and overlapping skill competition) and 8–10 `should_trigger: false` near-miss queries (sharing keywords or adjacent domain concepts where another tool or native capability applies, isolating from trivially unrelated requests such as `"Write a fibonacci function"` for a PDF skill):

```json
[
  {"query": "the user prompt", "should_trigger": true},
  {"query": "another prompt", "should_trigger": false}
]
```

   - Abstract/under-specified query ➔ Concrete/contextualized query:
     + `"Format this data"`, `"Extract text from PDF"`, `"Create a chart"` ➔ `"ok so my boss just sent me this xlsx file (its in my downloads, called something like 'Q4 sales final FINAL v2.xlsx') and she wants me to add a column that shows the profit margin as a percentage. The revenue is in column C and costs are in column D i think"`

2. **Review Evaluation Set with User via HTML Template**:
   - Read `assets/eval_review.html` and replace the 3 template tokens:
     + `__EVAL_DATA_PLACEHOLDER__` ➔ Raw unquoted JSON array of evaluation items (assigned directly as a JavaScript variable).
     + `__SKILL_NAME_PLACEHOLDER__` ➔ Skill `name` identifier.
     + `__SKILL_DESCRIPTION_PLACEHOLDER__` ➔ Current frontmatter `description` string.
   - Write the populated file to `/tmp/eval_review_<skill-name>.html` and launch it via `open /tmp/eval_review_<skill-name>.html`.
   - Load the exported dataset from `~/Downloads/eval_set.json` after the user edits entries and clicks `"Export Eval Set"` (selecting the most recent file such as `eval_set (1).json` when multiple downloads exist).

3. **Execute Automated Optimization Loop**: Save the approved eval set to the workspace and execute `scripts.run_loop` in the background using the current session model ID (splitting 60% train / 40% held-out test, running each query 3 times, iterating up to 5 rounds, opening an HTML report, and returning JSON with `best_description` selected by held-out test score) while tailing progress updates to the user:

```bash
python -m scripts.run_loop \
  --eval-set <path-to-trigger-eval.json> \
  --skill-path <path-to-skill> \
  --model <model-id-powering-this-session> \
  --max-iterations 5 \
  --verbose
```

4. **Apply Selected Description**: Update the `description` field in `SKILL.md` frontmatter with `best_description` and present the before/after comparison alongside train and held-out test scores.

### Skill Packaging & Delivery

1. Stage the skill directory in `/tmp/<skill-name>/` prior to packaging when source or output paths enforce write restrictions, preserving the original directory name and frontmatter `name` unchanged for existing skills.
2. Package the skill folder into a `.skill` archive:

```bash
python -m scripts.package_skill <path/to/skill-folder>
```

3. Present the resulting `.skill` file via the `present_files` tool when available, or return the generated `.skill` file path to the user for installation.

## Environment Execution Matrix & Bundled References

### Environment Adaptation Matrix

Adapt execution mechanics across the 3 runtime environments according to the following matrix:

| Execution Dimension | Claude Code (Subagents + CLI + Display) | Cowork (Subagents + Headless CLI) | Claude.ai (Single-Agent VM without Subagents/CLI) |
| :--- | :--- | :--- | :--- |
| **Test Case & Baseline Execution** | Spawn `with_skill` and baseline (`without_skill` or `old_skill`) subagents concurrently in the same turn. | Spawn `with_skill` and baseline subagents in parallel; fall back to serial subagent execution if timeouts occur. | Read `SKILL.md` and execute each test prompt sequentially inline; omit baseline runs. |
| **Evaluation Viewer & Feedback Collection** | Launch `eval-viewer/generate_review.py` server in background and read auto-saved `feedback.json` after submission. | Run `eval-viewer/generate_review.py --static <output_path>` prior to self-editing, share the HTML link, and read the downloaded `feedback.json` copied/accessed in the workspace. | Present each prompt and output inline in chat (or save output files for download) and collect user feedback directly in conversation. |
| **Quantitative Benchmarking & Blind Comparison** | Execute `agents/grader.md`, `scripts.aggregate_benchmark`, `agents/analyzer.md`, and optional blind comparison (`agents/comparator.md`). | Execute full grading, benchmark aggregation, analyst pass, and optional blind comparison via subagents. | Omit quantitative benchmarking and blind A/B comparison; evaluate via qualitative user feedback. |
| **Description Optimization (`claude -p`)** | Execute `scripts.run_loop` after user review of `/tmp/eval_review_<skill-name>.html`. | Execute `scripts.run_loop` via subprocess after the skill body stabilizes and the user confirms readiness. | Omit automated description optimization (requires `claude -p` CLI). |
| **Staging & Packaging (`package_skill.py`)** | Copy read-only installed skills to `/tmp/`, run `python -m scripts.package_skill`, and invoke `present_files` or return the path. | Stage in `/tmp/` when permissions require, run `python -m scripts.package_skill`, and invoke `present_files` or return the path. | Copy read-only installed skills to `/tmp/`, run `python -m scripts.package_skill`, and provide the `.skill` file for download. |

### Bundled Reference & Script Inventory

Load or execute the following bundled resources at their designated workflow stages:
- `agents/grader.md`: Assertion evaluation rules and `grading.json` schema (`text`, `passed`, `evidence`) for grader subagents.
- `agents/comparator.md`: Anonymized A/B evaluation protocol for blind comparison subagents.
- `agents/analyzer.md`: Benchmark pattern diagnostics ("Analyzing Benchmark Results") and blind comparison root-cause analysis.
- `references/schemas.md`: JSON schemas for `evals.json`, `eval_metadata.json`, `grading.json`, `benchmark.json`, and `feedback.json`.
- `assets/eval_review.html`: Interactive HTML template for reviewing and exporting trigger evaluation queries (`__EVAL_DATA_PLACEHOLDER__`, `__SKILL_NAME_PLACEHOLDER__`, `__SKILL_DESCRIPTION_PLACEHOLDER__`).
- `eval-viewer/generate_review.py`: Viewer generator for qualitative outputs and quantitative benchmarks.
- `scripts/aggregate_benchmark.py`: Aggregation module (`python -m scripts.aggregate_benchmark`) producing `benchmark.json` and `benchmark.md`.
- `scripts/run_loop.py`: Automated train/test split evaluation loop (`python -m scripts.run_loop`) for frontmatter `description` optimization.
- `scripts/package_skill.py`: Packaging utility (`python -m scripts.package_skill`) generating the distributable `.skill` archive.
