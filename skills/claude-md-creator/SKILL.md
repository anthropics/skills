---
name: claude-md-creator
description: |
  Create, evaluate, and improve CLAUDE.md files for Claude Code projects. Use this skill whenever
  the user mentions CLAUDE.md, project instructions, Claude Code memory, project rules, .claude/rules/,
  or wants to set up persistent instructions for Claude Code. Also trigger when users say "init my project
  for Claude", "set up Claude Code", "evaluate my CLAUDE.md", "improve my CLAUDE.md", "create project rules",
  "audit my CLAUDE.md", or ask about best practices for Claude Code memory. This skill handles both creating
  new CLAUDE.md files from scratch and evaluating/improving existing ones.
---

# CLAUDE.md Creator & Evaluator

Create well-structured CLAUDE.md files and evaluate existing ones with a 5-phase pipeline that tests codebase coherence and blind effectiveness.

## Overview

CLAUDE.md files give Claude persistent instructions for a project. They're loaded into every session's context window and directly affect how reliably Claude follows your team's standards. This skill provides:

1. **Create** — Generate a CLAUDE.md from scratch by interviewing the user and analyzing the codebase
2. **Quick Eval** — Verify that every claim in your CLAUDE.md matches the actual codebase (~1 min)
3. **Full Eval** — Quick Eval + blind A/B test proving your CLAUDE.md actually changes Claude's behavior (~5-10 min)
4. **Improve** — Apply evaluation findings to fix stale, vague, or ineffective instructions

## Mode Detection

- **"Create CLAUDE.md"** / **"Init for Claude"** → Create mode
- **"Evaluate CLAUDE.md"** / **"Audit"** / **"Quick eval"** → Quick Eval
- **"Full eval"** / **"Blind test"** / **"Test effectiveness"** → Full Eval
- **"Improve CLAUDE.md"** / **"Fix my CLAUDE.md"** → Quick Eval → Improve
- Ambiguous → Ask the user

---

## Create Mode

### Step 1: Analyze the Codebase

Scan the project to gather context:

1. **Package manager & scripts**: Read `package.json`, `pyproject.toml`, `Cargo.toml`, `Makefile`, etc.
2. **Framework detection**: Check for Next.js, React, Vue, Django, Rails, etc.
3. **Test framework**: Look for jest, pytest, vitest, etc. and how to run tests
4. **Linting/formatting**: Check for eslint, prettier, ruff, black, etc.
5. **Directory structure**: `ls` the top-level and key directories (`src/`, `app/`, `lib/`, `tests/`)
6. **Existing configuration**: Check for `.claude/`, `.claude/rules/`, existing CLAUDE.md
7. **Git conventions**: Read recent commit messages for style patterns
8. **CI/CD**: Check for `.github/workflows/`, `Jenkinsfile`, etc.

### Step 2: Interview the User

Fill gaps that can't be determined from code alone:

1. **Build & deploy**: Any non-obvious build steps? Environment-specific commands?
2. **Architecture decisions**: Patterns the team follows that aren't obvious from code?
3. **Coding standards**: Naming conventions, import ordering, error handling patterns?
4. **Common workflows**: Feature branch strategy? PR process?
5. **Gotchas**: Known pitfalls or anti-patterns specific to this project?
6. **Team context**: Monorepo? Multiple teams with different conventions?

Don't ask about things already found from the codebase scan.

### Step 3: Generate the CLAUDE.md

#### Size: Target under 200 lines

The entire CLAUDE.md is loaded into every session's context window. Longer files consume more tokens and reduce adherence. Split using `.claude/rules/` files.

#### Structure: Markdown headers and bullets

Claude scans structure the way readers do. Organized sections are easier to follow.

#### Specificity: Concrete and verifiable

- "Use 2-space indentation" instead of "Format code properly"
- "Run `npm test` before committing" instead of "Test your changes"
- "API handlers live in `src/api/handlers/`" instead of "Keep files organized"

#### Recommended Structure

```markdown
# Project Name

Brief one-line description.

## Build & Run

- `command` — what it does

## Test

- `command` — run all tests

## Code Style

- Concrete rule 1

## Architecture

- Directory conventions

## Conventions

- Naming, imports, error handling

## Common Pitfalls

- Gotcha — why and how to avoid
```

#### What to include

- Build, lint, and test commands (exact commands)
- Code style preferences (indentation, naming, imports)
- Architecture patterns and directory conventions
- Common pitfalls specific to this project
- Workflow instructions (branch naming, PR process)

#### What NOT to include

- Things derivable from reading code
- Git history or recent changes
- Long reference documentation (use `.claude/rules/` or `references/`)
- Ephemeral task details
- Generic programming advice Claude already knows

### Step 4: Generate .claude/rules/ Files (if needed)

If instructions exceed 200 lines, or if the project has distinct domains, split:

```
.claude/
├── CLAUDE.md              # Main instructions (under 200 lines)
└── rules/
    ├── code-style.md      # Code style guidelines
    ├── testing.md         # Testing conventions
    └── api-design.md      # API development rules
```

Path-specific rules use YAML frontmatter:

```markdown
---
paths:
  - "src/api/**/*.ts"
---

# API Development Rules

- All endpoints must include input validation
```

### Step 5: Present and Iterate

Show the generated files. Ask for feedback. Adjust.

---

## Quick Eval (Phase 1-2)

Fast codebase coherence check. Verifies every instruction matches the real project.

### Phase 1: Claim Extraction

Extract every testable instruction from the CLAUDE.md into structured claims.

```bash
python <skill-path>/scripts/extract_claims.py <claude-md-path> --rules-dir <rules-dir> --pretty --output <workspace>/claims.json
```

Then launch the `claim_extractor` agent to enrich claims the script missed (natural language conventions, implicit architecture decisions, compound rules):

```
Agent(claim_extractor): Enrich claims.json with semantic claims missed by the script.
  Inputs: claude_md_path, rules_dir, script output at <workspace>/claims.json
  Output: Enriched <workspace>/claims.json
```

### Phase 2: Codebase Coherence Verification

Verify each claim against the actual project.

```bash
python <skill-path>/scripts/verify_coherence.py <workspace>/claims.json <project-root> --pretty --output <workspace>/coherence_raw.json
```

Then launch the `coherence_checker` agent to handle claims the script marked `unverifiable` (conventions, naming patterns, import rules — these require code sampling):

```
Agent(coherence_checker): Enrich coherence_raw.json by sampling actual code files.
  Inputs: claims.json, coherence_raw.json, project_root
  Output: Enriched <workspace>/coherence_report.json
```

### Generate Quick Eval Report

Aggregate and generate HTML report:

```bash
python <skill-path>/scripts/aggregate_results.py <workspace>/coherence_report.json --claims <workspace>/claims.json --pretty --output <workspace>/evaluation_summary.json
python <skill-path>/scripts/generate_report.py <workspace>/evaluation_summary.json --output /tmp/claude-md-eval.html
```

Open the report and present the summary to the user:
- Overall score (0-100) with grade (A-F)
- Coherence breakdown (verified / stale / partial / unverifiable)
- Top issues ranked by severity
- Fix suggestions with specific corrections

---

## Full Eval (Phase 1-5)

Everything in Quick Eval plus a blind A/B test proving the CLAUDE.md actually changes Claude's behavior.

### Phase 1-2: Same as Quick Eval

Run the same claim extraction and coherence verification.

### Phase 3: Dynamic Eval Task Generation

Generate coding tasks that test whether Claude follows the CLAUDE.md conventions.

```bash
python <skill-path>/scripts/generate_eval_tasks.py <workspace>/claims.json <workspace>/coherence_report.json <project-root> --pretty --output <workspace>/eval_tasks_skeleton.json
```

Then launch the `eval_generator` agent to fill in natural task prompts:

```
Agent(eval_generator): Create 3-7 realistic coding tasks from verified claims.
  Inputs: claims.json, coherence_report.json, project_root, eval_tasks_skeleton.json
  Output: <workspace>/eval_tasks.json with natural task_prompt for each task
```

**Important**: Task prompts must NOT mention CLAUDE.md conventions. The whole point is to test whether Claude follows them from context, not from explicit instructions.

### Phase 4: Blind Effectiveness Test

For each eval task, run two coding sessions:

#### Step 4a: Run WITH CLAUDE.md

```
Agent(blind_coder): Complete coding task with CLAUDE.md context.
  Inputs: task_prompt, project_root, output_dir=<workspace>/with_claude_md/<task-id>/, claude_md_content=<full CLAUDE.md content>
```

#### Step 4b: Run WITHOUT CLAUDE.md

```
Agent(blind_coder): Complete coding task without CLAUDE.md context.
  Inputs: task_prompt, project_root, output_dir=<workspace>/without_claude_md/<task-id>/
```

Run both in parallel per task for efficiency.

#### Step 4c: Programmatic Checks

For each task's expected_behaviors, run the programmatic checks:
- `code_pattern`: regex match in generated code
- `file_location`: file created in expected directory
- `file_naming`: filename matches regex pattern
- `import_style`: import follows convention
- `code_absence`: pattern does NOT appear

#### Step 4d: Blind Judgment

Randomly assign outputs as "A" and "B" (so the judge doesn't know which had CLAUDE.md):

```
Agent(blind_judge): Compare Output A vs Output B.
  Inputs: task_prompt, output_a_dir, output_b_dir, project_root, expected_behaviors
  Output: JSON with winner, reasoning, scores (naming/structure/style/patterns/overall 1-5)
```

Collect all results into `<workspace>/blind_results.json`.

### Phase 5: Final Report

Aggregate everything:

```bash
python <skill-path>/scripts/aggregate_results.py <workspace>/coherence_report.json --blind <workspace>/blind_results.json --claims <workspace>/claims.json --pretty --output <workspace>/evaluation_summary.json
python <skill-path>/scripts/generate_report.py <workspace>/evaluation_summary.json --output /tmp/claude-md-eval.html
```

Present the full report with all three tabs:
1. **Coherence** — codebase alignment details
2. **Effectiveness** — blind test wins/ties/losses + score delta
3. **Recommendations** — remove, fix, add, strengthen

---

## Improve Mode

After evaluation, apply improvements:

1. Read the evaluation report (run Quick Eval if not already done)
2. Fix issues in priority order:
   - **Remove** vague/generic instructions
   - **Fix** stale paths and outdated references
   - **Add** missing key sections (build, test commands)
   - **Strengthen** partially-followed conventions
3. Show the user a diff of changes
4. If the file needs splitting, create `.claude/rules/` files
5. Re-run Quick Eval to confirm improvement

---

## Scoring & Grades

### Coherence Score (Quick Eval)

Percentage of verifiable claims that match the codebase:

```
coherence_score = verified_claims / (verified + stale + partial) × 100
```

### Effectiveness Score (Full Eval)

Weighted blind test results:

```
effectiveness_score = (wins + ties × 0.5) / total_tasks × 100
```

### Overall Score

| Eval Type | Formula |
|-----------|---------|
| Quick Eval | `coherence_score` |
| Full Eval | `coherence × 0.5 + effectiveness × 0.5` |

### Grades

| Score | Grade | Meaning |
|-------|-------|---------|
| 90-100 | A | Excellent — all claims match, high effectiveness |
| 80-89 | B | Good — minor issues |
| 70-79 | C | Adequate — several fixes needed |
| 60-69 | D | Needs work — significant gaps |
| 0-59 | F | Major rewrite recommended |

---

## File Reference

### Scripts
- `scripts/extract_claims.py` — Phase 1: parse CLAUDE.md into structured claims
- `scripts/verify_coherence.py` — Phase 2: verify claims against codebase
- `scripts/generate_eval_tasks.py` — Phase 3: generate eval task skeletons
- `scripts/aggregate_results.py` — Phase 5: aggregate all results
- `scripts/generate_report.py` — Phase 5: generate HTML report

### Agents
- `agents/claim_extractor.md` — Enriches script-extracted claims with semantic analysis
- `agents/coherence_checker.md` — Verifies conventions by sampling actual code
- `agents/eval_generator.md` — Creates natural coding tasks from claims
- `agents/blind_coder.md` — Executes coding tasks (with or without CLAUDE.md)
- `agents/blind_judge.md` — Blind comparison of two code outputs

### References
- `references/schemas.md` — JSON schemas for all data structures
- `references/claim-taxonomy.md` — Claim type definitions and patterns
- `references/best-practices.md` — CLAUDE.md best practices from official docs
