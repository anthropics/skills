# Skill Creator

The meta-skill. Teaches Claude how to build, validate, test, and package skills—the modular units that transform Claude Code from a general-purpose agent into a specialized one.

**Last updated:** 2026-03-04

**Reflects:** Claude Code skills specification (Feb 2026), [Agent Skills](https://agentskills.io/) open standard, Claude 4.6 prompting best practices, [Skill_Seekers](https://github.com/yusufkaraaslan/Skill_Seekers) v2.0.0+ for documentation scraping, and Anthropic's [skill-creator eval framework](https://claude.com/blog/improving-skill-creator-test-measure-and-refine-agent-skills) (March 2026) for testing, benchmarking, and iterative refinement.

---

## Why This Skill Exists

Skills are Claude Code's extension mechanism—modular packages of specialized knowledge, workflows, scripts, and assets that Claude loads on demand. A well-crafted skill turns a 10-minute repeated workflow into a one-shot invocation. A poorly crafted one wastes context tokens, triggers at wrong times, or silently fails.

This skill encodes the full lifecycle: understanding requirements, planning reusable contents, scaffolding structure, writing effective SKILL.md instructions, populating references from documentation, validating, packaging, and iterating. It is the skill that builds all other skills.

---

## Structure

```
skill-creator/
  SKILL.md                                  # Full skill creation guide (~600 lines)
  README.md                                 # This file
  LICENSE.txt                               # License
  scripts/
    init_skill.py                           # Scaffold new skill from template
    quick_validate.py                       # Validate frontmatter and structure
    package_skill.py                        # Zip for distribution (validates first)
    scrape_documentation_helper.py          # Interactive Skill_Seekers guide
    run_eval.py                             # Execute evals with/without skill
    aggregate_benchmark.py                  # Aggregate grading into benchmark report
    run_loop.py                             # Description optimization loop
    improve_description.py                  # Generate improved descriptions
    generate_report.py                      # HTML report from eval/benchmark data
    utils.py                                # Shared utilities
  agents/
    grader.md                               # Grade assertions against outputs
    comparator.md                           # Blind A/B output comparison
    analyzer.md                             # Benchmark pattern analysis
  eval-viewer/
    generate_review.py                      # Generate HTML review viewer
    viewer.html                             # HTML template for review UI
  references/
    frontmatter-reference.md                # Complete YAML frontmatter field reference
    documentation-scraping.md               # Skill_Seekers deep dive
    schemas.md                              # JSON schemas for eval/grading/benchmark
```

---

## What It Covers

### Skill Anatomy

Every skill is a directory with a required `SKILL.md` and optional bundled resources:

| Directory | Content Type | Purpose |
|-----------|-------------|---------|
| `scripts/` | Executable code | Deterministic tasks. Only output enters context—a 200-line script costs ~20 tokens. |
| `references/` | Documentation | Loaded on demand. Keeps SKILL.md lean while making deep knowledge discoverable. |
| `assets/` | Output resources | Templates, images, fonts. Used in final output without entering context. |

### Progressive Disclosure

Skills load in three tiers to minimize context consumption:

| Level | When Loaded | Token Cost |
|-------|-------------|------------|
| **Metadata** | Always (startup) | ~100 tokens per skill |
| **Instructions** | When triggered | Under 5k tokens |
| **Resources** | As needed | Effectively unlimited |

You can install dozens of skills with minimal penalty. Claude only knows each skill exists until one is triggered.

### SKILL.md Frontmatter

10 fields control invocation, tool access, model routing, and subagent execution:

| Field | Purpose |
|-------|---------|
| `name` | Display name (max 64 chars, kebab-case) |
| `description` | When to use (max 1024 chars)—this is the trigger |
| `argument-hint` | Autocomplete hint (e.g., `[issue-number]`) |
| `disable-model-invocation` | User-only invoke (for side-effect workflows) |
| `user-invocable` | Claude-only (background knowledge, not a command) |
| `allowed-tools` | Restrict tool access when active |
| `model` | Model override when active |
| `context` | `fork` = isolated subagent execution |
| `agent` | Subagent type: `Explore`, `Plan`, `general-purpose`, custom |
| `hooks` | Scoped lifecycle hooks |

Full reference with invocation control matrix: `references/frontmatter-reference.md`

### Dynamic Context Injection

Shell commands execute before skill content reaches Claude. The exclamation-backtick syntax (`!` + `` `command` ``) runs preprocessing—Claude sees only the rendered output. Powers live PR summaries, git diffs, and dynamic context.

### Claude 4.6 Prompting Alignment

The skill encodes writing conventions calibrated for Claude 4.6:

- **Imperative voice**, not second person. "To accomplish X, do Y" not "You should do X."
- **Direct imperatives** without ALL CAPS or CRITICAL/MANDATORY/MUST qualifiers. Claude 4.6 follows well-structured instructions without coercive framing.
- **Explain WHY** behind directives. Claude generalizes better from explanations than from bare commands.
- **No anti-laziness prompts.** "Be thorough" and "think carefully" amplify Claude 4.6 into over-planning loops.
- **Explicit subagent guidance** on when NOT to spawn agents. Single-file edits and sub-5-minute tasks don't need orchestration.

---

## Scripts

### `init_skill.py` — Scaffold a new skill

```bash
python3 ~/.claude/skills/skill-creator/scripts/init_skill.py my-skill --path ~/.claude/skills
```

Creates a complete template directory with SKILL.md (frontmatter + TODO placeholders), and example `scripts/`, `references/`, `assets/` directories.

### `quick_validate.py` — Validate structure and frontmatter

```bash
python3 ~/.claude/skills/skill-creator/scripts/quick_validate.py ~/.claude/skills/my-skill
```

Checks: SKILL.md exists, valid YAML frontmatter, naming conventions, description quality, file organization.

### `package_skill.py` — Package for distribution

```bash
python3 ~/.claude/skills/skill-creator/scripts/package_skill.py ~/.claude/skills/my-skill
```

Validates first, then creates `my-skill.zip` preserving directory structure. Fails with diagnostics if validation errors found.

### `scrape_documentation_helper.py` — Populate references from docs

```bash
python3 ~/.claude/skills/skill-creator/scripts/scrape_documentation_helper.py
```

Interactive guide for using [Skill_Seekers](https://github.com/yusufkaraaslan/Skill_Seekers) to scrape framework documentation into `references/`. Supports 15+ preset configs (React, Vue, Django, FastAPI, Godot, Tailwind, etc.), llms.txt fast-path, and GitHub source extraction.

---

## The 8-Step Creation Process

1. **Understand** — Gather concrete examples of how the skill will be used. What triggers it? What does the user say?
2. **Plan** — Analyze examples to identify reusable resources: scripts for repeated code, references for domain knowledge, assets for templates.
3. **Initialize** — Run `init_skill.py` to scaffold the directory.
4. **Edit** — Build resources first (scripts, references, assets), then write SKILL.md instructions. Optionally scrape documentation with Skill_Seekers.
5. **Package** — Run `package_skill.py` to validate and zip.
6. **Test & Evaluate** — Write evals (`evals/evals.json`), run with/without skill, grade assertions, aggregate benchmarks, review in the eval viewer.
7. **Optimize Description** — Generate trigger eval queries, run the optimization loop with train/test split, adopt the best-performing description.
8. **Iterate** — Use the skill on real tasks, notice gaps, refine.

---

## Skill Locations

| Location | Path | Scope |
|----------|------|-------|
| Personal | `~/.claude/skills/<name>/SKILL.md` | All your projects |
| Project | `.claude/skills/<name>/SKILL.md` | This project only |
| Plugin | `<plugin>/skills/<name>/SKILL.md` | Where plugin enabled (namespaced) |
| Enterprise | Managed settings | All org users (highest priority) |

---

## Eval Framework

Adapted from Anthropic's [skill-creator eval framework](https://claude.com/blog/improving-skill-creator-test-measure-and-refine-agent-skills) (March 2026). Measures skill effectiveness through structured testing.

### Quick Start

```bash
# 1. Write evals in your skill directory
mkdir -p my-skill/evals/files
# Create evals/evals.json with test prompts and expectations

# 2. Run evals
python3 scripts/run_eval.py --eval-set my-skill/evals/evals.json --skill-path my-skill/

# 3. Grade outputs
# The grader agent (agents/grader.md) evaluates expectations against outputs

# 4. Aggregate into benchmark
python3 scripts/aggregate_benchmark.py benchmark-dir/ --skill-path my-skill/

# 5. Review results
python3 eval-viewer/generate_review.py workspace/
```

### Agents

| Agent | Purpose |
|-------|---------|
| `agents/grader.md` | Evaluate assertions as PASS/FAIL with evidence, extract implicit claims |
| `agents/comparator.md` | Blind A/B comparison—judges outputs without knowing which skill produced them |
| `agents/analyzer.md` | Surface patterns across benchmark runs (non-discriminating assertions, variance, tradeoffs) |

### Description Optimization

Systematically improve the YAML `description` field to reduce undertriggering:

```bash
python3 scripts/run_loop.py \
  --eval-set trigger-queries.json \
  --skill-path my-skill/ \
  --holdout 0.4 \
  --runs-per-query 3 \
  --model sonnet
```

Generates improved descriptions using extended thinking, evaluates on held-out test set, produces an HTML accuracy report.

### Schemas

All JSON schemas documented in `references/schemas.md`: `evals.json`, `grading.json`, `benchmark.json`, `history.json`, `timing.json`, `metrics.json`, `comparison.json`, `analysis.json`.

---

## Requirements

- Python 3.9+
- No external dependencies for core scripts (eval scripts use stdlib only)
- [Skill_Seekers](https://github.com/yusufkaraaslan/Skill_Seekers) for documentation scraping (optional)

---

## Install

```bash
cp -r skills/skill-creator ~/.claude/skills/
```
