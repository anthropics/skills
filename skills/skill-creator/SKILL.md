---
name: skill-creator
description: Create new skills, modify and improve existing skills, and measure skill performance. Use when users want to create a skill from scratch, edit, or optimize an existing skill, run evals to test a skill, benchmark skill performance with variance analysis, or optimize a skill's description for better triggering accuracy.
license: Apache-2.0
metadata:
  fork: Cadtastic/skills
  upstream: anthropics/skills
  version: "1.1.0"
---

# Skill Creator

A skill for creating new skills and iteratively improving them.

The core loop:

1. Decide what the skill should do
2. Write a draft
3. Create test prompts and run claude-with-the-skill on them
4. Help the user evaluate results (qualitatively + quantitatively)
5. Improve the skill based on feedback
6. Repeat until satisfied
7. Optimize the description for better triggering accuracy
8. Package and deliver

Your job is to figure out where the user is in this loop and jump in. They may bring an idea ("I want to make a skill for X"), an existing draft (skip to eval/iterate), or just want to vibe ("I don't need evals, just help me think it through"). Be flexible.

## Communicating with the user

Users come in with a wide range of familiarity with coding jargon. Some are senior engineers; some are plumbers, parents, or grandparents who just started exploring Claude. Read context cues:

- "evaluation" and "benchmark" are borderline, but usually OK
- "JSON" and "assertion" — wait for cues the user knows these before using without explanation
- When in doubt, briefly define the term

---

## Creating a skill

### Capture intent

Start by understanding what the user wants. The current conversation may already contain the workflow they want to capture ("turn this into a skill"). Extract from history first — tools used, sequence of steps, corrections, observed input/output formats. The user fills gaps and confirms before proceeding.

Then probe:

1. What should this skill enable Claude to do?
2. When should it trigger? (user phrases, contexts)
3. What's the expected output format?
4. Should we set up test cases? Skills with objectively verifiable outputs (file transforms, data extraction, code generation, fixed workflows) benefit from them. Subjective skills (writing style, art) often don't. Suggest the default; let the user decide.

### Interview and research

Proactively ask about edge cases, input/output formats, example files, success criteria, and dependencies. Don't write test prompts until this is ironed out.

If useful MCPs are available (searching docs, finding similar skills, looking up best practices), research in parallel via subagents.

### Write the SKILL.md

The Agent Skills specification at <https://agentskills.io/specification> is the source of truth for the SKILL.md format. The constraints encoded below were correct at the time this guide was written; **before final packaging, run the spec-drift check in `references/spec-check.md` to catch any changes since.**

#### Required frontmatter

- **name**
  - 1–64 characters
  - Lowercase ASCII letters (`a-z`) and hyphens (`-`) only
  - No leading or trailing hyphens; no consecutive hyphens (`--`)
  - **Must match the parent directory name exactly.** Rename the folder → rename the `name:` field. Mismatch = silent install rejection.

- **description**
  - 1–1024 characters. **Hard limit** — installer rejects anything over with `field 'description' in SKILL.md must be at most 1024 characters`.
  - Describes both what the skill does AND specific contexts for when to use it. All "when to use" info lives here, not in the body.
  - Claude tends to *under-trigger* skills — write descriptions that are a little "pushy" with specific trigger phrases.
    - Before: `"How to build a dashboard."`
    - After: `"How to build a dashboard. Use whenever the user mentions dashboards, data visualization, internal metrics, or wants to display company data, even if they don't explicitly ask for a 'dashboard.'"`
  - If over budget, condense trigger lists, drop parenthetical methodology mentions, prefer one good trigger paragraph over two. The pushiness guidance still applies — just within budget.

#### Optional frontmatter

- **license** — License name or reference to a bundled `LICENSE.txt`. Keep short.
  - Examples: `license: Apache-2.0` · `license: Proprietary. LICENSE.txt has complete terms`
- **compatibility** — 1–500 characters. Environment requirements: intended product, system packages, network access, etc. Most skills don't need this.
  - Examples: `compatibility: Requires Python 3.14+ and uv` · `compatibility: Designed for Claude Code (or similar products)`
- **metadata** — Arbitrary key-value mapping for additional metadata. Keep keys unique to avoid conflicts.
  ```yaml
  metadata:
    author: example-org
    version: "1.0"
  ```
- **allowed-tools** (experimental) — Space-separated string of pre-approved tools the skill may use. Support varies between agent implementations.
  - Example: `allowed-tools: Bash(git:*) Bash(jq:*) Read`

#### Validate the frontmatter

Run the bundled validator before packaging. It checks every constraint above in one pass and reports per-field PASS/FAIL with specific error messages:

```bash
uv run scripts/validate_frontmatter.py path/to/your/skill/
```

Exit code 0 = valid, 1 = constraint violated, 2 = could not parse. The script uses [PEP 723](https://peps.python.org/pep-0723/) inline metadata, so `uv run` (or `pipx run`) resolves PyYAML automatically — no manual install. See `scripts/validate_frontmatter.py --help` for options.

For end-to-end validation against the upstream spec (catches constraint changes that may have happened since this guide was written), see the spec-drift workflow in `references/spec-check.md`.

### Skill Writing Guide

#### Anatomy of a skill

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

#### Progressive disclosure

Skills load progressively:

1. **Metadata** (~100 tokens): `name` + `description`, always in context
2. **SKILL.md body** (<5000 tokens recommended): loaded when the skill activates
3. **Bundled resources** (unlimited): loaded only when needed; scripts can execute without loading

**Key patterns:**

- Keep SKILL.md under 500 lines / 5000 tokens. If approaching this, add a layer of hierarchy with clear pointers to follow-up reference files.
- Reference files clearly from SKILL.md with guidance on when to read them.
- For large reference files (>300 lines), include a table of contents.
- **Keep file references one level deep from SKILL.md.** Avoid deeply nested reference chains — they fragment context and obscure what's where.

**Domain organization:** when a skill supports multiple domains or frameworks, organize by variant:

```
cloud-deploy/
├── SKILL.md (workflow + selection)
└── references/
    ├── aws.md
    ├── gcp.md
    └── azure.md
```

Claude reads only the relevant reference file.

#### Principle of lack of surprise

Skills must not contain malware, exploit code, or anything that could compromise security. The skill's contents should match its description — don't go along with requests for misleading skills or skills designed to facilitate unauthorized access, data exfiltration, or other malicious activities. Roleplay-as-X skills are fine.

#### Writing patterns

Prefer the imperative form in instructions.

**Defining output formats:**

```markdown
## Report structure
ALWAYS use this exact template:
# [Title]
## Executive summary
## Key findings
## Recommendations
```

**Examples pattern:**

```markdown
## Commit message format
**Example 1:**
Input: Added user authentication with JWT tokens
Output: feat(auth): implement JWT-based authentication
```

### Writing style

Explain *why* in lieu of heavy-handed musty MUSTs. LLMs have good theory of mind — given a good harness and the reasoning behind a rule, they go beyond rote instructions. If you find yourself writing ALWAYS or NEVER in all caps, or super-rigid structures, reframe and explain. More humane, more effective.

Make the skill general, not super-narrow to specific examples. Draft, look at it with fresh eyes, improve.

### Test cases

After writing the draft, come up with 2–3 realistic test prompts — the kind of thing a real user would actually say. Share them with the user before running: *"Here are a few test cases I'd like to try. Do these look right, or do you want to add more?"*

Save test cases to `evals/evals.json`. Don't write assertions yet — just the prompts. Assertions get drafted while runs are in progress.

```json
{
  "skill_name": "example-skill",
  "evals": [
    { "id": 1, "prompt": "User's task prompt", "expected_output": "Description", "files": [] }
  ]
}
```

See `references/schemas.md` for the full schema.

---

## Running and evaluating test cases

The full procedure — spawning runs, capturing timing, grading, aggregating, launching the eval viewer — is in **`references/running-evals.md`**. Read it when you reach this phase. Key reminders:

- Spawn with-skill AND baseline runs **in the same turn**, not serial.
- Save outputs to `<skill-name>-workspace/iteration-<N>/eval-<ID>/...`.
- Capture timing from subagent notifications immediately — that data isn't persisted elsewhere.
- After grading, run `scripts/aggregate_benchmark.py`, then `eval-viewer/generate_review.py`. Don't write your own HTML; use the bundled viewer.
- For Cowork/headless: pass `--static <output_path>` to write a standalone HTML instead of starting a server. **Generate the eval viewer BEFORE evaluating outputs yourself** — the user reviews first.

---

## Improving the skill

You've run the tests, the user reviewed the results, now you make the skill better.

### How to think about improvements

1. **Generalize from feedback.** Skills are used many times across many prompts. You and the user iterate on a few examples because it's fast — but if the skill only works for those examples, it's useless. Avoid fiddly overfit changes and oppressive MUSTs. If something's stubborn, try a different metaphor or pattern of working. Cheap to try; sometimes lands somewhere great.

2. **Keep the prompt lean.** Cut things that aren't pulling weight. Read transcripts, not just outputs — if the skill makes the model waste time on unproductive steps, remove the instructions causing that.

3. **Explain the why.** When you find yourself writing ALWAYS or NEVER in all caps, or rigid structures, that's a yellow flag. Reframe and explain the reasoning. The model will generalize from understanding; it won't from rules alone.

4. **Look for repeated work across test cases.** If all three subagents independently wrote a similar helper script, that's a strong signal the skill should bundle that script. Write once, put in `scripts/`, point the skill at it.

This task creates real economic value. Your thinking time is not the blocker — take time, write a draft, look at it again, improve.

### The iteration loop

1. Apply improvements
2. Rerun all test cases into a new `iteration-<N+1>/` directory (including baselines)
3. Launch the reviewer with `--previous-workspace` pointing at the previous iteration
4. Wait for user feedback
5. Read feedback, improve again, repeat

Keep going until the user is happy, the feedback is empty, or you stop making meaningful progress.

---

## Advanced: blind comparison

For rigorous A/B comparison between two versions ("is the new version actually better?"), use the blind comparison system. See `agents/comparator.md` and `agents/analyzer.md`. Optional; most users don't need it.

---

## Description optimization

After creating or improving a skill, offer to optimize the description for better triggering accuracy. Full procedure in **`references/description-optimization.md`**. The short version:

1. Generate ~20 realistic test queries (mix of should-trigger and should-not-trigger).
2. Review queries with the user via the HTML template at `assets/eval_review.html`.
3. Run `scripts/run_loop.py` to iteratively improve the description against the eval set.
4. Apply the best result to the skill's frontmatter.

The triggering mechanism: skills appear in `available_skills` with name + description; Claude consults a skill based on its description when the task is complex enough to benefit. Simple one-step queries may not trigger skills regardless of description quality — design eval queries that are substantive.

---

## Environment-specific guidance

This skill works in Claude Code, Claude.ai, and Cowork. Each has different capabilities (subagents, browser, display, networking). Adaptations for each are in **`references/environments.md`**. Read it when you need to adapt the workflow for the user's environment.

---

## Staying current with the Agent Skills spec

This guide encodes the spec as of writing. The spec at <https://agentskills.io/specification> evolves — fields get added, limits change, deprecations happen. To stay current without unnecessary fetches:

- **Before final packaging**, run the spec-drift check in **`references/spec-check.md`**. One fetch, comparison, delta surfaced.
- **If an install fails with a validation error this guide doesn't anticipate**, fetch the spec and look for what changed.
- **On explicit user request** ("is my skill spec-compliant?"), run the check.
- **Cache within a session** — don't refetch the spec for every skill creation in the same conversation. The spec doesn't change in 30 minutes.
- **Do NOT fetch on every invocation** — adds latency, costs bandwidth, and offers no value when the local guide is current.

---

## Reference files and scripts

`agents/` — specialized subagent prompts:

- `agents/grader.md` — evaluate assertions against outputs
- `agents/comparator.md` — blind A/B comparison
- `agents/analyzer.md` — analyze why one version beat another

`references/` — on-demand documentation:

- `references/schemas.md` — JSON structures for evals.json, grading.json, etc.
- `references/running-evals.md` — full eval procedure (spawn, time, grade, aggregate, view)
- `references/description-optimization.md` — full trigger-optimization workflow
- `references/environments.md` — Claude.ai and Cowork specific adaptations
- `references/spec-check.md` — verify the skill against the live Agent Skills documentation (gating + procedure)
- `references/spec-source-map.md` — top