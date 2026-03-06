---
name: skill-creator
description: Create new skills, modify and improve existing skills, and measure skill performance. Use when users want to create a skill from scratch, update or optimize an existing skill, run evals to test a skill, benchmark skill performance with variance analysis, or optimize a skill's description for better triggering accuracy.
---

# Skill Creator

This skill provides guidance for creating effective skills.

## About Skills

Skills are modular, self-contained packages that extend Claude's capabilities by providing specialized knowledge, workflows, and tools. Think of them as "onboarding guides" for specific domains or tasks—they transform Claude from a general-purpose agent into a specialized agent equipped with procedural knowledge that no model can fully possess.

Skills follow the [Agent Skills](https://agentskills.io/) open standard, with Claude Code extensions for invocation control, subagent execution, and dynamic context injection.

### What Skills Provide

1. Specialized workflows - Multi-step procedures for specific domains
2. Tool integrations - Instructions for working with specific file formats or APIs
3. Domain expertise - Company-specific knowledge, schemas, business logic
4. Bundled resources - Scripts, references, and assets for complex and repetitive tasks

### Anatomy of a Skill

Every skill consists of a required SKILL.md file and optional bundled resources:

```
skill-name/
├── SKILL.md (required)
│   ├── YAML frontmatter metadata
│   └── Markdown instructions
└── Bundled Resources (optional)
    ├── scripts/          - Executable code (Python/Bash/etc.)
    ├── references/       - Documentation loaded into context as needed
    └── assets/           - Files used in output (templates, icons, fonts)
```

#### SKILL.md (required)

**Metadata Quality:** The `name` and `description` in YAML frontmatter determine when Claude will use the skill. Be specific about what the skill does and when to use it. Use the third-person (e.g. "This skill should be used when..." instead of "Use this skill when...").

**Frontmatter Fields:**

| Field | Required | Description |
|-------|----------|-------------|
| `name` | No | Display name (max 64 chars, lowercase + hyphens). Defaults to directory name. |
| `description` | Recommended | What the skill does and when to use it (max 1024 chars). |
| `argument-hint` | No | Hint shown during autocomplete (e.g., `[issue-number]`). |
| `disable-model-invocation` | No | `true` = only user can invoke via `/name`. |
| `user-invocable` | No | `false` = hide from `/` menu (Claude-only background knowledge). |
| `allowed-tools` | No | Restrict tools when skill is active (e.g., `Read, Grep, Glob`). |
| `model` | No | Model override when skill is active. |
| `context` | No | `fork` = run in isolated subagent. |
| `agent` | No | Subagent type: `Explore`, `Plan`, `general-purpose`, or custom from `.claude/agents/`. |
| `hooks` | No | Scoped hooks for skill lifecycle. See [Hooks docs](https://code.claude.com/docs/en/hooks). |

**Example with all fields:**

```yaml
---
name: deploy-production
description: Deploy the application to production. Use after all tests pass.
argument-hint: [environment]
disable-model-invocation: true
allowed-tools: Bash(deploy:*), Read
context: fork
agent: general-purpose
---
```

### String Substitutions

Skills support dynamic value substitution in the markdown content:

| Variable | Description |
|----------|-------------|
| `$ARGUMENTS` | All arguments passed when invoking (e.g., `/my-skill arg1 arg2`) |
| `${CLAUDE_SESSION_ID}` | Current session ID for logging or session-specific files |

If `$ARGUMENTS` is not present in content, arguments are appended as `ARGUMENTS: <value>`.

**Example:**

```markdown
---
name: fix-issue
description: Fix a GitHub issue
disable-model-invocation: true
---

Fix GitHub issue $ARGUMENTS following our coding standards.

Log progress to logs/${CLAUDE_SESSION_ID}.log
```

### Dynamic Context Injection

The exclamation-backtick syntax runs shell commands before skill content reaches Claude. The command output replaces the placeholder.

**Syntax:** exclamation mark followed by backtick-wrapped command: `EXCLAIM` + `BACKTICK command BACKTICK`

**Example skill content:**

```
## PR Context
- Diff: EXCLAIM-BACKTICK gh pr diff BACKTICK
- Comments: EXCLAIM-BACKTICK gh pr view --comments BACKTICK
- Changed files: EXCLAIM-BACKTICK gh pr diff --name-only BACKTICK

Summarize this pull request...
```

(Replace EXCLAIM with the exclamation mark character and BACKTICK with the backtick character in real skills)

When this skill runs:
1. Each exclamation-backtick command executes immediately (before Claude sees anything)
2. The output replaces the placeholder in the skill content
3. Claude receives the fully-rendered prompt with actual data

This is preprocessing, not something Claude executes. Claude only sees the final result.

### Invocation Control

By default, both users and Claude can invoke any skill. Two frontmatter fields control this:

| Frontmatter | User can invoke | Claude can invoke | In context |
|-------------|-----------------|-------------------|------------|
| (default) | Yes | Yes | Description always visible |
| `disable-model-invocation: true` | Yes | No | Description hidden from Claude |
| `user-invocable: false` | No | Yes | Description always visible |

**When to use each:**

- **`disable-model-invocation: true`**: For workflows with side effects (deploy, commit, send-message). Prevents Claude from triggering automatically.
- **`user-invocable: false`**: For background knowledge that isn't a meaningful command (e.g., `legacy-system-context`). Claude should know this when relevant, but `/legacy-system-context` isn't useful for users.

### Subagent Integration

Add `context: fork` to run skills in isolation. The skill content becomes the subagent's prompt (no conversation history access).

```yaml
---
name: deep-research
description: Research a topic thoroughly
context: fork
agent: Explore
---

Research $ARGUMENTS thoroughly:
1. Find relevant files using Glob and Grep
2. Read and analyze the code
3. Summarize findings with specific file references
```

**Agent options:**

| Agent | Description |
|-------|-------------|
| `Explore` | Read-only codebase exploration (Glob, Grep, Read) |
| `Plan` | Architecture planning and design |
| `general-purpose` | Full capabilities (default) |
| Custom | Any agent from `.claude/agents/` |

**Note:** `context: fork` only makes sense for skills with explicit instructions. Guidelines-only skills (e.g., "use these API conventions") receive no actionable prompt and return without meaningful output.

### Skill Locations

Where a skill is stored determines who can use it:

| Location | Path | Applies to | Priority |
|----------|------|------------|----------|
| Enterprise | Managed settings | All org users | Highest |
| Personal | `~/.claude/skills/<name>/SKILL.md` | All your projects | High |
| Project | `.claude/skills/<name>/SKILL.md` | This project only | Medium |
| Plugin | `<plugin>/skills/<name>/SKILL.md` | Where plugin enabled | Namespaced |

When skills share the same name, higher-priority locations win. Plugin skills use `plugin-name:skill-name` namespace, so they cannot conflict.

**Nested discovery:** When editing files in subdirectories (e.g., `packages/frontend/`), Claude Code also discovers skills from nested `.claude/skills/` directories. This supports monorepos where packages have their own skills.

**Legacy commands:** Files in `.claude/commands/` still work with the same frontmatter. Skills are recommended since they support additional features like supporting files.

#### Bundled Resources (optional)

##### Scripts (`scripts/`)

**Content Type: Code** - Executable code (Python/Bash/etc.) for tasks that require deterministic reliability or are repeatedly rewritten.

- **When to include**: When the same code is being rewritten repeatedly or deterministic reliability is needed
- **Example**: `scripts/rotate_pdf.py` for PDF rotation tasks
- **Benefits**: Token efficient, deterministic, **script code never enters context - only output does**
- **Key advantage**: A 200-line script only costs ~20 tokens (the output), not 2000+ tokens (the code)
- **Note**: Scripts may still need to be read by Claude for patching or environment-specific adjustments

##### References (`references/`)

**Content Type: Instructions** - Documentation and reference material intended to be loaded as needed into context to inform Claude's process and thinking.

- **When to include**: For documentation that Claude should reference while working
- **Examples**: `references/finance.md` for financial schemas, `references/mnda.md` for company NDA template, `references/policies.md` for company policies, `references/api_docs.md` for API specifications
- **Use cases**: Database schemas, API documentation, domain knowledge, company policies, detailed workflow guides
- **Benefits**: Keeps SKILL.md lean, loaded only when Claude determines it's needed
- **Best practice**: If files are large (>10k words), include grep search patterns in SKILL.md
- **Avoid duplication**: Information should live in either SKILL.md or references files, not both. Prefer references files for detailed information unless it's truly core to the skill—this keeps SKILL.md lean while making information discoverable without hogging the context window. Keep only essential procedural instructions and workflow guidance in SKILL.md; move detailed reference material, schemas, and examples to references files.

##### Assets (`assets/`)

**Content Type: Resources** - Files not intended to be loaded into context, but rather used within the output Claude produces.

- **When to include**: When the skill needs files that will be used in the final output
- **Examples**: `assets/logo.png` for brand assets, `assets/slides.pptx` for PowerPoint templates, `assets/frontend-template/` for HTML/React boilerplate, `assets/font.ttf` for typography
- **Use cases**: Templates, images, icons, boilerplate code, fonts, sample documents that get copied or modified
- **Benefits**: Separates output resources from documentation, enables Claude to use files without loading them into context

### Progressive Disclosure Design Principle

Skills use a three-level loading system to manage context efficiently:

| Level | When Loaded | Token Cost | Content |
|-------|-------------|------------|---------|
| **Level 1: Metadata** | Always (at startup) | ~100 tokens per Skill | `name` and `description` from YAML frontmatter |
| **Level 2: Instructions** | When Skill is triggered | Under 5k tokens | SKILL.md body with instructions and guidance |
| **Level 3+: Resources** | As needed | Effectively unlimited* | Bundled files executed via bash without loading into context |

*Scripts are executed without loading code into context (only output enters context). Reference files and assets are loaded only when Claude explicitly accesses them via bash commands.

**Key insight**: You can install dozens of Skills with minimal context penalty. Claude only knows each Skill exists and when to use it until one is triggered.

**Context budget**: Skill descriptions are loaded into context so Claude knows what's available. If you have many skills, they may exceed the character budget (default 15,000 characters). Run `/context` to check for excluded skills. To increase the limit, set `SLASH_COMMAND_TOOL_CHAR_BUDGET` environment variable.

### The Skills Filesystem Architecture

Skills exist as directories on the local filesystem, and Claude interacts with them using bash commands and file operations.

**How Claude accesses Skill content:**

1. **Reading instructions**: When a Skill is triggered, Claude reads SKILL.md from the filesystem via bash, bringing its instructions into context
2. **Loading references**: If instructions reference other files (like `references/api_docs.md` or database schemas), Claude reads those files using additional bash commands
3. **Executing scripts**: When instructions mention executable scripts, Claude runs them via bash. **Only the script output enters context, not the code itself**

**What this enables:**

- **On-demand file access**: Claude reads only the files needed for each task. A Skill can include dozens of reference files, but if your task only needs one schema, Claude loads just that file. The rest consume zero tokens
- **Efficient script execution**: When Claude runs `validate_form.py`, only the output consumes tokens, not the 200-line script. This makes scripts far more efficient than having Claude generate equivalent code on the fly
- **No practical limit on bundled content**: Because files don't consume context until accessed, Skills can include comprehensive documentation, datasets, examples, or reference materials without context penalty

**Example workflow:**
```
1. User: "Process this PDF and extract tables"
2. Claude: bash: read pdf-skill/SKILL.md
3. SKILL.md mentions scripts/extract_tables.py
4. Claude: bash: python scripts/extract_tables.py input.pdf
5. Script output: "Extracted 3 tables: [table data...]"
6. Claude proceeds using the extracted data (script code never entered context)
```

## Skill Creation Process

To create a skill, follow the "Skill Creation Process" in order, skipping steps only if there is a clear reason why they are not applicable.

### Step 1: Understanding the Skill with Concrete Examples

Skip this step only when the skill's usage patterns are already clearly understood. It remains valuable even when working with an existing skill.

To create an effective skill, clearly understand concrete examples of how the skill will be used. This understanding can come from either direct user examples or generated examples that are validated with user feedback.

For example, when building an image-editor skill, relevant questions include:

- "What functionality should the image-editor skill support? Editing, rotating, anything else?"
- "Can you give some examples of how this skill would be used?"
- "I can imagine users asking for things like 'Remove the red-eye from this image' or 'Rotate this image'. Are there other ways you imagine this skill being used?"
- "What would a user say that should trigger this skill?"

To avoid overwhelming users, avoid asking too many questions in a single message. Start with the most important questions and follow up as needed for better effectiveness.

Conclude this step when there is a clear sense of the functionality the skill should support.

### Step 2: Planning the Reusable Skill Contents

To turn concrete examples into an effective skill, analyze each example by:

1. Considering how to execute on the example from scratch
2. Identifying what scripts, references, and assets would be helpful when executing these workflows repeatedly

Example: When building a `pdf-editor` skill to handle queries like "Help me rotate this PDF," the analysis shows:

1. Rotating a PDF requires re-writing the same code each time
2. A `scripts/rotate_pdf.py` script would be helpful to store in the skill

Example: When designing a `frontend-webapp-builder` skill for queries like "Build me a todo app" or "Build me a dashboard to track my steps," the analysis shows:

1. Writing a frontend webapp requires the same boilerplate HTML/React each time
2. An `assets/hello-world/` template containing the boilerplate HTML/React project files would be helpful to store in the skill

Example: When building a `big-query` skill to handle queries like "How many users have logged in today?" the analysis shows:

1. Querying BigQuery requires re-discovering the table schemas and relationships each time
2. A `references/schema.md` file documenting the table schemas would be helpful to store in the skill

To establish the skill's contents, analyze each concrete example to create a list of the reusable resources to include: scripts, references, and assets.

### Step 3: Initializing the Skill

At this point, it is time to actually create the skill.

Skip this step only if the skill being developed already exists, and iteration or packaging is needed. In this case, continue to the next step.

When creating a new skill from scratch, always run the `init_skill.py` script. The script conveniently generates a new template skill directory that automatically includes everything a skill requires, making the skill creation process much more efficient and reliable.

Usage:

```bash
scripts/init_skill.py <skill-name> --path <output-directory>
```

The script:

- Creates the skill directory at the specified path
- Generates a SKILL.md template with proper frontmatter and TODO placeholders
- Creates example resource directories: `scripts/`, `references/`, and `assets/`
- Adds example files in each directory that can be customized or deleted

After initialization, customize or remove the generated SKILL.md and example files as needed.

### Step 4: Edit the Skill

When editing the (newly-generated or existing) skill, remember that the skill is being created for another instance of Claude to use. Focus on including information that would be beneficial and non-obvious to Claude. Consider what procedural knowledge, domain-specific details, or reusable assets would help another Claude instance execute these tasks more effectively.

#### Start with Reusable Skill Contents

To begin implementation, start with the reusable resources identified above: `scripts/`, `references/`, and `assets/` files. Note that this step may require user input. For example, when implementing a `brand-guidelines` skill, the user may need to provide brand assets or templates to store in `assets/`, or documentation to store in `references/`.

Also, delete any example files and directories not needed for the skill. The initialization script creates example files in `scripts/`, `references/`, and `assets/` to demonstrate structure, but most skills won't need all of them.

#### Populating References from Documentation (Optional)

For skills based on existing frameworks, libraries, or tools with online documentation, use [Skill_Seekers](https://github.com/yusufkaraaslan/Skill_Seekers) (v2.0.0+) to automatically scrape and organize documentation into the `references/` directory. Skill_Seekers now supports unified multi-source scraping, combining documentation websites, GitHub repositories, and PDF files into comprehensive reference materials.

**When to use this approach:**
- Building skills for frameworks with comprehensive online docs (React, Django, FastAPI, etc.)
- Creating skills for game engines (Godot, Unity)
- Documenting APIs or libraries with web-based documentation
- Extracting API references directly from GitHub source code
- Combining multiple sources (docs + code + PDFs) for comprehensive skills
- Detecting discrepancies between documentation and actual implementation

**Quick Start:**

```bash
# One-time setup
git clone https://github.com/yusufkaraaslan/Skill_Seekers.git ~/Skill_Seekers
cd ~/Skill_Seekers
pip install requests beautifulsoup4

# Option 1: Documentation-only scraping (classic approach)
python3 cli/doc_scraper.py --config configs/react.json
cp -r output/react/references/* /path/to/your-skill/references/

# Option 2: GitHub-only scraping (extract API from source code)
python3 cli/github_scraper.py --repo facebook/react --extract-api
cp -r output/react_github/references/* /path/to/your-skill/references/

# Option 3: Unified multi-source scraping (RECOMMENDED)
# Combines documentation + GitHub code + PDFs into one comprehensive skill
python3 cli/unified_scraper.py --config configs/react_unified.json
cp -r output/react_complete/references/* /path/to/your-skill/references/

# Option 4: Custom unified config
python3 cli/config_validator.py configs/myframework_unified.json
python3 cli/unified_scraper.py --config configs/myframework_unified.json
```

**Alternative:** For simpler needs or when documentation is not web-based, manually create reference files in the `references/` directory.

For detailed Skill_Seekers documentation, see `references/documentation-scraping.md`.

#### Update SKILL.md

**Writing Style:** Write the entire skill using **imperative/infinitive form** (verb-first instructions), not second person. Use objective, instructional language (e.g., "To accomplish X, do Y" rather than "You should do X" or "If you need to do X"). This maintains consistency and clarity for AI consumption. Avoid ALL CAPS for emphasis — use bold markdown or section headings instead. Avoid CRITICAL/MANDATORY/MUST qualifiers; direct imperatives are sufficient for Claude 4.6.

To complete SKILL.md, answer the following questions:

1. What is the purpose of the skill, in a few sentences?
2. When should the skill be used?
3. In practice, how should Claude use the skill? All reusable skill contents developed above should be referenced so that Claude knows how to use them.

#### Skill Writing Philosophy

When writing skill instructions, follow these principles adapted from Anthropic's skill-creator research:

**Explain the "why" behind everything.** Instructions that explain reasoning produce better generalization than bare directives. "Validate output with the script because OCR errors are common in scanned documents" outperforms "Run the validation script." Claude generalizes the reasoning to novel situations the instructions don't cover.

**Keep the prompt lean.** Every token in SKILL.md competes for context with the user's actual task. Move reference material to `references/`, detailed examples to `assets/`, and repeated logic to `scripts/`. The skill body should contain only what Claude needs to decide *what to do*—not exhaustive detail on *how to do it*.

**Bundle repeated work into scripts.** When the same code appears across multiple test runs or eval transcripts, extract it into a script. Scripts are token-efficient (only output enters context), deterministic, and cacheable. Look for patterns across test cases to identify bundling opportunities.

**Make descriptions slightly "pushy."** Skills undertrigger more often than they overtrigger. Descriptions that actively claim territory ("This skill should be used when..." with specific trigger phrases) perform better than passive descriptions. Include keywords users would naturally say.

#### Claude 4.6 Prompting Alignment

When writing or reviewing skill instructions, follow these patterns:

**Language calibration:**
- Use direct imperatives without ALL CAPS emphasis. "Use Firecrawl for web scraping" not "ALWAYS use Firecrawl" or "You MUST use Firecrawl."
- Replace CRITICAL/MANDATORY/MUST markers with plain headings. Claude 4.6 follows well-structured instructions without coercive framing.
- Explain WHY behind directives. "Use --only-main-content to reduce token consumption" not "ALWAYS use --only-main-content." Claude generalizes better from explanations.

**Remove anti-laziness prompts:**
- Do not include "be thorough," "think carefully," "do not be lazy," or motivational framing. Claude 4.6 is already proactive — these amplify it into over-planning or write-then-rewrite loops.

**Subagent guidance (for orchestration skills):**
- Include explicit guidance on when NOT to spawn agents. Claude 4.6 tends to reach for subagents even when a direct approach is faster.
- "Use agents when tasks can run in parallel or require isolated context. For sequential tasks, single-file edits, or work completable in under 5 minutes, work directly."

**Overeagerness prevention:**
- Include guidance about minimal solutions. Factual quality criteria ("maintain existing conventions") outperform motivational framing ("fight entropy").

### Step 5: Packaging a Skill

Once the skill is ready, it should be packaged into a distributable zip file that gets shared with the user. The packaging process automatically validates the skill first to ensure it meets all requirements:

```bash
scripts/package_skill.py <path/to/skill-folder>
```

Optional output directory specification:

```bash
scripts/package_skill.py <path/to/skill-folder> ./dist
```

The packaging script will:

1. **Validate** the skill automatically, checking:
   - YAML frontmatter format and required fields
   - Skill naming conventions and directory structure
   - Description completeness and quality
   - File organization and resource references

2. **Package** the skill if validation passes, creating a zip file named after the skill (e.g., `my-skill.zip`) that includes all files and maintains the proper directory structure for distribution.

If validation fails, the script will report the errors and exit without creating a package. Fix any validation errors and run the packaging command again.

### Step 6: Testing & Evaluation

After packaging, test the skill systematically to measure its effectiveness. This step adapts Anthropic's eval framework for skill quality measurement.

#### Two Kinds of Skills

Before writing evals, identify which category the skill falls into—this determines eval strategy:

- **Capability uplift**: Helps Claude do something it cannot consistently do without the skill (e.g., fill PDF forms, generate specific file formats). Eval strategy: compare outputs with and without the skill.
- **Encoded preference**: Sequences workflow steps Claude can already do, but encodes specific preferences or domain knowledge (e.g., coding style guide, brand voice). Eval strategy: compare outputs against a human-reviewed gold standard.

#### Writing Evals

Create `evals/evals.json` in the skill directory with 2-5 realistic test prompts:

```json
{
  "skill_name": "example-skill",
  "evals": [
    {
      "id": 1,
      "prompt": "User's example prompt",
      "expected_output": "Description of expected result",
      "files": ["evals/files/sample1.pdf"],
      "expectations": [
        "The output includes X",
        "The skill used script Y"
      ]
    }
  ]
}
```

Each eval needs:
- A realistic prompt a user would actually say
- Optional input files (placed in `evals/files/`)
- A human-readable description of expected output
- 3-7 verifiable expectations that a grader can check against the output

Write expectations as specific, falsifiable statements—not vague quality judgments. "The output contains a table with 5 columns" is verifiable. "The output is well-formatted" is not.

#### Running Evals

Execute evals using the eval runner script:

```bash
# Run evals with the skill active
python3 scripts/run_eval.py --eval-set evals/evals.json --skill-path <skill-path>

# Run with multiple attempts per query for reliability
python3 scripts/run_eval.py --eval-set evals/evals.json --skill-path <skill-path> --runs-per-query 3
```

Each run produces an output directory with the skill's outputs, a transcript, and timing/token metrics.

#### Grading

After running evals, grade the outputs against expectations. The grader agent (`agents/grader.md`) evaluates each expectation as PASS/FAIL with evidence, extracts implicit claims from the output, and summarizes executor behavior from the transcript.

Grading produces `grading.json` with pass rates, execution metrics, and timing data. See `references/schemas.md` for the full schema.

#### Benchmarking

To aggregate results across multiple runs:

```bash
python3 scripts/aggregate_benchmark.py <benchmark-dir> --skill-path <skill-path>
```

This produces `benchmark.json` with statistical aggregates (mean, stddev) for pass_rate, timing, and token usage across with-skill and without-skill configurations. The analyzer agent (`agents/analyzer.md`) then surfaces patterns the aggregate metrics would hide—non-discriminating assertions, high-variance evals, and quality-vs-speed tradeoffs.

#### Reviewing Results

Launch the eval viewer for qualitative and quantitative review:

```bash
# Interactive server (auto-refreshes on new outputs)
python3 eval-viewer/generate_review.py <workspace-path>

# Static HTML export
python3 eval-viewer/generate_review.py <workspace-path> --static review.html

# With previous iteration context
python3 eval-viewer/generate_review.py <workspace-path> --previous-workspace <prev-workspace>

# With benchmark data
python3 eval-viewer/generate_review.py <workspace-path> --benchmark <benchmark.json>
```

The viewer has two tabs: **Outputs** (qualitative review with feedback per run) and **Benchmark** (quantitative pass rates, timing, and token charts).

#### Blind A/B Comparison

For comparing two skill versions, use the comparator agent (`agents/comparator.md`) which receives outputs labeled A and B without knowing which skill produced them. This prevents bias toward a particular approach. The comparator generates an evaluation rubric with Content and Structure dimensions, scores each output 1-5, and declares a winner.

After comparison, the analyzer agent unblinds the results and produces actionable improvement suggestions categorized by priority (high/medium/low) and type (instructions, tools, examples, error_handling, structure, references).

#### Version Tracking

Track improvement iterations in `history.json`:

```json
{
  "skill_name": "pdf",
  "current_best": "v2",
  "iterations": [
    {"version": "v0", "parent": null, "expectation_pass_rate": 0.65, "grading_result": "baseline"},
    {"version": "v1", "parent": "v0", "expectation_pass_rate": 0.75, "grading_result": "won"},
    {"version": "v2", "parent": "v1", "expectation_pass_rate": 0.85, "grading_result": "won"}
  ]
}
```

### Step 7: Description Optimization

Skill descriptions determine when Claude uses the skill. A weak description causes undertriggering (skill not invoked when it should be) or overtriggering (skill invoked when it should not be). This step systematically optimizes the description.

#### Generate Trigger Eval Queries

Create 20 test queries: 10 that should trigger the skill and 10 that should not. Include realistic edge cases—queries that are close to the skill's domain but should not trigger it.

For a `pdf-editor` skill, examples:
- **Should trigger**: "Rotate this PDF 90 degrees", "Merge these three PDFs", "Extract page 5 from this document"
- **Should not trigger**: "Read this PDF and summarize it", "Convert this Word doc to PDF", "What does this PDF contain?"

#### Run the Optimization Loop

```bash
python3 scripts/run_loop.py \
  --eval-set trigger-queries.json \
  --skill-path <skill-path> \
  --holdout 0.4 \
  --runs-per-query 3 \
  --max-iterations 5 \
  --model sonnet
```

The loop:
1. Splits queries into 60% train / 40% test
2. Runs each query 3 times for reliability (majority vote)
3. Analyzes failures on the training set
4. Generates an improved description using extended thinking
5. Evaluates on the held-out test set
6. Repeats until convergence or max iterations

#### Review and Adopt

The loop produces an HTML report showing accuracy progression across iterations. Review the final description—it should be specific enough to avoid overtriggering but inclusive enough to catch legitimate use cases.

If the optimized description improves test-set accuracy, update the skill's YAML frontmatter `description` field. If accuracy plateaus or regresses, keep the current description and investigate whether the trigger queries themselves need refinement.

### Step 8: Iterate

After testing the skill, users may request improvements. Often this happens right after using the skill, with fresh context of how the skill performed.

**Iteration workflow:**
1. Use the skill on real tasks
2. Notice struggles or inefficiencies
3. Identify how SKILL.md or bundled resources should be updated
4. Implement changes and test again

## Sharing Skills

Skills can be distributed at different scopes:

- **Project skills**: Commit `.claude/skills/` to version control
- **Plugins**: Create a `skills/` directory in your [plugin](https://code.claude.com/docs/en/plugins)
- **Managed**: Deploy organization-wide through [managed settings](https://code.claude.com/docs/en/iam#managed-settings)

## Troubleshooting

### Skill not triggering

If Claude doesn't use a skill when expected:

1. Check the description includes keywords users would naturally say
2. Verify the skill appears in response to "What skills are available?"
3. Try rephrasing the request to match the description more closely
4. Invoke it directly with `/skill-name` if the skill is user-invocable

### Skill triggers too often

If Claude uses a skill when not wanted:

1. Make the description more specific
2. Add `disable-model-invocation: true` if only manual invocation is wanted

### Claude doesn't see all skills

Skill descriptions are loaded into context. If there are many skills, they may exceed the character budget (default 15,000 characters). Run `/context` to check for a warning about excluded skills.

To increase the limit, set the `SLASH_COMMAND_TOOL_CHAR_BUDGET` environment variable.

## Related Resources

- **[Subagents](https://code.claude.com/docs/en/sub-agents)**: Delegate tasks to specialized agents
- **[Plugins](https://code.claude.com/docs/en/plugins)**: Package and distribute skills with other extensions
- **[Hooks](https://code.claude.com/docs/en/hooks)**: Automate workflows around tool events
- **[Memory](https://code.claude.com/docs/en/memory)**: Manage CLAUDE.md files for persistent context
- **[Permissions](https://code.claude.com/docs/en/iam)**: Control tool and skill access
