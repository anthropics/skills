# The Complete Guide to Building Skills for Claude

---

## Contents

- [Introduction](#introduction)
- [Chapter 1: Fundamentals](#chapter-1-fundamentals)
- [Chapter 2: Planning and Design](#chapter-2-planning-and-design)
- [Chapter 3: Testing and Iteration](#chapter-3-testing-and-iteration)
- [Chapter 4: Distribution and Sharing](#chapter-4-distribution-and-sharing)
- [Chapter 5: Patterns and Troubleshooting](#chapter-5-patterns-and-troubleshooting)
- [Chapter 6: Resources and References](#chapter-6-resources-and-references)
- [Reference A: Quick Checklist](#reference-a-quick-checklist)
- [Reference B: YAML Frontmatter](#reference-b-yaml-frontmatter)
- [Reference C: Complete Skill Examples](#reference-c-complete-skill-examples)

---

## Introduction

A skill is a set of instructions - packaged as a simple folder - that teaches Claude how to handle specific tasks or workflows. Skills are one of the most powerful ways to customize Claude for your specific needs. Instead of re-explaining your preferences, processes, and domain expertise in every conversation, skills let you teach Claude once and benefit every time.

Skills are powerful when you have repeatable workflows: generating frontend designs from specs, conducting research with consistent methodology, creating documents that follow your team's style guide, or orchestrating multi-step processes. They work well with Claude's built-in capabilities like code execution and document creation. For those building MCP integrations, skills add another powerful layer helping turn raw tool access into reliable, optimized workflows.

This guide covers everything you need to know to build effective skills - from planning and structure to testing and distribution. Whether you're building a skill for yourself, your team, or for the community, you'll find practical patterns and real-world examples throughout.

**What you'll learn:**

- Technical requirements and best practices for skill structure
- Patterns for standalone skills and MCP-enhanced workflows
- Patterns we've seen work well across different use cases
- How to test, iterate, and distribute your skills

**Who this is for:**

- Developers who want Claude to follow specific workflows consistently
- Power users who want Claude to follow specific workflows
- Teams looking to standardize how Claude works across their organization

**Two Paths Through This Guide**

Building standalone skills? Focus on Fundamentals, Planning and Design, and category 1-2. Enhancing an MCP integration? The "Skills + MCP" section and category 3 are for you. Both paths share the same technical requirements, but you choose what's relevant to your use case.

What you'll get out of this guide: By the end, you'll be able to build a functional skill in a single sitting. Expect about 15-30 minutes to build and test your first working skill using the skill-creator.

---

## Chapter 1: Fundamentals

### What is a skill?

A skill is a folder containing:

- `SKILL.md` (required): Instructions in Markdown with YAML frontmatter
- `scripts/` (optional): Executable code (Python, Bash, etc.)
- `references/` (optional): Documentation loaded as needed
- `assets/` (optional): Templates, fonts, icons used in output

### Core design principles

#### Progressive Disclosure

Skills use a three-level system:

- **First level (YAML frontmatter):** Always loaded in Claude's system prompt. Provides just enough information for Claude to know when each skill should be used without loading all of it into context.
- **Second level (SKILL.md body):** Loaded when Claude thinks the skill is relevant to the current task. Contains the full instructions and guidance.
- **Third level (Linked files):** Additional files bundled within the skill directory that Claude can choose to navigate and discover only as needed.

This progressive disclosure minimizes token usage while maintaining specialized expertise.

#### Composability

Claude can load multiple skills simultaneously. Your skill should work well alongside others, not assume it's the only capability available.

#### Portability

Skills work identically across Claude.ai, Claude Code, and API. Create a skill once and it works across all surfaces without modification, provided the environment supports any dependencies the skill requires.

---

### For MCP Builders: Skills + Connectors

> 💡 Building standalone skills without MCP? Skip to Planning and Design - you can always return here later.

If you already have a [working MCP server](https://support.claude.com/en/articles/10949351-getting-started-with-local-mcp-servers-on-claude-desktop), you've done the hard part. Skills are the knowledge layer on top - capturing the workflows and best practices you already know, so Claude can apply them consistently.

**The kitchen analogy**

MCP provides the professional kitchen: access to tools, ingredients, and equipment.
Skills provide the recipes: step-by-step instructions on how to create something valuable.

Together, they enable users to accomplish complex tasks without needing to figure out every step themselves.

**How they work together:**

| MCP (Connectivity)                                            | Skills (Knowledge)                                 |
| ------------------------------------------------------------- | -------------------------------------------------- |
| Connects Claude to your service (Notion, Asana, Linear, etc.) | Teaches Claude how to use your service effectively |
| Provides real-time data access and tool invocation            | Captures workflows and best practices              |
| What Claude can do                                            | How Claude should do it                            |

**Why this matters for your MCP users**

Without skills:

- Users connect your MCP but don't know what to do next
- Support tickets asking "how do I do X with your integration"
- Each conversation starts from scratch
- Inconsistent results because users prompt differently each time
- Users blame your connector when the real issue is workflow guidance

With skills:

- Pre-built workflows activate automatically when needed
- Consistent, reliable tool usage
- Best practices embedded in every interaction
- Lower learning curve for your integration

---

## Chapter 2: Planning and Design

### Start with use cases

Before writing any code, identify 2-3 concrete use cases your skill should enable.

**Good use case definition:**

```
Use Case: Project Sprint Planning
Trigger: User says "help me plan this sprint" or "create sprint tasks"
Steps:
  1. Fetch current project status from Linear (via MCP)
  2. Analyze team velocity and capacity
  3. Suggest task prioritization
  4. Create tasks in Linear with proper labels and estimates
Result: Fully planned sprint with tasks created
```

Ask yourself:

- What does a user want to accomplish?
- What multi-step workflows does this require?
- Which tools are needed (built-in or MCP)?
- What domain knowledge or best practices should be embedded?

---

### Common skill use case categories

At Anthropic, we've observed three common use cases:

#### Category 1: Document & Asset Creation

Used for: Creating consistent, high-quality output including documents, presentations, apps, designs, code, etc.

Real example: [`frontend-design skill`](https://github.com/anthropics/skills/tree/main/skills/frontend-design)  (also see [skills for docx, pptx, xlsx, and ppt](https://github.com/anthropics/skills/tree/main/skills))

> "Create distinctive, production-grade frontend interfaces with high design quality. Use when building web components, pages, artifacts, posters, or applications."

Key techniques:

- Embedded style guides and brand standards
- Template structures for consistent output
- Quality checklists before finalizing
- No external tools required - uses Claude's built-in capabilities

#### Category 2: Workflow Automation

Used for: Multi-step processes that benefit from consistent methodology, including coordination across multiple MCP servers.

Real example: [`skill-creator`](https://github.com/anthropics/skills/blob/main/skills/skill-creator/SKILL.md) *(→ Appendix A13)* skill

> "Interactive guide for creating new skills. Walks the user through use case definition, frontmatter generation, instruction writing, and validation."

Key techniques:

- Step-by-step workflow with validation gates
- Templates for common structures
- Built-in review and improvement suggestions
- Iterative refinement loops

#### Category 3: MCP Enhancement

Used for: Workflow guidance to enhance the tool access an MCP server provides.

Real example: [`sentry-code-review` skill (from Sentry)](https://github.com/getsentry/sentry-for-claude/tree/main/skills) *(→ Appendix A14)*

> "Automatically analyzes and fixes detected bugs in GitHub Pull Requests using Sentry's error monitoring data via their MCP server."

Key techniques:

- Coordinates multiple MCP calls in sequence
- Embeds domain expertise
- Provides context users would otherwise need to specify
- Error handling for common MCP issues

---

### Define success criteria

How will you know your skill is working?

These are aspirational targets - rough benchmarks rather than precise thresholds. Aim for rigor but accept that there will be an element of vibes-based assessment. We are actively developing more robust measurement guidance and tooling.

**Quantitative metrics:**

- **Skill triggers on 90% of relevant queries**
  - How to measure: Run 10-20 test queries that should trigger your skill. Track how many times it loads automatically vs. requires explicit invocation.
- **Completes workflow in X tool calls**
  - How to measure: Compare the same task with and without the skill enabled. Count tool calls and total tokens consumed.
- **0 failed API calls per workflow**
  - How to measure: Monitor MCP server logs during test runs. Track retry rates and error codes.

**Qualitative metrics:**

- **Users don't need to prompt Claude about next steps**
  - How to assess: During testing, note how often you need to redirect or clarify. Ask beta users for feedback.
- **Workflows complete without user correction**
  - How to assess: Run the same request 3-5 times. Compare outputs for structural consistency and quality.
- **Consistent results across sessions**
  - How to assess: Can a new user accomplish the task on first try with minimal guidance?

---

### Technical requirements

#### File structure

```
your-skill-name/
├── SKILL.md           # Required - main skill file
├── scripts/           # Optional - executable code
│   ├── process_data.py
│   └── validate.sh
├── references/        # Optional - documentation
│   ├── api-guide.md
│   └── examples/
└── assets/            # Optional - templates, etc.
    └── report-template.md
```

#### Critical rules

**SKILL.md naming:**

- Must be exactly `SKILL.md` (case-sensitive)
- No variations accepted (`SKILL.MD`, `skill.md`, etc.)

**Skill folder naming:**

- Use kebab-case: `notion-project-setup` ✅
- No spaces: `Notion Project Setup` ❌
- No underscores: `notion_project_setup` ❌
- No capitals: `NotionProjectSetup` ❌

**No README.md:**

- Don't include `README.md` inside your skill folder
- All documentation goes in `SKILL.md` or `references/`
- Note: when distributing via GitHub, you'll still want a repo-level README for human users — see Distribution and Sharing.

---

### YAML frontmatter: The most important part

The YAML frontmatter is how Claude decides whether to load your skill. Get this right.

**Minimal required format:**

```yaml
---
name: your-skill-name
description: What it does. Use when user asks to [specific phrases].
---
```

That's all you need to start.

**Field requirements:**

`name` (required):

- kebab-case only
- No spaces or capitals
- Should match folder name

`description` (required):

- MUST include BOTH: what the skill does AND when to use it (trigger conditions)
- Under 1024 characters
- No XML tags (`<` or `>`)
- Include specific tasks users might say
- Mention file types if relevant

`license` (optional):

- Use if making skill open source
- Common: `MIT`, `Apache-2.0`

`compatibility` (optional):

- 1-500 characters
- Indicates environment requirements: e.g. intended product, required system packages, network access needs, etc.

`metadata` (optional):

- Any custom key-value pairs
- Suggested: `author`, `version`, `mcp-server`

```yaml
metadata:
  author: ProjectHub
  version: 1.0.0
  mcp-server: projecthub
```

**Security restrictions**

Forbidden in frontmatter:

- XML angle brackets (`< >`)
- Skills with "claude" or "anthropic" in name (reserved)

Why: Frontmatter appears in Claude's system prompt. Malicious content could inject instructions.

---

### Writing effective skills

#### The description field

According to Anthropic's [engineering blog](https://www.anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills) *(→ Appendix A1)*: "This metadata...provides just enough information for Claude to know when each skill should be used without loading all of it into context." This is the first level of progressive disclosure.

Structure: `[What it does] + [When to use it] + [Key capabilities]`

**Examples of good descriptions:**

```yaml
# Good - specific and actionable
description: Analyzes Figma design files and generates developer handoff
  documentation. Use when user uploads .fig files, asks for "design specs",
  "component documentation", or "design-to-code handoff".

# Good - includes trigger phrases
description: Manages Linear project workflows including sprint planning, task
  creation, and status tracking. Use when user mentions "sprint", "Linear tasks",
  "project planning", or asks to "create tickets".

# Good - clear value proposition
description: End-to-end customer onboarding workflow for PayFlow. Handles account
  creation, payment setup, and subscription management. Use when user says
  "onboard new customer", "set up subscription", or "create PayFlow account".
```

**Examples of bad descriptions:**

```yaml
# Too vague
description: Helps with projects.

# Missing triggers
description: Creates sophisticated multi-page documentation systems.

# Too technical, no user triggers
description: Implements the Project entity model with hierarchical relationships.
```

---

#### Writing the main instructions

After the frontmatter, write the actual instructions in Markdown.

**Recommended structure:**

```markdown
---
name: your-skill
description: [...]
---

# Your Skill Name

## Instructions

### Step 1: [First Major Step]

Clear explanation of what happens.

Example:
```bash
python scripts/fetch_data.py --project-id PROJECT_ID
```

Expected output: [describe what success looks like]

(Add more steps as needed)

## Examples

### Example 1: [common scenario]

User says: "Set up a new marketing campaign"

Actions:

1. Fetch existing campaigns via MCP
2. Create new campaign with provided parameters

Result: Campaign created with confirmation link

(Add more examples as needed)

## Troubleshooting

**Error:** [Common error message]
**Cause:** [Why it happens]
**Solution:** [How to fix]

(Add more error cases as needed)

```
#### Best Practices for Instructions

**Be Specific and Actionable**

✅ Good:
```

Run `python scripts/validate.py --input {filename}` to check data format.
If validation fails, common issues include:

- Missing required fields (add them to the CSV)

- Invalid date formats (use YYYY-MM-DD)
  
  ```
  
  ```

❌ Bad:

```
Validate the data before proceeding.
```

**Include error handling:**

```markdown
## Common Issues

### MCP Connection Failed

If you see "Connection refused":
1. Verify MCP server is running: Check Settings > Extensions
2. Confirm API key is valid
3. Try reconnecting: Settings > Extensions > [Your Service] > Reconnect
```

**Reference bundled resources clearly:**

```
Before writing queries, consult `references/api-patterns.md` for:
- Rate limiting guidance
- Pagination patterns
- Error codes and handling
```

**Use progressive disclosure:** Keep `SKILL.md` focused on core instructions. Move detailed documentation to `references/` and link to it. (See [Core Design Principles](https://www.anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills) *(→ Appendix A1)* for how the three-level system works.)

---

## Chapter 3: Testing and Iteration

Skills can be tested at varying levels of rigor depending on your needs:

- **Manual testing in Claude.ai** - Run queries directly and observe behavior. Fast iteration, no setup required.
- **Scripted testing in Claude Code** - Automate test cases for repeatable validation across changes.
- **Programmatic testing via skills API** - Build evaluation suites that run systematically against defined test sets.

Choose the approach that matches your quality requirements and the visibility of your skill. A skill used internally by a small team has different testing needs than one deployed to thousands of enterprise users.

> **Pro Tip: Iterate on a single task before expanding**
> We've found that the most effective skill creators iterate on a single challenging task until Claude succeeds, then extract the winning approach into a skill. This leverages Claude's in-context learning and provides faster signal than broad testing. Once you have a working foundation, expand to multiple test cases for coverage.

---

### Recommended Testing Approach

Based on early experience, effective skills testing typically covers three areas:

#### 1. Triggering tests

Goal: Ensure your skill loads at the right times.

Test cases:

- ✅ Triggers on obvious tasks
- ✅ Triggers on paraphrased requests
- ❌ Doesn't trigger on unrelated topics

Example test suite:

```
Should trigger:
- "Help me set up a new ProjectHub workspace"
- "I need to create a project in ProjectHub"
- "Initialize a ProjectHub project for Q4 planning"

Should NOT trigger:
- "What's the weather in San Francisco?"
- "Help me write Python code"
- "Create a spreadsheet" (unless ProjectHub skill handles sheets)
```

#### 2. Functional tests

Goal: Verify the skill produces correct outputs.

Test cases:

- Valid outputs generated
- API calls succeed
- Error handling works
- Edge cases covered

Example:

```
Test: Create project with 5 tasks
Given: Project name "Q4 Planning", 5 task descriptions
When: Skill executes workflow
Then:
  - Project created in ProjectHub
  - 5 tasks created with correct properties
  - All tasks linked to project
  - No API errors
```

#### 3. Performance comparison

Goal: Prove the skill improves results vs. baseline.

Use the metrics from Define Success Criteria. Here's what a comparison might look like:

```
Without skill:
- User provides instructions each time
- 15 back-and-forth messages
- 3 failed API calls requiring retry
- 12,000 tokens consumed

With skill:
- Automatic workflow execution
- 2 clarifying questions only
- 0 failed API calls
- 6,000 tokens consumed
```

---

### Using the skill-creator skill

The `skill-creator` skill - available in Claude.ai via plugin directory or download for Claude Code - can help you build and iterate on skills. If you have an MCP server and know your top 2-3 workflows, you can build and test a functional skill in a single sitting - often in 15-30 minutes.

**Creating skills:**

- Generate skills from natural language descriptions
- Produce properly formatted `SKILL.md` with frontmatter
- Suggest trigger phrases and structure

**Reviewing skills:**

- Flag common issues (vague descriptions, missing triggers, structural problems)
- Identify potential over/under-triggering risks
- Suggest test cases based on the skill's stated purpose

**Iterative improvement:**

- After using your skill and encountering edge cases or failures, bring those examples back to skill-creator
- Example: "Use the issues & solution identified in this chat to improve how the skill handles [specific edge case]"

To use:

```
"Use the skill-creator skill to help me build a skill for [your use case]"
```

> **Note:** `skill-creator` helps you design and refine skills but does not execute automated test suites or produce quantitative evaluation results.

---

### Iteration based on feedback

Skills are living documents. Plan to iterate based on:

**Undertriggering signals:**

- Skill doesn't load when it should
- Users manually enabling it
- Support questions about when to use it

Solution: Add more detail and nuance to the description - this may include keywords particularly for technical terms.

**Overtriggering signals:**

- Skill loads for irrelevant queries
- Users disabling it
- Confusion about purpose

Solution: Add negative triggers, be more specific.

**Execution issues:**

- Inconsistent results
- API call failures
- User corrections needed

Solution: Improve instructions, add error handling.

---

## Chapter 4: Distribution and Sharing

Skills make your MCP integration more complete. As users compare connectors, those with skills offer a faster path to value, giving you an edge over MCP-only alternatives.

### Current distribution model (January 2026)

**How individual users get skills:**

1. Download the skill folder
2. Zip the folder (if needed)
3. Upload to Claude.ai via Settings > Capabilities > Skills
4. Or place in Claude Code skills directory

**Organization-level skills:**

- Admins can deploy skills workspace-wide (shipped December 18, 2025)
- Automatic updates
- Centralized management

---

### An open standard

We've published [Agent Skills](https://agentskills.io/home) *(→ Appendix A16)* as an open standard. Like MCP, we believe skills should be portable across tools and platforms - the same skill should work whether you're using Claude or other AI platforms. That said, some skills are designed to take full advantage of a specific platform's capabilities; authors can note this in the skill's `compatibility` field. We've been collaborating with members of the ecosystem on the standard, and we're excited by early adoption.

---

### Using skills via API

For programmatic use cases - such as building applications, agents, or automated workflows that leverage skills - the API provides direct control over skill management and execution.

Key capabilities:

- `/v1/skills` endpoint for listing and managing skills
- Add skills to Messages API requests via the `container.skills` parameter
- Version control and management through the Claude Console
- Works with the Claude Agent SDK for building custom agents

**When to use skills via the API vs. Claude.ai:**

| Use Case                                        | Best Surface            |
| ----------------------------------------------- | ----------------------- |
| End users interacting with skills directly      | Claude.ai / Claude Code |
| Manual testing and iteration during development | Claude.ai / Claude Code |
| Individual, ad-hoc workflows                    | Claude.ai / Claude Code |
| Applications using skills programmatically      | API                     |
| Production deployments at scale                 | API                     |
| Automated pipelines and agent systems           | API                     |

> **Note:** Skills in the API require the Code Execution Tool beta, which provides the secure environment skills need to run.

For implementation details, see:

- [Skills API Quickstart](https://docs.claude.com/en/docs/agents-and-tools/agent-skills/quickstart) *(→ Appendix A10)*
- [Create Custom skills](https://docs.claude.com/en/api/skills/create-skill) *(→ Appendix A10)*
- [Skills in the Agent SDK](https://docs.claude.com/en/docs/agent-sdk/skills) *(→ Appendix A11)*

---

### Recommended approach today

Start by hosting your skill on GitHub with a public repo, clear README (for human visitors — this is separate from your skill folder, which should not contain a `README.md`), and example usage with screenshots. Then add a section to your MCP documentation that links to the skill, explains why using both together is valuable, and provides a quick-start guide.

**1. Host on GitHub**

- Public repo for open-source skills
- Clear README with installation instructions
- Example usage and screenshots

**2. Document in Your MCP Repo**

- Link to skills from MCP documentation
- Explain the value of using both together
- Provide quick-start guide

**3. Create an Installation Guide**

```markdown
# Installing the [Your Service] skill

1. Download the skill:
   - Clone repo: `git clone https://github.com/yourcompany/skills`
   - Or download ZIP from Releases

2. Install in Claude:
   - Open Claude.ai > Settings > Skills
   - Click "Upload skill"
   - Select the skill folder (zipped)

3. Enable the skill:
   - Toggle on the [Your Service] skill
   - Ensure your MCP server is connected

4. Test:
   - Ask Claude: "Set up a new project in [Your Service]"
```

---

### Positioning your skill

How you describe your skill determines whether users understand its value and actually try it. When writing about your skill—in your README, documentation, or marketing—keep these principles in mind.

**Focus on outcomes, not features:**

✅ Good:

> "The ProjectHub skill enables teams to set up complete project workspaces in seconds — including pages, databases, and templates — instead of spending 30 minutes on manual setup."

❌ Bad:

> "The ProjectHub skill is a folder containing YAML frontmatter and Markdown instructions that calls our MCP server tools."

**Highlight the MCP + skills story:**

> "Our MCP server gives Claude access to your Linear projects. Our skills teach Claude your team's sprint planning workflow. Together, they enable AI-powered project management."

---

## Chapter 5: Patterns and Troubleshooting

These patterns emerged from skills created by early adopters and internal teams. They represent common approaches we've seen work well, not prescriptive templates.

### Choosing your approach: Problem-first vs. tool-first

Think of it like Home Depot. You might walk in with a problem - "I need to fix a kitchen cabinet" - and an employee points you to the right tools. Or you might pick out a new drill and ask how to use it for your specific job.

Skills work the same way:

- **Problem-first:** "I need to set up a project workspace" → Your skill orchestrates the right MCP calls in the right sequence. Users describe outcomes; the skill handles the tools.
- **Tool-first:** "I have Notion MCP connected" → Your skill teaches Claude the optimal workflows and best practices. Users have access; the skill provides expertise.

Most skills lean one direction. Knowing which framing fits your use case helps you choose the right pattern below.

---

### Pattern 1: Sequential workflow orchestration

**Use when:** Your users need multi-step processes in a specific order.

Example structure:

```markdown
# Workflow: Onboard New Customer

## Step 1: Create Account
Call MCP tool: `create_customer`
Parameters: name, email, company

## Step 2: Setup Payment
Call MCP tool: `setup_payment_method`
Wait for: payment method verification

## Step 3: Create Subscription
Call MCP tool: `create_subscription`
Parameters: plan_id, customer_id (from Step 1)

## Step 4: Send Welcome Email
Call MCP tool: `send_email`
Template: welcome_email_template
```

Key techniques:

- Explicit step ordering
- Dependencies between steps
- Validation at each stage
- Rollback instructions for failures

---

### Pattern 2: Multi-MCP coordination

**Use when:** Workflows span multiple services.

Example: Design-to-development handoff

```markdown
# Phase 1: Design Export (Figma MCP)
1. Export design assets from Figma
2. Generate design specifications
3. Create asset manifest

# Phase 2: Asset Storage (Drive MCP)
1. Create project folder in Drive
2. Upload all assets
3. Generate shareable links

# Phase 3: Task Creation (Linear MCP)
1. Create development tasks
2. Attach asset links to tasks
3. Assign to engineering team

# Phase 4: Notification (Slack MCP)
1. Post handoff summary to #engineering
2. Include asset links and task references
```

Key techniques:

- Clear phase separation
- Data passing between MCPs
- Validation before moving to next phase
- Centralized error handling

---

### Pattern 3: Iterative refinement

**Use when:** Output quality improves with iteration.

Example: Report generation

```markdown
# Iterative Report Creation

## Initial Draft
1. Fetch data via MCP
2. Generate first draft report
3. Save to temporary file

## Quality Check
1. Run validation script: `scripts/check_report.py`
2. Identify issues:
   - Missing sections
   - Inconsistent formatting
   - Data validation errors

## Refinement Loop
1. Address each identified issue
2. Regenerate affected sections
3. Re-validate
4. Repeat until quality threshold met

## Finalization
1. Apply final formatting
2. Generate summary
3. Save final version
```

Key techniques:

- Explicit quality criteria
- Iterative improvement
- Validation scripts
- Know when to stop iterating

---

### Pattern 4: Context-aware tool selection

**Use when:** Same outcome, different tools depending on context.

Example: File storage

```markdown
# Smart File Storage

## Decision Tree
1. Check file type and size
2. Determine best storage location:
   - Large files (>10MB): Use cloud storage MCP
   - Collaborative docs: Use Notion/Docs MCP
   - Code files: Use GitHub MCP
   - Temporary files: Use local storage

## Execute Storage
Based on decision:
- Call appropriate MCP tool
- Apply service-specific metadata
- Generate access link

## Provide Context to User
Explain why that storage was chosen
```

Key techniques:

- Clear decision criteria
- Fallback options
- Transparency about choices

---

### Pattern 5: Domain-specific intelligence

**Use when:** Your skill adds specialized knowledge beyond tool access.

Example: Financial compliance

```markdown
# Payment Processing with Compliance

## Before Processing (Compliance Check)
1. Fetch transaction details via MCP
2. Apply compliance rules:
   - Check sanctions lists
   - Verify jurisdiction allowances
   - Assess risk level
3. Document compliance decision

## Processing
IF compliance passed:
  - Call payment processing MCP tool
  - Apply appropriate fraud checks
  - Process transaction
ELSE:
  - Flag for review
  - Create compliance case

## Audit Trail
- Log all compliance checks
- Record processing decisions
- Generate audit report
```

Key techniques:

- Domain expertise embedded in logic
- Compliance before action
- Comprehensive documentation
- Clear governance

---

### Troubleshooting

#### Skill won't upload

**Error:** `"Could not find SKILL.md in uploaded folder"`
**Cause:** File not named exactly `SKILL.md`
**Solution:** Rename to `SKILL.md` (case-sensitive). Verify with: `ls -la` should show `SKILL.md`.

**Error:** `"Invalid frontmatter"`
**Cause:** YAML formatting issue

Common mistakes:

```yaml
# Wrong - missing delimiters
name: my-skill
description: Does things

# Wrong - unclosed quotes
name: my-skill
description: "Does things

# Correct
---
name: my-skill
description: Does things
---
```

**Error:** `"Invalid skill name"`
**Cause:** Name has spaces or capitals

```yaml
# Wrong
name: My Cool Skill

# Correct
name: my-cool-skill
```

---

#### Skill doesn't trigger

**Symptom:** Skill never loads automatically

**Fix:** Revise your description field. See The Description Field for good/bad examples.

Quick checklist:

- Is it too generic? ("Helps with projects" won't work)
- Does it include trigger phrases users would actually say?
- Does it mention relevant file types if applicable?

**Debugging approach:** Ask Claude: "When would you use the [skill name] skill?" Claude will quote the description back. Adjust based on what's missing.

---

#### Skill triggers too often

**Symptom:** Skill loads for unrelated queries

**Solutions:**

1. Add negative triggers:
   
   ```yaml
   description: Advanced data analysis for CSV files. Use for statistical modeling,
   regression, clustering. Do NOT use for simple data exploration (use data-viz
   skill instead).
   ```

2. Be more specific:
   
   ```yaml
   # Too broad
   description: Processes documents
   ```

# More specific

description: Processes PDF legal documents for contract review

```
3. Clarify scope:
```yaml
description: PayFlow payment processing for e-commerce. Use specifically for
  online payment workflows, not for general financial queries.
```

---

#### MCP connection issues

**Symptom:** Skill loads but MCP calls fail

Checklist:

1. Verify MCP server is connected — Claude.ai: Settings > Extensions > [Your Service] — Should show "Connected" status
2. Check authentication — API keys valid and not expired — Proper permissions/scopes granted — OAuth tokens refreshed
3. Test MCP independently — Ask Claude to call MCP directly (without skill): "Use [Service] MCP to fetch my projects" — If this fails, issue is MCP not skill
4. Verify tool names — Skill references correct MCP tool names — Check MCP server documentation — Tool names are case-sensitive

---

#### Instructions not followed

**Symptom:** Skill loads but Claude doesn't follow instructions

Common causes:

1. **Instructions too verbose** — Keep instructions concise — Use bullet points and numbered lists — Move detailed reference to separate files

2. **Instructions buried** — Put critical instructions at the top — Use `## Important` or `## Critical` headers — Repeat key points if needed

3. **Ambiguous language:**

```markdown
# Bad
Make sure to validate things properly

# Good
CRITICAL: Before calling create_project, verify:
- Project name is non-empty
- At least one team member assigned
- Start date is not in the past
```

> **Advanced technique:** For critical validations, consider bundling a script that performs the checks programmatically rather than relying on language instructions. Code is deterministic; language interpretation isn't. See the [Office skills](https://github.com/anthropics/skills/tree/main/skills) for examples of this pattern.

4. **Model "laziness"** — Add explicit encouragement:

```markdown
## Performance Notes
- Take your time to do this thoroughly
- Quality is more important than speed
- Do not skip validation steps
```

> Note: Adding this to user prompts is more effective than in `SKILL.md`.

---

#### Large context issues

**Symptom:** Skill seems slow or responses degraded

Causes:

- Skill content too large
- Too many skills enabled simultaneously
- All content loaded instead of progressive disclosure

Solutions:

1. Optimize `SKILL.md` size — Move detailed docs to `references/` — Link to references instead of inline — Keep `SKILL.md` under 5,000 words

2. Reduce enabled skills — Evaluate if you have more than 20-50 skills enabled simultaneously — Recommend selective enablement — Consider skill "packs" for related capabilities

---

## Chapter 6: Resources and References

If you're building your first skill, start with the Best Practices Guide, then reference the API docs as needed.

### Official Documentation

**Anthropic Resources:**

- [Best Practices Guide](https://platform.claude.com/docs/en/agents-and-tools/agent-skills/best-practices) *(→ Appendix A9)*
- [Skills Documentation](https://platform.claude.com/docs/en/agents-and-tools/agent-skills/overview) *(→ Appendix A8)*
- [API Reference](https://platform.claude.com/docs/en/api/overview)
- [MCP Documentation](https://modelcontextprotocol.io)

**Blog Posts:**

- [Introducing Agent Skills](https://claude.com/blog/skills) *(→ Appendix A2)*
- [Engineering Blog: Equipping Agents for the Real World](https://www.anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)
- [Skills Explained](https://www.claude.com/blog/skills-explained) *(→ Appendix A3)*
- [How to Create Skills for Claude](https://www.claude.com/blog/how-to-create-skills-key-steps-limitations-and-examples) *(→ Appendix A4)*
- [Building Skills for Claude Code](https://www.claude.com/blog/building-skills-for-claude-code) *(→ Appendix A5)*
- [Improving Frontend Design through Skills](https://www.claude.com/blog/improving-frontend-design-through-skills) *(→ Appendix A6)*

### Example skills

**Public skills repository:**

- GitHub: [`anthropics/skills`](https://github.com/anthropics/skills) *(→ Appendix A12)*
- Contains Anthropic-created skills you can customize

### Tools and Utilities

**skill-creator skill:**

- Built into Claude.ai and available for Claude Code
- Can generate skills from descriptions
- Reviews and provides recommendations
- Use: "Help me build a skill using skill-creator"

**Validation:**

- skill-creator can assess your skills
- Ask: "Review this skill and suggest improvements"

### Getting Support

**For Technical Questions:**

- General questions: Community forums at the [Claude Developers Discord](https://discord.com/invite/6PPFFzqPDZ)

**For Bug Reports:**

- GitHub Issues: [`anthropics/skills/issues`](https://github.com/anthropics/skills/issues)
- Include: Skill name, error message, steps to reproduce

---

## Reference A: Quick Checklist

Use this checklist to validate your skill before and after upload. If you want a faster start, use the skill-creator skill to generate your first draft, then run through this list to make sure you haven't missed anything.

### Before you start

- [ ] Identified 2-3 concrete use cases
- [ ] Tools identified (built-in or MCP)
- [ ] Reviewed this guide and example skills
- [ ] Planned folder structure

### During development

- [ ] Folder named in kebab-case
- [ ] `SKILL.md` file exists (exact spelling)
- [ ] YAML frontmatter has `---` delimiters
- [ ] `name` field: kebab-case, no spaces, no capitals
- [ ] `description` includes WHAT and WHEN
- [ ] No XML tags (`< >`) anywhere
- [ ] Instructions are clear and actionable
- [ ] Error handling included
- [ ] Examples provided
- [ ] References clearly linked

### Before upload

- [ ] Tested triggering on obvious tasks
- [ ] Tested triggering on paraphrased requests
- [ ] Verified doesn't trigger on unrelated topics
- [ ] Functional tests pass
- [ ] Tool integration works (if applicable)
- [ ] Compressed as `.zip` file

### After upload

- [ ] Test in real conversations
- [ ] Monitor for under/over-triggering
- [ ] Collect user feedback
- [ ] Iterate on description and instructions
- [ ] Update version in metadata

---

## Reference B: YAML Frontmatter

### Required fields

```yaml
---
name: skill-name-in-kebab-case
description: What it does and when to use it. Include specific trigger phrases.
---
```

### All optional fields

```yaml
name: skill-name
description: [required description]
license: MIT                                         # Optional: License for open-source
allowed-tools: "Bash(python:*) Bash(npm:*) WebFetch" # Optional: Restrict tool access
metadata:                                            # Optional: Custom fields
  author: Company Name
  version: 1.0.0
  mcp-server: server-name
  category: productivity
  tags: [project-management, automation]
  documentation: https://example.com/docs
  support: support@example.com
```

### Security notes

**Allowed:**

- Any standard YAML types (strings, numbers, booleans, lists, objects)
- Custom metadata fields
- Long descriptions (up to 1024 characters)

**Forbidden:**

- XML angle brackets (`< >`) - security restriction
- Code execution in YAML (uses safe YAML parsing)
- Skills named with "claude" or "anthropic" prefix (reserved)

---

## Reference C: Complete Skill Examples

For full, production-ready skills demonstrating the patterns in this guide:

- Document Skills - [PDF](https://github.com/anthropics/skills/tree/main/skills/pdf), [DOCX](https://github.com/anthropics/skills/tree/main/skills/docx), [PPTX](https://github.com/anthropics/skills/tree/main/skills/pptx), [XLSX](https://github.com/anthropics/skills/tree/main/skills/xlsx) creation
- [Example Skills](https://github.com/anthropics/skills/tree/main/skills) - Various workflow patterns
- [Partner Skills Directory](https://www.claude.com/connectors) - View skills from various partners such as Asana, Atlassian, Canva, Figma, Sentry, Zapier, and more

These repositories stay up-to-date and include additional examples beyond what's covered here. Clone them, modify them for your use case, and use them as templates.

---

## Appendix: Referenced Pages & Articles

This appendix contains the full text of the key pages and articles linked throughout this guide, converted to plain text for offline reading. GitHub repository READMEs are included where content was retrievable; SKILL.md files are included in full.

### Table of Contents

- [A1. Engineering Blog: Equipping Agents for the Real World](#a1-engineering-blog-equipping-agents-for-the-real-world-with-agent-skills)
- [A2. Introducing Agent Skills](#a2-introducing-agent-skills)
- [A3. Skills Explained: How Skills Compares to Prompts, Projects, MCP, and Subagents](#a3-skills-explained-how-skills-compares-to-prompts-projects-mcp-and-subagents)
- [A4. How to Create Skills: Key Steps, Limitations, and Examples](#a4-how-to-create-skills-key-steps-limitations-and-examples)
- [A5. Building Skills for Claude Code: Automating Your Procedural Knowledge](#a5-building-skills-for-claude-code-automating-your-procedural-knowledge)
- [A6. Improving Frontend Design Through Skills](#a6-improving-frontend-design-through-skills)
- [A7. Extending Claude's Capabilities with Skills and MCP Servers](#a7-extending-claudes-capabilities-with-skills-and-mcp-servers)
- [A8. Official Documentation: Agent Skills Overview](#a8-official-documentation-agent-skills-overview)
- [A9. Official Documentation: Skill Authoring Best Practices](#a9-official-documentation-skill-authoring-best-practices)
- [A10. Official Documentation: Agent Skills Quickstart (API)](#a10-official-documentation-agent-skills-quickstart-api)
- [A11. Official Documentation: Agent Skills in the Agent SDK](#a11-official-documentation-agent-skills-in-the-agent-sdk)
- [A12. GitHub Repository: anthropics/skills — README](#a12-github-repository-anthropicsskills--readme)
- [A13. GitHub: anthropics/skills — skill-creator SKILL.md](#a13-github-anthropicsskills--skill-creator-skillmd)
- [A14. GitHub: getsentry/sentry-for-claude — sentry-code-review](#a14-github-getsentrysentry-for-claude--sentry-code-review)
- [A15. Getting Started with Local MCP Servers on Claude Desktop](#a15-getting-started-with-local-mcp-servers-on-claude-desktop)
- [A16. Agent Skills Open Standard](#a16-agent-skills-open-standard)

---

### A1. Engineering Blog: Equipping Agents for the Real World with Agent Skills

**Source:** https://www.anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills
**Published:** October 16, 2025
**Update note:** Agent Skills published as an open standard for cross-platform portability (December 18, 2025)

As model capabilities improve, we can now build general-purpose agents that interact with full-fledged computing environments. Claude Code, for example, can accomplish complex tasks across domains using local code execution and filesystems. But as these agents become more powerful, we need more composable, scalable, and portable ways to equip them with domain-specific expertise. This led us to create Agent Skills: organized folders of instructions, scripts, and resources that agents can discover and load dynamically to perform better at specific tasks.

Skills extend Claude's capabilities by packaging your expertise into composable resources for Claude, transforming general-purpose agents into specialized agents that fit your needs. Building a skill for an agent is like putting together an onboarding guide for a new hire. Instead of building fragmented, custom-designed agents for each use case, anyone can now specialize their agents with composable capabilities by capturing and sharing their procedural knowledge.

**What is a skill?**

A skill is a directory containing a SKILL.md file — organized folders of instructions, scripts, and resources that give agents additional capabilities. To see Skills in action, consider the PDF skill, which powers Claude's document editing abilities. Claude already knows a lot about understanding PDFs, but is limited in its ability to manipulate them directly (e.g. to fill out a form). This PDF skill gives Claude these new abilities.

At its simplest, a skill is a directory that contains a SKILL.md file. This file must start with YAML frontmatter that contains required metadata: `name` and `description`. At startup, the agent pre-loads the name and description of every installed skill into its system prompt. This metadata is the first level of progressive disclosure: it provides just enough information for Claude to know when each skill should be used without loading all of it into context.

**Progressive disclosure**

Progressive disclosure is the core design principle that makes Agent Skills flexible and scalable. Like a well-organized manual that starts with a table of contents, then specific chapters, and finally a detailed appendix, skills let Claude load information only as needed.

- Agents with a filesystem and code execution tools don't need to read the entirety of a skill into their context window when working on a particular task.
- This means that the amount of context that can be bundled into a skill is effectively unbounded.

The three levels:
1. YAML frontmatter (always loaded) — name and description only
2. SKILL.md body (loaded when relevant) — full instructions
3. Linked reference files (loaded on demand) — additional context, bundled within the skill directory

As skills grow in complexity, they may contain too much context to fit into a single SKILL.md, or context that's relevant only in specific scenarios. In these cases, skills can bundle additional files within the skill directory and reference them by name from SKILL.md.

**Security note**

Malicious skills may introduce vulnerabilities or direct Claude to exfiltrate data and take unintended actions. Install skills only from trusted sources. When installing from a less-trusted source, audit it before use — paying attention to code dependencies, bundled resources, and instructions directing Claude to connect to external network sources.

**Best practices for authoring skills**

- Start with evaluation: Identify specific gaps in your agents' capabilities by running them on representative tasks and observing where they struggle. Build skills incrementally to address shortcomings.
- Structure for scale: When SKILL.md becomes unwieldy, split its content into separate files and reference them. If certain contexts are mutually exclusive or rarely used together, keeping the paths separate reduces token usage. Code can serve as both executable tools and documentation.
- Think from Claude's perspective: Monitor how Claude uses your skill in real scenarios and iterate based on observations. Watch for unexpected trajectories or overreliance on certain contexts.

**Platform support**

Agent Skills are supported across Claude.ai, Claude Code, the Claude Agent SDK, and the Claude Developer Platform.

---

### A2. Introducing Agent Skills

**Source:** https://claude.com/blog/skills
**Published:** October 16, 2025
**Update note:** Organization-wide skill management, partner skills directory, and open standard published (December 18, 2025)

Claude can now use Skills to improve how it performs specific tasks. Skills are folders that include instructions, scripts, and resources that Claude can load when needed. Claude will only access a skill when it's relevant to the task at hand. When used, skills make Claude better at specialized tasks like working with Excel or following your organization's brand guidelines.

You've already seen Skills at work in Claude apps, where Claude uses them to create files like spreadsheets and presentations. Now, you can build your own skills and use them across Claude apps, Claude Code, and the API.

Think of Skills as custom onboarding materials that let you package expertise, making Claude a specialist on what matters most to you.

**Availability**

Skills are available to Pro, Max, Team, and Enterprise users. Anthropic provides skills for common tasks like document creation, examples you can customize, and the ability to create your own custom skills.

Claude automatically invokes relevant skills based on your task — no manual selection needed. You'll even see skills in Claude's chain of thought as it works.

**Creating skills**

Creating skills is simple. The "skill-creator" skill provides interactive guidance: Claude asks about your workflow, generates the folder structure, formats the SKILL.md file, and bundles the resources you need. No manual file editing required.

**API access**

Agent Skills can be added to Messages API requests. The new `/v1/skills` endpoint gives developers programmatic control over custom skill versioning and management. Skills require the Code Execution Tool beta, which provides the secure environment they need to run.

**Pre-built document skills**

Use Anthropic-created skills to have Claude read and generate:
- Professional Excel spreadsheets with formulas
- PowerPoint presentations
- Word documents
- Fillable PDFs

Developers can create custom Skills to extend Claude's capabilities for their specific use cases. Developers can also create, view, and upgrade skill versions through the Claude Console.

---

### A3. Skills Explained: How Skills Compares to Prompts, Projects, MCP, and Subagents

**Source:** https://claude.com/blog/skills-explained
**Published:** November 13, 2025

Skills are an increasingly powerful tool for creating custom AI workflows and agents, but where do they fit in the Claude stack? This guide breaks down each building block, explains when to use what, and shows you how to combine them.

**Skills**

Skills are folders containing instructions, scripts, and resources that Claude discovers and loads dynamically when relevant to a task. Think of them as specialized training manuals that give Claude expertise in specific domains — from working with Excel spreadsheets to following your organization's writing standards.

When to use a Skill instead of something else: If you find yourself typing the same prompt repeatedly across multiple conversations, it's time to create a Skill. Transform recurring instructions like "review this code for security vulnerabilities using OWASP standards" or "format this analysis with executive summary, key findings, and recommendations" into Skills. This saves you from re-explaining procedures each time and ensures consistent execution.

**Prompts**

Prompts are the instructions you provide to Claude in natural language during a conversation. They're ephemeral, conversational, and reactive — you provide context and direction in the moment.

Pro-tip: Prompts are your primary way of interacting with Claude, but they don't persist across conversations. For repeated workflows or specialized knowledge, consider capturing prompts as Skills or project instructions.

**Projects**

Available on all paid Claude plans, Projects are self-contained workspaces with their own chat histories and knowledge bases. Each project includes a 200K context window where you can upload documents, provide context, and set custom instructions that apply to all conversations within that project.

Everything you upload to a project's knowledge base becomes available across all chats within that project.

When to use a Skill instead: Projects give Claude persistent context for a specific body of work — your company's codebase, a research initiative, an ongoing client engagement. Skills teach Claude how to do something. A Project might contain all the background on your product launch, while a skill could teach Claude your team's writing standards or code review process. If you find yourself copying the same instructions across multiple Projects, that's a signal to create a skill instead.

**MCP (Model Context Protocol)**

MCP servers connect Claude to external tools and real-time data sources — databases, APIs, monitoring platforms. MCP extends what Claude can access and use.

When to use MCP: For real-time data access (searching Notion pages, reading Slack messages, querying databases) or actions in external systems (creating GitHub issues, updating project management tools, sending notifications).

**Subagents**

Subagents are specialized AI assistants with their own context windows, custom system prompts, and specific tool permissions. Available in Claude Code and the Claude Agent SDK, subagents handle discrete tasks independently and return results to the main agent.

**How they all work together**

These tools are complementary: use Skills for reusable task expertise, Projects for ongoing bodies of work, MCP for external connectivity, and Subagents for parallel or specialized task delegation.

---

### A4. How to Create Skills: Key Steps, Limitations, and Examples

**Source:** https://claude.com/blog/how-to-create-skills-key-steps-limitations-and-examples
**Published:** November 19, 2025

Skills are custom instructions that extend Claude's capabilities for specific tasks or domains. When you create a skill via a SKILL.md file, you're teaching Claude how to handle specific scenarios more effectively. The power of skills lies in their ability to encode institutional knowledge, standardize outputs, and handle complex multi-step workflows that would otherwise require repeated explanation.

**Key principles before you start**

Don't write skills speculatively. Build them when you have real, repeated tasks. The best skills solve problems you encounter regularly. Before creating a skill, ask: Have I done this task at least five times? Will I do it at least ten more times? If yes, a skill makes sense.

Aim for single-purpose skills. "SEO optimization for blog posts" is focused enough for specific instructions while broad enough for reusability.
- Too broad: "Content marketing helper"
- Too narrow: "Add meta descriptions"

**Testing your skill**

Functional tests include:
- Output consistency: do multiple runs with similar inputs produce comparable results?
- Usability: can someone unfamiliar with the domain use it successfully?
- Documentation accuracy: do your examples match actual behavior?

Monitor how your skill performs in real-world usage:
- Refine descriptions if triggering is inconsistent
- Clarify instructions if outputs vary unexpectedly

**Team and organizational skills**

Regardless of team size, create a shared document repository with skill specifications. Use a template format with name, description, instructions, and version info.

For medium to large teams, establish a skills governance process:
- Designate skill owners for each domain (finance, legal, marketing)
- Maintain a central wiki or shared drive as your skill library
- Include usage examples and common troubleshooting for each skill
- Version your skills and document changes in a changelog
- Schedule quarterly reviews to update or retire outdated skills

Enterprise customers can work with Anthropic's customer success team to explore additional deployment options and governance frameworks.

---

### A5. Building Skills for Claude Code: Automating Your Procedural Knowledge

**Source:** https://claude.com/blog/building-skills-for-claude-code
**Published:** December 2, 2025

Your team has built up hard-won knowledge about your data — you know which tables are the source of truth, why certain filters must always apply, and how revenue can be calculated differently depending on the context. But Claude doesn't retain context from previous sessions. Without a way to share your team's data playbook, you end up re-explaining the same details through prompting.

Skills let you package that expertise into something Claude Code can discover and use automatically. Skills give Claude Code access to your procedural knowledge through progressive disclosure, revealing information in layers only when needed, rather than flooding the context window.

**How it works**

Claude always sees a lightweight index of available skills (names and descriptions, about 100 words each). Full skill content is loaded only when relevant. Supporting files (schemas, documentation) are only loaded when Claude needs them for a specific task.

**Skills vs CLAUDE.md**

Skills and CLAUDE.md files both give Claude context, but serve different purposes.

CLAUDE.md is always loaded into Claude's context. It's for project-specific guidance (coding conventions, local workflows, common commands) that lives in your repo as a single markdown file, and works only in Claude Code.

Skills use progressive disclosure, loading only when relevant, and work across all Claude platforms (claude.ai, Claude Code, and Claude API). Beyond the context management advantages, Skills can include executable code and reference files — not just markdown. This makes them ideal for substantial, reusable knowledge that spans projects.

**Good candidates for skills**

- Cross-repo relevance: Knowledge that applies across multiple projects
- Multi-audience value: Both technical and non-technical users benefit
- Stable patterns: Procedures that don't change with every commit
- Data warehouse queries, internal platform documentation, and company-wide standards

**Building with Claude's help**

Claude can serve as your documentation partner. Start by describing your workflow conversationally:

> "Help me create a data warehouse skill. I'll walk you through our tables and business logic, and you can help me structure it properly."

Claude will ask clarifying questions: What are your key tables? What business terms need definition? What filters should always apply?

Once you've outlined your domain, Claude will help you structure the SKILL.md and organize reference files.

**Organizational impact**

Skills let you encode institutional knowledge that works across teams and platforms. New analysts query data correctly on day one, data scientists stop explaining the same table relationships, and business users can self-serve accurate metrics.

---

### A6. Improving Frontend Design Through Skills

**Source:** https://claude.com/blog/improving-frontend-design-through-skills
**Published:** November 12, 2025

We can unlock significantly better UI generations from Claude, without permanent context overhead, by creating a frontend design skill.

**The problem: distributional convergence**

When you ask an LLM to build a landing page without guidance, it will almost always converge to Inter fonts, purple gradients on white backgrounds, and minimal animations. During sampling, models predict tokens based on statistical patterns in training data. Safe design choices — those that work universally and offend no one — dominate web training data. Without direction, Claude samples from this high-probability center.

For developers building customer-facing products, this generic aesthetic undermines brand identity and makes AI-generated interfaces immediately recognizable — and dismissible.

**The solution: targeted prompting**

The good news is that Claude is highly steerable with the right prompting. Tell Claude to "avoid Inter and Roboto" or "use atmospheric backgrounds instead of solid colors," and results improve immediately.

The core insight is to think about frontend design the way a frontend engineer would. The more you can map aesthetic improvements to implementable frontend code, the better Claude can execute.

Several areas where targeted prompting works well:
- Typography: Choose fonts that are beautiful, unique, and interesting. Avoid generic fonts like Arial and Inter; opt for distinctive choices that elevate aesthetics.
- Animations: Prompting for motion (animations and micro-interactions) adds polish that static designs lack.
- Background effects: Guide the model toward more interesting background choices to create depth and visual interest.
- Themes: Claude has rich understanding of popular themes; use this to communicate the specific aesthetic you want.

**The frontend design skill**

Implementing improvements manually in every prompt is tedious. The frontend design skill combines all these improvements into one reusable asset. With this skill active, Claude's output improves across several types of frontend designs, including SaaS landing pages, blog layouts, and admin dashboards.

Key skill instructions include:
- Avoid overused font families (Inter, Roboto, Arial, system fonts)
- Avoid clichéd color schemes (particularly purple gradients on white backgrounds)
- Avoid predictable layouts and component patterns
- Create atmosphere and depth in backgrounds rather than defaulting to solid colors
- Interpret creatively and make unexpected choices that feel genuinely designed for the context

---

### A7. Extending Claude's Capabilities with Skills and MCP Servers

**Source:** https://claude.com/blog/extending-claude-capabilities-with-skills-mcp-servers
**Published:** December 19, 2025

**The hardware store analogy**

You walk into a hardware store looking to fix a broken cabinet. The store has everything you need (wood glue, clamps, replacement hinges) but knowing what items to buy and how to use them is a different problem. MCP is like having access to the aisles. Skills, meanwhile, are like an employee's expertise. All the inventory in the world won't help if you don't know which items you need or how to use them.

A skill is like the helpful employee who walks you through the repair process, points you to the right supplies, and shows you proper technique.

**How skills and MCP work together**

An MCP server gives Claude access to your external systems, services, and platforms. Skills provide the context Claude needs to use those connections effectively, teaching Claude the right workflows and processes for your specific needs.

The rule of thumb:
- MCP instructions cover how to use the server and its tools correctly.
- Skill instructions cover how to use them for a given process or in a multiserver workflow.

For example, a Salesforce MCP server might specify query syntax and API formats. A skill would specify which records to check first, how to cross-reference them against Slack conversations for recent context, and how to structure the output for your team's pipeline review.

**Watch for conflicting instructions**

When combining MCP servers and skills, watch for conflicting instructions. If your MCP server says to return JSON and your skill says to format as markdown tables, Claude has to guess which one is right. Keep tool-specific knowledge close to the tool (in MCP), and keep workflow-specific knowledge in skills.

**Real-world example 1: Financial analysis**

Comparable company analysis is a standard valuation method. Analysts spend hours pulling financial metrics from multiple sources, applying the same valuation methodology, and formatting outputs to meet compliance standards. It's repetitive, error-prone, and exactly the kind of workflow that benefits from skills and MCP working together.

- Skill: Comparable company analysis automates the valuation workflow, pulling data from multiple sources, applying consistent methodology, and formatting outputs to specific standards.
- MCP servers: Connections to S&P Capital IQ, Daloopa, and Morningstar for live market data.

**Real-world example 2: Meeting prep with Notion**

Meeting prep requires pulling context from multiple places — project docs, previous meeting notes, stakeholder info — then synthesizing into a pre-read and agenda. It's the kind of multi-step process you end up re-explaining every time.

- Skill: Meeting Intelligence defines which pages to search, how to structure outputs, and what sections to include.
- MCP server: Notion connection that searches, reads, and creates pages.

**When to use skills vs MCP**

Use skills when you need: multi-step workflows involving tools, processes where consistency matters, domain expertise to capture and share, or workflows that should survive when team members leave.

Use MCP when you need: real-time data access, actions in external systems, or event-driven integrations.

---

### A8. Official Documentation: Agent Skills Overview

**Source:** https://platform.claude.com/docs/en/agents-and-tools/agent-skills/overview

Skills are reusable, filesystem-based resources that provide Claude with domain-specific expertise: workflows, context, and best practices that transform general-purpose agents into specialists. Unlike prompts (conversation-level instructions for one-off tasks), Skills load on-demand and eliminate the need to repeatedly provide the same guidance across multiple conversations.

**Pre-built Agent Skills available immediately:**

- PowerPoint (pptx): Create presentations, edit slides, analyze presentation content
- Excel (xlsx): Create spreadsheets, analyze data, generate reports with charts
- Word (docx): Create documents, edit content, format text
- PDF (pdf): Generate formatted PDF documents and reports

**Skill structure**

Every Skill requires a SKILL.md file with YAML frontmatter:

```yaml
---
name: your-skill-name
description: Brief description of what this Skill does and when to use it
---
# Your Skill Name
## Instructions
[Clear, step-by-step guidance for Claude to follow]
## Examples
[Concrete examples of using this Skill]
```

Required fields: `name` and `description`

Field requirements:
- `name`: Maximum 64 characters, lowercase letters/numbers/hyphens only, no XML tags, no reserved words ("anthropic", "claude")
- `description`: Must be non-empty, maximum 1024 characters, no XML tags, should describe what the Skill does and when to use it

**The Skills architecture**

Skills leverage Claude's VM environment to provide capabilities beyond what's possible with prompts alone. Claude operates in a virtual machine with filesystem access, allowing Skills to exist as directories containing instructions, executable code, and reference materials.

This filesystem-based architecture enables progressive disclosure: Claude loads information in stages as needed, rather than consuming context upfront.

Content types loaded at different times:
- YAML frontmatter: Discovery information, loaded at startup into system prompt
- SKILL.md body: Full instructions, loaded when Claude determines the Skill is relevant
- Additional files: Reference materials, loaded on demand as needed
- Scripts: Executed via bash; only the output consumes context tokens

**Limitations**

Custom Skills do not sync across surfaces. Skills uploaded to Claude.ai must be separately uploaded to the API. Skills uploaded via the API are not available on Claude.ai.

Security considerations: Only use Skills from trusted sources. Even trustworthy Skills can be compromised if their external dependencies change over time. Tool misuse, data exposure, and dependency attacks are all possible vectors.

---

### A9. Official Documentation: Skill Authoring Best Practices

**Source:** https://platform.claude.com/docs/en/agents-and-tools/agent-skills/best-practices

Good Skills are concise, well-structured, and tested with real usage. This guide provides practical authoring decisions to help you write Skills that Claude can discover and use effectively.

**Start with evaluations**

Create evaluations BEFORE writing extensive documentation. This ensures your Skill solves real problems rather than documenting imagined ones.

Process:
1. Identify gaps: Run Claude on representative tasks without a Skill. Document specific failures or missing context.
2. Create evaluations: Build three scenarios that test these gaps.
3. Establish baseline: Measure Claude's performance without the Skill.
4. Write minimal instructions: Create just enough content to address the gaps and pass evaluations.
5. Iterate: Execute evaluations, compare against baseline, and refine.

Evaluation structure example:

```json
{
  "skills": ["pdf-processing"],
  "query": "Extract all text from this PDF file and save it to output.txt",
  "files": ["test-files/document.pdf"],
  "expected_behavior": [
    "Successfully reads the PDF file using an appropriate PDF processing library",
    "Extracts text content from all pages without missing any pages",
    "Saves the extracted text to output.txt in a clear, readable format"
  ]
}
```

**Naming conventions**

Use gerund form (verb + -ing) for Skill names, as this clearly describes the activity the Skill provides.

Good examples: `processing-pdfs`, `analyzing-spreadsheets`, `managing-databases`, `testing-code`, `writing-documentation`

**Develop Skills iteratively with Claude**

The most effective Skill development process involves Claude itself. Work with one instance of Claude ("Claude A") to create a Skill that will be used by other instances ("Claude B").

Process:
1. Work with Claude A (the expert who helps refine the Skill)
2. Test with Claude B (the agent using the Skill to perform real work)
3. Observe Claude B's behavior and bring insights back to Claude A

Use the Skill in real workflows: Give Claude B actual tasks, not test scenarios. Observe where it struggles, succeeds, or makes unexpected choices.

Example observation: "When I asked Claude B for a regional sales report, it wrote the query but forgot to filter out test accounts, even though the Skill mentions this rule."

Return to Claude A for improvements and share observations. Claude A might suggest reorganizing to make rules more prominent, using stronger language like "MUST filter" instead of "always filter."

**Watch how Claude navigates your Skills**

As you iterate, pay attention to:
- Unexpected exploration paths: If Claude reads files in an unexpected order, your structure may not be as intuitive as you thought.
- Missed connections: If Claude fails to follow references to important files, links may need to be more explicit.
- Overreliance on certain sections: If Claude repeatedly reads the same file, consider whether that content should be in the main SKILL.md.
- Ignored content: If Claude never accesses a bundled file, it might be unnecessary or poorly signaled.

**Runtime environment**

Skills run in the code execution environment with filesystem access, bash commands, and code execution capabilities.

Package dependencies:
- claude.ai: Can install packages from npm and PyPI and pull from GitHub repositories
- Anthropic API: Has no network access and no runtime package installation

List required packages in your SKILL.md and verify they're available in the code execution tool documentation.

---

### A10. Official Documentation: Agent Skills Quickstart (API)

**Source:** https://platform.claude.com/docs/en/agents-and-tools/agent-skills/quickstart

Learn how to use Agent Skills to create documents with the Claude API in under 10 minutes.

**Prerequisites**

- Anthropic API key
- Python 3.7+ or curl installed
- Basic familiarity with making API requests

**Step 1: List available skills**

```python
import anthropic
client = anthropic.Anthropic()
skills = client.beta.skills.list(source="anthropic", betas=["skills-2025-10-02"])
```

**Step 2: Create a document with a skill**

```python
response = client.beta.messages.create(
    model="claude-opus-4-5",
    max_tokens=4096,
    betas=["code-execution-2025-08-25", "skills-2025-10-02"],
    container={
        "skills": [{"type": "anthropic", "skill_id": "pptx", "version": "latest"}]
    },
    messages=[
        {
            "role": "user",
            "content": "Create a presentation on renewable energy with 5 slides"
        }
    ],
    tools=[{"type": "code_execution_20250825", "name": "code_execution"}],
)
```

**Step 3: Download the generated file**

```python
file_id = None
for block in response.content:
    if block.type == "tool_use" and block.name == "code_execution":
        for result_block in block.content:
            if hasattr(result_block, "file_id"):
                file_id = result_block.file_id
                break

if file_id:
    file_content = client.beta.files.download(
        file_id=file_id,
        betas=["files-api-2025-04-14"]
    )
    with open("presentation.pptx", "wb") as f:
        file_content.write_to_file(f.name)
```

**Other supported skill IDs**

```python
# Excel spreadsheet
container={"skills": [{"type": "anthropic", "skill_id": "xlsx", "version": "latest"}]}

# Word document
container={"skills": [{"type": "anthropic", "skill_id": "docx", "version": "latest"}]}

# PDF document
container={"skills": [{"type": "anthropic", "skill_id": "pdf", "version": "latest"}]}
```

---

### A11. Official Documentation: Agent Skills in the Agent SDK

**Source:** https://platform.claude.com/docs/en/agent-sdk/skills

Agent Skills extend Claude with specialized capabilities that Claude autonomously invokes when relevant. Skills are packaged as SKILL.md files containing instructions, descriptions, and optional supporting resources.

**Loading Skills in the SDK**

```python
import asyncio
from claude_agent_sdk import query, ClaudeAgentOptions

async def main():
    options = ClaudeAgentOptions(
        cwd="/path/to/project",
        setting_sources=["user", "project"],
        allowed_tools=["Skill", "Read", "Write", "Bash"],
    )
    async for message in query(
        prompt="Help me process this PDF document",
        options=options
    ):
        print(message)

asyncio.run(main())
```

**Skill loading locations**

- Project Skills (`.claude/skills/`): Shared with your team via git — loaded when `setting_sources` includes "project"
- User Skills (`~/.claude/skills/`): Personal Skills across all projects — loaded when `setting_sources` includes "user"
- Plugin Skills: Bundled with installed Claude Code plugins

**Troubleshooting: Skill not triggering**

Check the description field: Ensure it's specific and includes relevant keywords. See Agent Skills Best Practices for guidance on writing effective descriptions.

---

### A12. GitHub Repository: anthropics/skills — README

**Source:** https://github.com/anthropics/skills
**Full README:** https://github.com/anthropics/skills/blob/main/README.md

This is the official Anthropic public repository for Agent Skills. Skills are folders of instructions, scripts, and resources that Claude loads dynamically to improve performance on specialized tasks. Skills teach Claude how to complete specific tasks in a repeatable way, whether that's creating documents with your company's brand guidelines, analyzing data using your organization's specific workflows, or automating personal tasks.

> Note: This repository contains Anthropic's implementation of skills for Claude. For information about the Agent Skills standard, see [agentskills.io](https://agentskills.io).

**Repository structure:**

```
skills/
├── skills/      # Skill examples
│   ├── Creative & Design     (e.g. algorithmic-art, frontend-design)
│   ├── Development & Technical  (e.g. mcp-builder, skill-creator)
│   ├── Enterprise & Communication
│   └── Document Skills       (pdf, docx, pptx, xlsx)
├── spec/        # The Agent Skills specification
└── template/    # Skill template
```

**Quick start template:**

```yaml
---
name: my-skill-name
description: A clear description of what this skill does and when to use it
---
# My Skill Name

[Add your instructions here that Claude will follow when this skill is active]

## Examples
- Example usage 1
- Example usage 2

## Guidelines
- Guideline 1
- Guideline 2
```

**Installing via Claude Code:**

```bash
/plugin marketplace add anthropics/skills
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
```

**Key support links:**
- [What are skills?](https://support.claude.com/en/articles/12512176-what-are-skills)
- [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [How to create custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [Skills API Quickstart](https://platform.claude.com/docs/en/agents-and-tools/agent-skills/quickstart)

---

### A13. GitHub: anthropics/skills — skill-creator SKILL.md

**Source:** https://github.com/anthropics/skills/blob/main/skills/skill-creator/SKILL.md
**Type:** SKILL.md file — key content included

**Frontmatter:**

```yaml
---
name: skill-creator
description: Interactive guide for creating new skills. Walks the user through use
  case definition, frontmatter generation, instruction writing, and validation.
---
```

**Skill structure reference (from SKILL.md):**

```
skill-name/
├── SKILL.md (required)
│   ├── YAML frontmatter metadata (required)
│   │   ├── name: (required)
│   │   ├── description: (required)
│   │   └── compatibility: (optional, rarely needed)
│   └── Markdown instructions (required)
└── Bundled Resources (optional)
    ├── scripts/    - Executable code (Python/Bash/etc.)
    ├── references/ - Documentation loaded into context as needed
    └── assets/     - Files used in output (templates, icons, fonts, etc.)
```

**Workflow steps (from SKILL.md):**

Follow these steps in order, skipping only if there is a clear reason they are not applicable:

1. **Understand concrete use cases** — Clearly understand concrete examples of how the skill will be used. This understanding can come from either direct user examples or generated examples that are validated with user feedback. Ask: "What functionality should this skill support? What are common inputs and outputs?"

2. **Establish skill contents** — Analyze each concrete example to create a list of reusable resources to include: scripts, references, and assets.

3. **Create the skill** — When creating a new skill from scratch, always run the `init_skill.py` script. The script generates a new template skill directory that automatically includes everything a skill requires. After initialization, customize or remove the generated SKILL.md and example files as needed. Remember that the skill is being created for another instance of Claude to use.

4. **Write the SKILL.md** — Write instructions for using the skill and its bundled resources. Frontmatter contains name and description (required). Only name and description are read by Claude to determine when the skill triggers, so be clear and comprehensive.

5. **Package** — Once development is complete, package into a distributable `.skill` file. The packaging process automatically validates the skill first. Creates a `.skill` file named after the skill (e.g., `my-skill.skill`).

**Reference file best practices (from SKILL.md):**

- Avoid deeply nested references — keep references one level deep from SKILL.md
- For files longer than 100 lines, include a table of contents at the top
- Consult `references/workflows.md` for sequential workflows and conditional logic
- Consult `references/output-patterns.md` for template and example patterns

**Example description format:**

> "Comprehensive document creation, editing, and analysis with support for tracked changes, comments, formatting preservation, and text extraction. Use when Claude needs to work with professional documents (.docx files) for: (1) Creating new documents, (2) Modifying or editing content, (3) Working with tracked changes, (4) Adding comments, or any other document tasks"

---

### A14. GitHub: getsentry/sentry-for-claude — sentry-code-review

**Source:** https://github.com/getsentry/sentry-for-claude/tree/main/skills/sentry-code-review
**Full README:** https://github.com/getsentry/sentry-for-claude/blob/main/README.md

> **⚠️ TODO — Fetch & verify SKILL.md content (Pass 3)**
> The content below is based on search result excerpts. A future pass should fetch
> the raw file at:
> `https://raw.githubusercontent.com/getsentry/sentry-for-claude/main/skills/sentry-code-review/SKILL.md`
> and replace this section with the verified full content.

**Repository context (from README):**

```
sentry-for-claude/
├── .claude-plugin/
│   ├── plugin.json         # Plugin metadata
│   └── marketplace.json    # Marketplace listing
├── .mcp.json               # MCP server configuration
├── AGENTS.md               # Agent instructions
├── commands/
│   └── seer.md             # /seer command
└── skills/
    ├── sentry-code-review/
    ├── sentry-ios-swift-setup/
    ├── sentry-setup-ai-monitoring/
    ├── sentry-setup-logging/
    ├── sentry-setup-metrics/
    └── sentry-setup-tracing/
```

**Install:**

```bash
git clone https://github.com/getsentry/sentry-for-claude.git
cd sentry-for-claude
/plugin marketplace add /path/to/sentry-for-claude
/plugin install sentry@local
```

**Frontmatter (from search excerpts):**

```yaml
---
name: sentry-code-review
description: Analyze and resolve Sentry comments on GitHub Pull Requests. Use this
  when asked to review or fix issues identified by Sentry in PR comments. Can review
  specific PRs by number or automatically find recent PRs with Sentry feedback.
---
```

**Workflow summary (from search excerpts):**

Step 1 — Identify the PR (use provided number or find recent ones with `gh api`).
Step 2 — Fetch Sentry comments (ONLY process comments from users whose login starts with "sentry").
Step 3 — Analyze each comment: extract file path, line number, issue description, severity, and confidence score. Verify the issue still exists before fixing.
Step 4 — Fix issues: always Read before Edit; make targeted fixes; ask user if unsure.
Step 5 — Output a structured summary with issues resolved, issues requiring manual review, and totals.

Core principles: Only Sentry comments. Verify first. Remind user to run tests after fixes.

---

### A15. Getting Started with Local MCP Servers on Claude Desktop

**Source:** https://support.claude.com/en/articles/10949351-getting-started-with-local-mcp-servers-on-claude-desktop
**Type:** Support article — placeholder

> Full article: https://support.claude.com/en/articles/10949351-getting-started-with-local-mcp-servers-on-claude-desktop

This support article covers how to configure and connect local MCP servers using Claude Desktop, including setup steps, authentication, and verifying a "Connected" status in Settings > Extensions.

---

### A16. Agent Skills Open Standard

**Source:** https://agentskills.io/home
**Type:** External specification site — placeholder

> Full specification: https://agentskills.io/home

The Agent Skills open standard defines a portable format for skills that works across AI platforms — not just Claude. The standard specifies the SKILL.md format, YAML frontmatter requirements, and progressive disclosure architecture. Anthropic published this standard in December 2025 to enable cross-platform portability.

The `compatibility` field in SKILL.md frontmatter allows skill authors to note when a skill is designed to take full advantage of a specific platform's capabilities.

