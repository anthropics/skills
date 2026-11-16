# Skills
Skills are folders of instructions, scripts, and resources that Claude loads dynamically to improve performance on specialized tasks. Skills teach Claude how to complete specific tasks in a repeatable way, whether that's creating documents with your company's brand guidelines, analyzing data using your organization's specific workflows, or automating personal tasks.

For more information, check out:
- [What are skills?](https://support.claude.com/en/articles/12512176-what-are-skills)
- [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [How to create custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [Equipping agents for the real world with Agent Skills](https://anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)

# About This Repository

This repository contains example skills that demonstrate what's possible with Claude's skills system. These examples range from creative applications (art, music, design) to technical tasks (testing web apps, MCP server generation) to enterprise workflows (communications, branding, etc.).

Each skill is self-contained in its own directory with a `SKILL.md` file containing the instructions and metadata that Claude uses. Browse through these examples to get inspiration for your own skills or to understand different patterns and approaches.

The example skills in this repo are open source (Apache 2.0). Anthropic's document skills (docx, pdf, pptx, xlsx) are not carried here: they ship with Claude, so use those built-in versions.

**Note:** These are reference examples for inspiration and learning. They showcase general-purpose capabilities rather than organization-specific workflows or sensitive content.

## Disclaimer

**These skills are provided for demonstration and educational purposes only.** While some of these capabilities may be available in Claude, the implementations and behaviors you receive from Claude may differ from what is shown in these examples. These examples are meant to illustrate patterns and possibilities. Always test skills thoroughly in your own environment before relying on them for critical tasks.

# Example Skills

This repository includes a diverse collection of example skills demonstrating different capabilities:

**Legend:** 🅰️ = Anthropic-authored | ![Bernier LLC](assets/bernier-emoji-16.png) = Bernier LLC-authored

## Creative & Design
- 🅰️ [**algorithmic-art**](algorithmic-art/SKILL.md) - Create generative art using p5.js with seeded randomness, flow fields, and particle systems
- 🅰️ [**canvas-design**](canvas-design/SKILL.md) - Design beautiful visual art in .png and .pdf formats using design philosophies
- 🅰️ [**slack-gif-creator**](slack-gif-creator/SKILL.md) - Create animated GIFs optimized for Slack's size constraints

## Development & Technical
- 🅰️ [**artifacts-builder**](artifacts-builder/SKILL.md) - Build complex claude.ai HTML artifacts using React, Tailwind CSS, and shadcn/ui components
- 🅰️ [**mcp-builder**](mcp-builder/SKILL.md) - Guide for creating high-quality MCP servers to integrate external APIs and services
- 🅰️ [**webapp-testing**](webapp-testing/SKILL.md) - Test local web applications using Playwright for UI verification and debugging

## Testing & QA
- ![Bernier LLC](assets/bernier-emoji-16.png) [**api-verification**](api-verification/SKILL.md) - Run a principal × operation access matrix against REST endpoints and MCP tools and flag over-permissive or over-restrictive operations
- ![Bernier LLC](assets/bernier-emoji-16.png) [**api-verification-writer**](api-verification-writer/SKILL.md) - Write one verification doc per REST endpoint and MCP tool, flagging spec/code drift and missing auth declarations
- ![Bernier LLC](assets/bernier-emoji-16.png) [**browser-verification**](browser-verification/SKILL.md) - Manual QA verification of web application features in a browser using verification checklists
- ![Bernier LLC](assets/bernier-emoji-16.png) [**playwright-test-generator**](playwright-test-generator/SKILL.md) - Convert verification docs to Playwright tests incrementally with support for auth-aware generation and hook-driven automation
- ![Bernier LLC](assets/bernier-emoji-16.png) [**playwright-test-runner**](playwright-test-runner/SKILL.md) - Autonomous Playwright test execution, failure diagnosis, fix implementation, and environment teardown
- ![Bernier LLC](assets/bernier-emoji-16.png) [**ui-audit**](ui-audit/SKILL.md) - Automated UI audit system for discovering routes, creating exploration tasks, and generating Playwright tests
- ![Bernier LLC](assets/bernier-emoji-16.png) [**ux-audit**](ux-audit/SKILL.md) - Systematically identify user experience problems through browser inspection and code analysis with prioritized findings and WCAG 2.1 AA coverage
- ![Bernier LLC](assets/bernier-emoji-16.png) [**verification-writer**](verification-writer/SKILL.md) - Generate, update, and audit manual verification docs for browser-based QA from codebase routes, components, and user types

## Developer Workflow
- ![Bernier LLC](assets/bernier-emoji-16.png) [**commit**](commit/SKILL.md) - Standardized commit workflow with commitlint validation, gitignore checks, and safe push procedures
- ![Bernier LLC](assets/bernier-emoji-16.png) [**feature-map-review**](feature-map-review/SKILL.md) - Map every feature of a project, record every gap under a permanent id, re-cut plans and backlog by feature, then map the work graph and code boundaries to show what can run in parallel
- ![Bernier LLC](assets/bernier-emoji-16.png) [**feedback-loop**](feedback-loop/SKILL.md) - Log friction from skills, agents, hooks, plugins, AEC and the dev process to a local per-subject store, then review it with the user and turn it into PRs, issues or plan files
- ![Bernier LLC](assets/bernier-emoji-16.png) [**git-conventions**](git-conventions/SKILL.md) - Enforce lowercase conventional commits through a commit-msg hook, no commitlint install needed
- ![Bernier LLC](assets/bernier-emoji-16.png) [**orchata**](orchata/SKILL.md) - Plan and execute a task end to end with multi-agent orchestration, involving the human only where their hands are needed
- ![Bernier LLC](assets/bernier-emoji-16.png) [**plan-review**](plan-review/SKILL.md) - Audit and clean up plan files by correlating them with git branches and performing code inspection to determine actual completion state
- ![Bernier LLC](assets/bernier-emoji-16.png) [**pr-merge-flow**](pr-merge-flow/SKILL.md) - Keep parallel PRs from restarting each other's CI: hand merges to the repo's traffic cop (never `--auto`) and sync the base only on a real conflict
- ![Bernier LLC](assets/bernier-emoji-16.png) [**adversarial-review**](adversarial-review/SKILL.md) - Codex-first adversarial PR review loop with required inline line-item comments
- ![Bernier LLC](assets/bernier-emoji-16.png) [**review-gate**](review-gate/SKILL.md) - Enforce review before merge: trusted pull_request_target gate, doctor + merge guard
- ![Bernier LLC](assets/bernier-emoji-16.png) [**resume**](resume/SKILL.md) - Pick up in-flight work by reconciling run state, the activity log and the tracker against git
- ![Bernier LLC](assets/bernier-emoji-16.png) [**seed-data**](seed-data/SKILL.md) - Create, modify, or audit application data across environments with data classification, idempotency enforcement, and framework-aware workflow
- ![Bernier LLC](assets/bernier-emoji-16.png) [**ship**](ship/SKILL.md) - Close out a branch in one command: verify, commit, push, open the PR and sync the tracker
- ![Bernier LLC](assets/bernier-emoji-16.png) [**typecheck-on-edit**](typecheck-on-edit/SKILL.md) - Type-check a TypeScript repo after every edit through a blocking PostToolUse hook

## Enterprise & Communication
- 🅰️ [**brand-guidelines**](brand-guidelines/SKILL.md) - Apply Anthropic's official brand colors and typography to artifacts
- 🅰️ [**internal-comms**](internal-comms/SKILL.md) - Write internal communications like status reports, newsletters, and FAQs
- 🅰️ [**theme-factory**](theme-factory/SKILL.md) - Style artifacts with 10 pre-set professional themes or generate custom themes on-the-fly

## Meta Skills
- 🅰️ [**skill-creator**](skill-creator/SKILL.md) - Guide for creating effective skills that extend Claude's capabilities
- 🅰️ [**template-skill**](template-skill/SKILL.md) - A basic template to use as a starting point for new skills

# Document Skills

Google Workspace document skills. For Word, PDF, PowerPoint, and Excel files, use the docx/pdf/pptx/xlsx skills that ship with Claude.

- ![Bernier LLC](assets/bernier-emoji-16.png) [**gdocs**](gdocs/SKILL.md) - Writes and updates Google Docs with intelligent content synthesis. Transforms raw content into professional, document-appropriate text with proper formatting and attribution. Supports multi-tab documents and structure-aware insertion
- ![Bernier LLC](assets/bernier-emoji-16.png) [**gslides**](document-skills/gslides/SKILL.md) - Complete Google Slides solution with 6 phases: Foundation, Creation, Visual Design (WCAG compliance, brand guidelines), Data Visualization (11 chart types), AI-Powered Content Generation (FREE - no API key!), and Quality Assurance. Transform raw notes into beautiful, brand-compliant presentations in seconds

# Try in Claude Code, Claude.ai, and the API

## Claude Code
You can register this repository as a Claude Code Plugin marketplace by running the following command in Claude Code:
```
/plugin marketplace add anthropics/skills
```

Then, to install a specific set of skills:
1. Select `Browse and install plugins`
2. Select `anthropic-agent-skills`
3. Select `document-skills` or `example-skills`
4. Select `Install now`

Alternatively, directly install either Plugin via:
```
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
```

After installing the plugin, you can use the skill by just mentioning it. For instance, if you install the `document-skills` plugin from the marketplace, you can ask Claude Code to do something like: "Use the gdocs skill to add these meeting notes to my project doc"

## Claude.ai

These example skills are all already available to paid plans in Claude.ai. 

To use any skill from this repository or upload custom skills, follow the instructions in [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude#h_a4222fa77b).

## Claude API

You can use Anthropic's pre-built skills, and upload custom skills, via the Claude API. See the [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide#creating-a-skill) for more.

# Creating a Basic Skill

Skills are simple to create - just a folder with a `SKILL.md` file containing YAML frontmatter and instructions. You can use the **template-skill** in this repository as a starting point:

```markdown
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

The frontmatter requires only two fields:
- `name` - A unique identifier for your skill (lowercase, hyphens for spaces)
- `description` - A complete description of what the skill does and when to use it

The markdown content below contains the instructions, examples, and guidelines that Claude will follow. For more details, see [How to create custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills).

# Partner Skills

Skills are a great way to teach Claude how to get better at using specific pieces of software. As we see awesome example skills from partners, we may highlight some of them here:

- **Notion** - [Notion Skills for Claude](https://www.notion.so/notiondevs/Notion-Skills-for-Claude-28da4445d27180c7af1df7d8615723d0)