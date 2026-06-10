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

The example skills in this repo are open source (Apache 2.0). We've also included the document creation & editing skills that power [Claude's document capabilities](https://www.anthropic.com/news/create-files) under the hood in the [`document-skills/`](./document-skills/) folder. These are source-available, not open source, but we wanted to share these with developers as a reference for more complex skills that are actively used in a production AI application.

**Note:** These are reference examples for inspiration and learning. They showcase general-purpose capabilities rather than organization-specific workflows or sensitive content.

## Disclaimer

**These skills are provided for demonstration and educational purposes only.** While some of these capabilities may be available in Claude, the implementations and behaviors you receive from Claude may differ from what is shown in these examples. These examples are meant to illustrate patterns and possibilities. Always test skills thoroughly in your own environment before relying on them for critical tasks.

# Example Skills

This repository includes a diverse collection of example skills demonstrating different capabilities:

## Creative & Design
- **algorithmic-art** - Create generative art using p5.js with seeded randomness, flow fields, and particle systems
- **canvas-design** - Design beautiful visual art in .png and .pdf formats using design philosophies
- **slack-gif-creator** - Create animated GIFs optimized for Slack's size constraints

## Development & Technical
- **artifacts-builder** - Build complex claude.ai HTML artifacts using React, Tailwind CSS, and shadcn/ui components
- **mcp-server** - Guide for creating high-quality MCP servers to integrate external APIs and services
- **webapp-testing** - Test local web applications using Playwright for UI verification and debugging

## Enterprise & Communication
- **brand-guidelines** - Apply Anthropic's official brand colors and typography to artifacts
- **internal-comms** - Write internal communications like status reports, newsletters, and FAQs
- **theme-factory** - Style artifacts with 10 pre-set professional themes or generate custom themes on-the-fly

## Meta Skills
- **skill-creator** - Guide for creating effective skills that extend Claude's capabilities
- **template-skill** - A basic template to use as a starting point for new skills

# Document Skills

The `document-skills/` subdirectory contains skills that Anthropic developed to help Claude create various document file formats. These skills demonstrate advanced patterns for working with complex file formats and binary data:

- **docx** - Create, edit, and analyze Word documents with support for tracked changes, comments, formatting preservation, and text extraction
- **pdf** - Comprehensive PDF manipulation toolkit for extracting text and tables, creating new PDFs, merging/splitting documents, and handling forms
- **pptx** - Create, edit, and analyze PowerPoint presentations with support for layouts, templates, charts, and automated slide generation
- **xlsx** - Create, edit, and analyze Excel spreadsheets with support for formulas, formatting, data analysis, and visualization

**Important Disclaimer:** These document skills are point-in-time snapshots and are not actively maintained or updated. Versions of these skills ship pre-included with Claude. They are primarily intended as reference examples to illustrate how Anthropic approaches developing more complex skills that work with binary file formats and document structures.

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

After installing the plugin, you can use the skill by just mentioning it. For instance, if you install the `document-skills` plugin from the marketplace, you can ask Claude Code to do something like: "Use the PDF skill to extract the form fields from path/to/some-file.pdf"

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