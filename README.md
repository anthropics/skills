> **Note:** This repository contains Anthropic's implementation of skills for Claude. For information about the Agent Skills standard, see [agentskills.io](http://agentskills.io).

# Skills
Skills are folders of instructions, scripts, and resources that Claude loads dynamically to improve performance on specialized tasks. Skills teach Claude how to complete specific tasks in a repeatable way, whether that's creating documents with your company's brand guidelines, analyzing data using your organization's specific workflows, or automating personal tasks.

For more information, check out:
- [What are skills?](https://support.claude.com/en/articles/12512176-what-are-skills)
- [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [How to create custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [Equipping agents for the real world with Agent Skills](https://anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)

# About This Repository

This repository contains skills that demonstrate what's possible with Claude's skills system. These skills range from creative applications (art, music, design) to technical tasks (testing web apps, MCP server generation, pre-deployment validation) to enterprise workflows (communications, branding, etc.).

Each skill is self-contained in its own folder with a `SKILL.md` file containing the instructions and metadata that Claude uses. Browse through these skills to get inspiration for your own skills or to understand different patterns and approaches.

Many skills in this repo are open source (Apache 2.0). We've also included the document creation & editing skills that power [Claude's document capabilities](https://www.anthropic.com/news/create-files) under the hood in the [`skills/docx`](./skills/docx), [`skills/pdf`](./skills/pdf), [`skills/pptx`](./skills/pptx), and [`skills/xlsx`](./skills/xlsx) subfolders. These are source-available, not open source, but we wanted to share these with developers as a reference for more complex skills that are actively used in a production AI application.

## Disclaimer

**These skills are provided for demonstration and educational purposes only.** While some of these capabilities may be available in Claude, the implementations and behaviors you receive from Claude may differ from what is shown in these skills. These skills are meant to illustrate patterns and possibilities. Always test skills thoroughly in your own environment before relying on them for critical tasks.

# Skill Sets
- [./skills](./skills): Skill examples for Creative & Design, Development & Technical, Enterprise & Communication, and Document Skills
- [./spec](./spec): The Agent Skills specification
- [./template](./template): Skill template

## Example Skills

### Creative & Design
| Skill | Description |
|---|---|
| [algorithmic-art](./skills/algorithmic-art) | Generative art using p5.js with seeded randomness, flow fields, and particle systems |
| [ascii-mockup](./skills/ascii-mockup) | Mobile-first ASCII art UI wireframes across 5 breakpoints with versioned design tokens, ARIA-compliant color palettes, CDN-served fonts, and zero-hardcode CSS — chains with ux-journey-mapper and frontend-design |
| [canvas-design](./skills/canvas-design) | Visual design in PNG/PDF — posters, artwork, and static design pieces |
| [frontend-design](./skills/frontend-design) | Production-grade web UIs: pages, components, dashboards, and HTML artifacts |
| [slack-gif-creator](./skills/slack-gif-creator) | Animated GIFs optimized for Slack with constraint validation and animation utilities |
| [theme-factory](./skills/theme-factory) | Apply or generate themes (colors, fonts) across slides, docs, and HTML artifacts |

### Development & Technical
| Skill | Description |
|---|---|
| [mcp-builder](./skills/mcp-builder) | Guide for building MCP servers in Python (FastMCP) or TypeScript to integrate external APIs |
| [pre-deploy-validator](./skills/pre-deploy-validator) | Pre-deployment flight checks: lint, security scanning, tests, dependency audit, and docs verification |
| [skill-creator](./skills/skill-creator) | Create, improve, and benchmark skills with evals and description optimization |
| [web-artifacts-builder](./skills/web-artifacts-builder) | Complex Claude.ai HTML artifacts using React, Tailwind CSS, and shadcn/ui |
| [webapp-testing](./skills/webapp-testing) | Interact with and test local web apps via Playwright — screenshots, logs, UI verification |

### Enterprise & Communication
| Skill | Description |
|---|---|
| [brand-guidelines](./skills/brand-guidelines) | Apply Anthropic brand colors and typography to any artifact |
| [doc-coauthoring](./skills/doc-coauthoring) | Structured workflow for co-authoring docs, proposals, specs, and decision documents |
| [internal-comms](./skills/internal-comms) | Internal communications: status reports, newsletters, FAQs, incident reports, and updates |

## Document Skills
| Skill | Description |
|---|---|
| [docx](./skills/docx) | Create, read, edit, and manipulate Word documents (.docx) |
| [pdf](./skills/pdf) | Read, combine, split, annotate, fill forms, and create PDF files |
| [pptx](./skills/pptx) | Create, edit, parse, and manipulate PowerPoint presentations (.pptx) |
| [xlsx](./skills/xlsx) | Open, edit, create, and convert spreadsheet files (.xlsx, .csv, .tsv) |

## API & SDK Skills
| Skill | Description |
|---|---|
| [claude-api](./skills/claude-api) | Reference docs and patterns for building apps with the Claude API and Anthropic SDKs |

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

After installing the plugin, you can use the skill by just mentioning it. For instance, if you install the `document-skills` plugin from the marketplace, you can ask Claude Code to do something like: "Use the PDF skill to extract the form fields from `path/to/some-file.pdf`"

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

---

## ASCII Mockup Skill — Demo

> **Skill invoked:** `ascii-mockup`
> **Project:** Taskflow — a minimal task-management web app
> **Stack:** React / Next.js · Tailwind-compatible tokens · Google Fonts CDN
> **Version:** 1.0.0 · 2026-03-26

### ARIA Color Palette

| Pair | Foreground | Background | Ratio | AA Normal | AA Large |
|---|---|---|---|---|---|
| Body text on surface | `#111827` | `#f9fafb` | **16.0:1** | ✅ | ✅ |
| CTA button label | `#ffffff` | `#2563eb` | **5.9:1** | ✅ | ✅ |
| Ghost button label | `#2563eb` | `#f9fafb` | **4.6:1** | ✅ | ✅ |
| Muted caption on surface | `#6b7280` | `#f9fafb` | **4.6:1** | ✅ | ✅ |
| Status error on surface | `#b91c1c` | `#f9fafb` | **7.1:1** | ✅ | ✅ |

All pairs meet **WCAG 2.1 AA**. Dark-mode overrides swap surface and text tokens automatically.

---

### tokens.css (excerpt — zero hardcoded values after `:root`)

```css
@import url('https://fonts.googleapis.com/css2?family=Syne:wght@700;800&family=DM+Sans:wght@400;500;600&family=JetBrains+Mono:wght@400;500&display=swap');

:root {
  --color-brand-primary:    #2563eb;
  --color-brand-secondary:  #0891b2;
  --color-brand-accent:     #7c3aed;

  --color-action-primary:   var(--color-brand-primary);
  --color-action-ghost:     transparent;
  --color-surface-base:     var(--color-neutral-50);
  --color-surface-elevated: var(--color-neutral-0);
  --color-text-primary:     var(--color-neutral-900);
  --color-text-muted:       var(--color-neutral-500);
  --color-border-default:   var(--color-neutral-200);

  --font-display: 'Syne', serif;
  --font-body:    'DM Sans', sans-serif;
  --font-mono:    'JetBrains Mono', monospace;

  --type-scale-base: 1rem;
  --type-scale-3xl:  1.875rem;
  --space-4:         1rem;
  --radius-lg:       0.5rem;
  --shadow-md:       0 4px 6px -1px rgb(0 0 0 / 0.1), 0 2px 4px -2px rgb(0 0 0 / 0.1);
  --duration-normal: 200ms;
  --ease-default:    cubic-bezier(0.4, 0, 0.2, 1);
}

@media (prefers-color-scheme: dark) {
  :root {
    --color-surface-base:     var(--color-neutral-950);
    --color-surface-elevated: var(--color-neutral-900);
    --color-text-primary:     var(--color-neutral-50);
    --color-text-muted:       var(--color-neutral-400);
    --color-border-default:   var(--color-neutral-700);
  }
}

@media (prefers-reduced-motion: reduce) {
  :root { --duration-normal: 0ms; --duration-fast: 0ms; --duration-slow: 0ms; }
}
```

---

### ASCII Wireframes — All 5 Breakpoints

#### `xs` — iPhone 720 · 390px · 48 cols

```
╔════════════════════════════════════════════════╗
║  BREAKPOINT: xs — iPhone 720 · 390px · 48 cols ║
╚════════════════════════════════════════════════╝
┌────────────────────────────────────────────────┐
│ ▓ status bar                        9:41 ▲ ●●  │
├────────────────────────────────────────────────┤
│ ☰  Taskflow                              🔔 👤  │
│    // NAV: sticky · z var(--z-sticky)          │
├────────────────────────────────────────────────┤
│                                                │
│  ┌──────────────────────────────────────────┐  │
│  │  Good morning, Alex 👋                   │  │
│  │  You have 4 tasks due today              │  │
│  └──────────────────────────────────────────┘  │
│  // font: var(--font-display)                  │
│  // size: var(--type-scale-3xl)                │
│                                                │
│  ┌──────────────────────────────────────────┐  │
│  │ 🔍  Search tasks…                        │  │
│  └──────────────────────────────────────────┘  │
│  // input: min-height var(--space-12)          │
│                                                │
│  ── TODAY ──────────────────────────── 4/7 ──  │
│  ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓░░░░░░░░░░░░░░░░░░░░  │
│  // progress: var(--color-brand-primary)       │
│                                                │
│  ╔══════════════════════════════════════════╗  │
│  ║ ☐  Write Q2 report          [DUE TODAY]  ║  │
│  ║    Project: Marketing · 🔴 High          ║  │
│  ╚══════════════════════════════════════════╝  │
│  ╔══════════════════════════════════════════╗  │
│  ║ ☐  Review PR #47            [DUE TODAY]  ║  │
│  ║    Project: Engineering · 🟡 Medium      ║  │
│  ╚══════════════════════════════════════════╝  │
│  ╔══════════════════════════════════════════╗  │
│  ║ ☑  Team standup             [DONE]       ║  │
│  ║    Project: General · 🟢 Low            ║  │
│  ╚══════════════════════════════════════════╝  │
│  // card: var(--shadow-md) var(--radius-lg)    │
│  // spacing: var(--space-4) padding            │
│                                                │
│  ┌──────────────────────────────────────────┐  │
│  │         [+ Add New Task]                 │  │
│  └──────────────────────────────────────────┘  │
│  // CTA: var(--color-action-primary)           │
│  // min-height: 44px (touch target WCAG 2.5.5) │
│                                                │
├────────────────────────────────────────────────┤
│   🏠 Home   📋 Tasks   📊 Board   👤 Profile   │
│ // bottom nav: env(safe-area-inset-bottom)     │
└────────────────────────────────────────────────┘
```

---

#### `sm` — iPad · 768px · 96 cols

```
╔════════════════════════════════════════════════════════════════════════════════════════════════╗
║  BREAKPOINT: sm — iPad · 768px · 96 cols                                                       ║
╚════════════════════════════════════════════════════════════════════════════════════════════════╝
┌────────────────────────────────────────────────────────────────────────────────────────────────┐
│  Taskflow                       🔍 Search tasks…                          🔔  Alex ▾           │
│  // NAV: full horizontal · var(--z-sticky)                                                     │
├──────────────────┬─────────────────────────────────────────────────────────────────────────────┤
│ SIDEBAR (240px)  │  MAIN CONTENT                                                               │
│ ──────────────── │  ─────────────────────────────────────────────────────────────────────────  │
│ 📋 My Tasks      │  Good morning, Alex 👋    ▓▓▓▓▓▓▓▓▓▓▓▓░░░░░░  4 of 7 complete             │
│ 📊 Board         │                                                                             │
│ 📁 Projects    ▾ │  ┌───────────────────────────────┐  ┌───────────────────────────────────┐  │
│   · Marketing    │  │ ☐ Write Q2 report  [DUE TODAY] │  │ ☐ Design system audit  [TOMORROW] │  │
│   · Engineering  │  │ Marketing · 🔴 High            │  │ Design · 🟡 Medium                │  │
│   · Design       │  │              [Edit] [Complete] │  │                    [Edit][Complete]│  │
│ 📅 Calendar      │  └───────────────────────────────┘  └───────────────────────────────────┘  │
│ ──────────────── │  ┌───────────────────────────────┐  ┌───────────────────────────────────┐  │
│ FILTERS          │  │ ☐ Review PR #47    [DUE TODAY] │  │ ☑ Team standup          [DONE]    │  │
│ Priority  ▾      │  │ Engineering · 🟡 Medium        │  │ General · 🟢 Low                  │  │
│ Project   ▾      │  │              [Edit] [Complete] │  │                    [Reopen][View]  │  │
│ Date      ▾      │  └───────────────────────────────┘  └───────────────────────────────────┘  │
│ ──────────────── │                                                                             │
│ [+ New Task]     │                           [+ Add New Task]                                  │
└──────────────────┴─────────────────────────────────────────────────────────────────────────────┘
// SIDEBAR: width 240px · var(--color-surface-elevated) · var(--shadow-md)
// GRID: 2-col cards · gap var(--space-6)
// [+ New Task] sidebar btn: var(--color-action-primary) · width 100%
```

---

#### `md` — Desktop 1440 · 1440px · 180 cols

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╗
║  BREAKPOINT: md — Desktop 1440 · 1440px · 180 cols                                                                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╝
┌──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│  🗂 Taskflow        📋 My Tasks   📊 Board   📁 Projects   📅 Calendar          🔍 Search tasks…                                     🔔  [+ New Task]   Alex ▾                   │
├────────────────┬───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┬─────────────────────────────┤
│  SIDEBAR       │  TASK LIST                                                                                                                         │  TASK DETAIL PANEL          │
│  ──────────    │  ─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── │  ─────────────────────────  │
│  📋 My Tasks   │  FILTERS: [All ▾] [Priority ▾] [Project ▾] [Due Date ▾] [Assignee ▾]                              Sort: Due Date ▲   View: ☰ ⊞  │  Write Q2 report            │
│  📊 Board      │  ──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── │                             │
│  📁 Projects ▾ │   ☐  Write Q2 report        Marketing    🔴 High    Alex      Due: Today     ▓ 0%   [Edit] [Complete] [···]                      │  📁 Marketing               │
│   · Marketing  │   ☐  Review PR #47           Engineering  🟡 Medium  Jordan    Due: Today     ▓ 0%   [Edit] [Complete] [···]                      │  🔴 High · Due Today        │
│   · Design     │   ☐  Design system audit     Design       🟡 Medium  Sam       Due: Tomorrow  ▓ 25%  [Edit] [Complete] [···]                      │                             │
│   · Engineering│   ☐  Update dependencies     Engineering  🟢 Low     Jordan    Due: Fri       ▓ 0%   [Edit] [Complete] [···]                      │  Description                │
│   · General    │   ☑  Team standup            General      🟢 Low     Team      Completed      ✓      [Reopen] [View]                              │  ┌─────────────────────┐   │
│  ──────────    │   ☐  Client call prep        Marketing    🔴 High    Alex      Due: Fri       ▓ 50%  [Edit] [Complete] [···]                      │  │ Draft the Q2 report │   │
│  PROJECTS      │   ☐  Accessibility review    Design       🟡 Medium  Sam       Due: Next Wk   ▓ 0%   [Edit] [Complete] [···]                      │  │ for stakeholders··· │   │
│  ──────────    │                                                                                                                                    │  └─────────────────────┘   │
│  [+ New Task]  │                                                   Showing 7 tasks                                                                 │                             │
│                │                                                                                                                                    │  Subtasks (0/3)             │
│                │                                                                                                                                    │  ☐ Gather metrics           │
│                │                                                                                                                                    │  ☐ Write exec summary       │
│                │                                                                                                                                    │  ☐ Peer review              │
│                │                                                                                                                                    │  [+ Add subtask]            │
└────────────────┴───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┴─────────────────────────────┘
// 3-PANEL: sidebar 200px · task list flex-1 · detail panel 320px
// ROW hover: var(--color-surface-elevated) · var(--duration-fast) transition
// DETAIL PANEL: var(--shadow-xl) on scroll enter
```

---

#### `lg` — Desktop 1920 · 1920px · 240 cols

```
╔════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╗
║  BREAKPOINT: lg — Desktop 1920 · 1920px · 240 cols                                                                                                                                                                                        ║
╚════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╝
┌────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│  🗂 Taskflow     📋 Tasks   📊 Board   📁 Projects   📅 Calendar   📈 Analytics                    🔍 Search tasks…                                                    🔔  [+ New Task]   Alex ▾   ⚙                                       │
├──────────────┬─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┬──────────────────────────────────────────────────────────────────────┤
│ SIDEBAR 240px│  TASK BOARD — KANBAN                                                                                                                                  │  ANALYTICS PANEL (320px)                                             │
│ ──────────── │  ────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── │  ────────────────────────────────────────────────────────────────── │
│ 📋 My Tasks  │  ┌─────────────────────┐  ┌─────────────────────┐  ┌─────────────────────┐  ┌─────────────────────┐  ┌─────────────────────┐                        │  COMPLETION TREND                                                    │
│ 📊 Board     │  │ 📥 BACKLOG (12)      │  │ 📋 TO DO (5)         │  │ 🔄 IN PROGRESS (3)   │  │ 👀 REVIEW (2)        │  │ ✅ DONE (7)          │                        │  ┌────────────────────────────────────────────────────────────┐   │
│ 📁 Projects  │  │ ─────────────────── │  │ ─────────────────── │  │ ─────────────────── │  │ ─────────────────── │  │ ─────────────────── │                        │  │  10 │                                      ▂▄▆█             │   │
│  Marketing   │  │ ╔═══════════════╗   │  │ ╔═══════════════╗   │  │ ╔═══════════════╗   │  │ ╔═══════════════╗   │  │ ╔═══════════════╗   │                        │  │   8 │                             ▂▄▆▄▆▄█▄█▆              │   │
│  Engineering │  │ ║ Update deps   ║   │  │ ║ Write Q2 rpt  ║   │  │ ║ Design audit  ║   │  │ ║ Review PR#47  ║   │  │ ║ Team standup  ║   │                        │  │   6 │                    ▂▄▆▄▂▄▆▄                         │   │
│  Design      │  │ ║ Eng · 🟢 Low  ║   │  │ ║ Mkt · 🔴 High ║   │  │ ║ Dsgn ·🟡 Med ║   │  │ ║ Eng ·🟡 Med  ║   │  │ ║ Gen · 🟢 Low  ║   │                        │  │   4 │          ▂▄▆▄▂▄                                     │   │
│  General     │  │ ╚═══════════════╝   │  │ ╚═══════════════╝   │  │ ║ ▓▓▓░░░ 25%   ║   │  │ ╚═══════════════╝   │  │ ╚═══════════════╝   │                        │  │   2 │  ▂▄▄▄▂                                               │   │
│  ──────────  │  │ ···                 │  │ ···                 │  │ ╚═══════════════╝   │  │ ···                 │  │ ···                 │                        │  │   0 └───────────────────────────────────────────────────────   │   │
│  📅 Calendar │  │                     │  │                     │  │                     │  │                     │  │                     │                        │  │       Mon  Tue  Wed  Thu  Fri  Sat  Sun  Mon  Tue  Wed        │   │
│  📈 Analytics│  │ [+ Add card]        │  │ [+ Add card]        │  │ [+ Add card]        │  │ [+ Add card]        │  │ [+ Add card]        │                        │  └────────────────────────────────────────────────────────────┘   │
│  ──────────  │  └─────────────────────┘  └─────────────────────┘  └─────────────────────┘  └─────────────────────┘  └─────────────────────┘                        │  // chart: inline SVG · colors via currentColor                     │
│  [+ New Task]│                                                                                                                                                  │  ────────────────────────────────────────────────────────────────── │
│              │                                                                                                                                                  │  BY PROJECT         TASKS   DONE   %                                │
│              │                                                                                                                                                  │  Marketing          ▓▓▓▓▓▓▓▓░░░░    5   2   40%                    │
│              │                                                                                                                                                  │  Engineering        ▓▓▓▓▓▓░░░░░░    4   2   50%                    │
│              │                                                                                                                                                  │  Design             ▓▓▓▓░░░░░░░░    3   1   33%                    │
│              │                                                                                                                                                  │  General            ▓▓▓▓▓▓▓▓▓▓▓▓    2   2  100%                    │
└──────────────┴─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┴──────────────────────────────────────────────────────────────────────┘
// KANBAN: horizontal scroll on md, native grid on lg · overflow-x auto
// ANALYTICS: sticky right panel, collapsible · var(--shadow-xl)
// CHART: CSS custom-prop colors, no hardcoded fills
```

---

#### `xl` — UWHD 21:9 · 3440px · 430 cols (center-locked max-width)

```
╔════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╗
║  BREAKPOINT: xl — UWHD 21:9 · 3440px · 430 cols  [max-width: 1920px centered, gutters fill remainder]                                                                                                                                                                                                                                                                                                                      ║
╚════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╝
░░░░ GUTTER (auto) ░░░░┌──────────────────── max-width: 1920px  [identical to lg layout, locked center] ──────────────────────┐░░░░ GUTTER (auto) ░░░░
                        │  🗂 Taskflow  [full lg layout reproduced here — sidebar + kanban + analytics]                        │
                        │  // BODY: background var(--color-surface-base) extends edge-to-edge (gutters bleed)                  │
                        │  // CONTENT: max-width 1920px; margin-inline auto                                                   │
                        │  // GUTTER COLOR: var(--color-surface-base) — no harsh edge                                         │
                        │  // FONT: same scale as lg — no increase to avoid readability issues at distance                    │
                        └────────────────────────────────────────────────────────────────────────────────────────────────────────┘
// UWHD STRATEGY: center-lock with max-width. Never stretch content to full 3440px.
// Gutters intentionally use surface-base to feel like ambient background, not dead space.
// Optional: add a subtle ambient illustration or gradient in the gutter zone.
```

---

### Component Directory Scaffold (React / Next.js)

```
src/
  design-system/
    tokens/
      tokens.json                ← source of truth (v1.0.0)
      tokens.css                 ← compiled CSS custom props + Google Fonts @import
      tokens.ts                  ← typed JS: export const color, space, shadow …
    components/
      primitives/
        Button/
          Button.tsx             ← variant: primary | ghost | danger
          Button.module.css      ← uses only var(--*) tokens
        Input/
        Badge/
        Avatar/
        Icon/
      layout/
        Container/               ← max-width + margin-inline auto
        Grid/                    ← 12-col responsive
        Stack/                   ← vertical / horizontal spacing
        Divider/
      navigation/
        Navbar/
        Sidebar/
        BottomNav/               ← xs only
        Breadcrumb/
        Tabs/
      feedback/
        Toast/
        Alert/
        Modal/
        Skeleton/
        ProgressBar/
      data-display/
        TaskCard/                ← maps to ╔══╗ card in mockup
        KanbanColumn/
        StatBar/
        MiniChart/
      forms/
        Form/
        Field/
        Select/
        Checkbox/
        Radio/
      media/
        AspectRatio/
        LazyImage/
    mockups/
      xs/  taskflow-dashboard.txt
      sm/  taskflow-dashboard.txt
      md/  taskflow-dashboard.txt
      lg/  taskflow-dashboard.txt
      xl/  taskflow-dashboard.txt
      CHANGELOG.md
      VERSION
```

---

### mockups/CHANGELOG.md

```markdown
## [1.0.0] — 2026-03-26

### Added
- Initial 5-breakpoint mockup set: xs, sm, md, lg, xl
- Design token manifest: tokens.json + tokens.css
- ARIA color palette — all pairs meet WCAG 2.1 AA
- Google Fonts CDN: Syne (display) + DM Sans (body) + JetBrains Mono
- Component scaffold for React / Next.js
- Dark mode token overrides
- prefers-reduced-motion support
```

### mockups/VERSION

```
1.0.0
```

---

### Skill Chain — Next Steps

```
Step 1 ✅  ascii-mockup     → wireframes + tokens (complete)
Step 2 →   ux-journey-mapper → overlay task-creation & completion journey on mockup screens
Step 3 →   frontend-design   → production HTML/CSS/React using tokens.css as the style foundation
```

To continue, say: **"Map the task creation journey"** or **"Build the production frontend from these tokens."**

---

# Partner Skills

Skills are a great way to teach Claude how to get better at using specific pieces of software. As we see awesome example skills from partners, we may highlight some of them here:

- **Notion** - [Notion Skills for Claude](https://www.notion.so/notiondevs/Notion-Skills-for-Claude-28da4445d27180c7af1df7d8615723d0)
