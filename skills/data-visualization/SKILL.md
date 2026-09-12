---
name: data-visualization
description: >
  Design and produce data visualizations for program evaluation, reporting, and stakeholder
  communication in educational and nonprofit contexts. Use this skill whenever the user mentions
  dashboards, charts, graphs, infographics, data displays, scorecards, KPI summaries, program
  reports, funder reports, evaluation summaries, or wants to visualize any kind of outcome,
  indicator, or performance data — even if they don't use the word "visualization." Trigger also
  when the user shares a data table, CSV, or Excel file and wants to present, communicate, or
  report it. Covers all output formats: interactive HTML/React dashboards, static SVG/PNG charts,
  slide-ready infographics, and printable PDF reports. Aligns to Kirkpatrick, Logic Model/Theory
  of Change, ESSA/Title I, and nonprofit funder reporting standards. Always recommend chart type
  before building. Always apply WCAG 2.1 accessibility standards.
---

# Data Visualization Skill

Produces publication-ready data visualizations for education and nonprofit contexts across four
output formats, four evaluation/reporting frameworks, and four stakeholder audiences.

---

## Step 1 — Intake and Clarification

Before building anything, gather:

### 1a. Data Source
Determine how data is arriving:

| Input Type | Action |
|---|---|
| **Pasted CSV / table text** | Parse inline; confirm column headers and data types |
| **Uploaded Excel/CSV file** | Read file from `/mnt/user-data/uploads`; preview first 10 rows; confirm structure |
| **Verbal description** | Elicit values explicitly: ask for labels, numbers, time periods, and N |
| **No data yet** | Offer to generate a realistic sample dataset matching the user's program context |

Always confirm: unit of analysis, time period(s), population/sample, and whether values are counts, percentages, or rates.

### 1b. Purpose and Audience
Ask (or infer from context):
- **Purpose**: Is this for internal reflection, external reporting, a funder deliverable, a board deck, a school improvement plan, or policy testimony?
- **Audience**: School/district leadership · Nonprofit board/funders · Government/policy stakeholders · Teachers/instructional coaches
- **Framework in use** (see Step 2 for alignment logic)

### 1c. Output Format
If not specified, use this decision guide:

| Use Case | Recommended Format |
|---|---|
| Live presentation / board meeting | Interactive HTML/React dashboard |
| Funder report / annual report | Printable PDF with embedded visuals |
| Slide deck / stakeholder briefing | Slide-ready infographic (SVG/PNG, 16:9 or 4:3) |
| Quick single metric or comparison | Static chart (SVG/PNG) |
| Internal team monitoring | Interactive HTML dashboard |

---

## Step 2 — Framework Alignment

Match visualization structure to the reporting framework in use. Read the relevant reference file before building.

| Framework | Reference File | Key Visual Elements |
|---|---|---|
| **Kirkpatrick (L1–L4)** | `references/kirkpatrick.md` | Level-by-level outcome ladder; reaction → learning → behavior → results |
| **Logic Model / Theory of Change** | `references/logic-model.md` | Input → Activity → Output → Outcome → Impact flow |
| **ESSA / Title I** | `references/essa-title1.md` | Subgroup disaggregation; proficiency targets; evidence tiers |
| **Nonprofit Funder Reporting** | `references/funder-reporting.md` | Goal–metric–actual–variance table; narrative + data integration |

If the user hasn't named a framework but the context implies one (e.g., "grant report," "PD evaluation," "school accountability"), infer and confirm before proceeding.

---

## Step 3 — Chart Type Recommendation

**Always recommend the chart type before building.** Present the recommendation with a one-sentence rationale.

Use this decision matrix:

| Data Structure | Goal | Recommended Chart |
|---|---|---|
| One metric vs. target | Status at a point in time | Gauge / bullet chart |
| One metric over time | Trend | Line chart |
| Multiple categories, one period | Comparison | Horizontal bar chart |
| Multiple categories, multiple periods | Change over time by group | Grouped or stacked bar |
| Part-to-whole | Composition | Donut chart (≤5 segments); stacked bar (>5) |
| Two continuous variables | Correlation | Scatter plot |
| Geographic distribution | Spatial pattern | Choropleth map |
| Hierarchical outcomes (Kirkpatrick/Logic Model) | Program pathway | Sankey or flowchart |
| Subgroup performance gaps | Equity/disaggregation | Diverging bar or dot plot |
| Multiple KPIs at a glance | Dashboard summary | Scorecard / KPI card grid |

Avoid pie charts for more than 4 categories. Avoid 3D charts entirely (distorts perception). Avoid dual-axis charts unless the relationship between axes is explicitly the insight.

State the recommendation clearly:
> "For this data and goal, I recommend a **[chart type]** because **[one-sentence rationale]**. Want me to proceed with this, or would you prefer a different format?"

---

## Step 4 — Build the Visualization

### Output format specifications:

#### Interactive HTML/React Dashboard
- Use React with Recharts (`import { ... } from "recharts"`) or Chart.js
- Use Tailwind utility classes for layout
- Include: KPI cards at top, primary chart(s) in center, plain-language summary at bottom
- Add `aria-label` to all chart containers
- Export as `.jsx` artifact

#### Static Chart (SVG/PNG)
- Build as inline SVG
- Use CSS variables for color theming
- Minimum font size: 14px for labels, 12px for axis ticks
- Include title, subtitle, source line, and accessible alt-text block in a `<desc>` tag

#### Slide-Ready Infographic
- Target dimensions: 1280×720px (16:9) or 960×720px (4:3)
- Use high-contrast color palette (see Accessibility section)
- Minimal text; lead with the headline insight, not the data
- Embed a plain-language callout box with key takeaway
- Deliver as SVG or PNG

#### Printable PDF Report
- Read `/mnt/skills/public/pdf/SKILL.md` before building
- Structure: Cover → Executive Summary → Visualizations → Data Tables → Methodology note
- Use `reportlab` or `weasyprint` for generation
- Embed alt-text as hidden accessible text layer

---

## Step 5 — Accessibility Standards

Apply to **every output**, without exception:

| Standard | Requirement |
|---|---|
| **WCAG 2.1 AA Color Contrast** | Text on background: ≥4.5:1. Large text/icons: ≥3:1. Never use color alone to encode meaning — always pair with shape, pattern, or label |
| **Alt-text / Captions** | Every chart has a descriptive alt-text (what the chart shows + key finding). Every infographic has a caption. SVG uses `<title>` and `<desc>` tags |
| **Screen-reader HTML** | Use `role="img"` + `aria-label` on chart wrappers. Add a visually-hidden `<table>` version of the underlying data for screen readers |
| **Plain-language summary** | Every visualization includes a 2–3 sentence plain-language "What this shows" block, written at ≤8th grade reading level |

**Accessible color palettes** (WCAG AA compliant, colorblind-safe):
- Primary sequential: `#1a4e8c → #2176ae → #57a0d3 → #a8d1f0`
- Diverging (gap/equity): `#c0392b` (below) · `#f4f4f4` (neutral) · `#1a4e8c` (above)
- Categorical (up to 6): `#1a4e8c · #e67e22 · #27ae60 · #8e44ad · #c0392b · #16a085`
- Never use red/green as sole distinguishers (colorblind risk)

---

## Step 6 — Deliver and Document

After building:

1. **Present the visualization** using `present_files` if a file was created, or render inline as an artifact
2. **State the chart type and rationale** used (one sentence)
3. **Provide the plain-language summary** (2–3 sentences, ≤8th grade)
4. **Note the framework alignment** (e.g., "Aligned to Kirkpatrick Level 4 — Results")
5. **Offer one iteration prompt**: "Want me to adjust colors, add a comparison group, or export in a different format?"

---

## Edge Cases

| Situation | Handling |
|---|---|
| Data has too many categories (>10) | Recommend grouping small values into "Other"; ask user to confirm |
| Data is incomplete / has gaps | Flag explicitly; offer to interpolate, annotate gaps, or exclude — never silently fill |
| Conflicting frameworks in one report | Build modular sections; label each with its framework |
| User wants raw numbers only | Build a styled data table (not a chart); still apply accessibility standards |
| Sensitive subgroup data | Add a data privacy note; avoid displaying cells with N<10 |
| No data provided at all | Generate a realistic sample dataset, label it "Sample Data — Replace with Actuals," and build the visualization on that |
