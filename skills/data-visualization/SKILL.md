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

## Overview

Produces publication-ready data visualizations for education and nonprofit contexts across four output formats, four evaluation/reporting frameworks, and four stakeholder audiences.

**Always recommend the chart type before building.** State the chart type, explain why in one sentence, and ask for confirmation or adjustment.

## Audience and Framework Alignment

| Primary Audience | Data Goal | Preferred Output |
|---|---|---|
| Funders / Grantors | Impact and ROI | PDF report + infographic |
| School/district leadership | Program KPIs | Interactive dashboard |
| Teachers / instructional coaches | Student progress | Static chart (slide-ready) |
| Community / families | Accessible summary | Infographic with plain language |

| Framework | When to Apply | Key Visual Elements |
|---|---|---|
| Kirkpatrick (L1–L4) | Training evaluation | Cascade chart or 4-panel summary |
| Logic Model / Theory of Change | Program outcomes | Flow diagram (input → activity → output → outcome → impact) |
| ESSA/Title I Reporting | Federal compliance | Required disaggregation by subgroup |
| Nonprofit Funder Reporting | Grant accountability | Goal vs. actual comparison (bullet chart or progress bar) |

## Chart Type Recommendation Protocol

Always start by selecting the correct chart type before building. Use this selection matrix:

| Data Situation | Analytical Goal | Recommended Chart |
|---|---|---|
| One value over time | Trend | Line chart |
| Compare 2–7 categories at one point in time | Comparison | Bar chart (horizontal preferred for long labels) |
| Compare 2–7 categories over time | Change over time | Grouped bar or small multiples |
| Part-to-whole relationship (≤5 parts) | Composition | Donut chart (<=5 segments); stacked bar (>5) |
| Two continuous variables | Correlation | Scatter plot |
| Geographic distribution | Spatial pattern | Choropleth map |
| Hierarchical outcomes (Kirkpatrick/Logic Model) | Program pathway | Sankey or flowchart |
| Subgroup performance gaps | Equity/disaggregation | Diverging bar or dot plot |
| Multiple KPIs at a glance | Dashboard summary | Scorecard / KPI card grid |

Avoid pie charts for more than 4 categories. Avoid 3D charts entirely (distorts perception). Avoid dual-axis charts unless the relationship between axes is explicitly the insight.

State the recommendation clearly:
"For this data and goal, I recommend a **[chart type]** because **[one-sentence rationale]**. Want me to proceed with this, or would you prefer a different format?"

## Output Formats

### Interactive HTML/React Dashboard

Use React with Recharts or Chart.js
Use Tailwind utility classes for layout
Include: KPI cards at top, primary chart(s) in center, plain-language summary at bottom
Add aria-label to all chart containers
Export as .jsx artifact

### Static SVG/PNG Chart

Build as inline SVG
Use CSS variables for color theming
Minimum font size: 14px for labels, 12px for axis ticks
Include title, subtitle, source line, and accessible alt-text block in a desc tag

### Slide-Ready Infographic

Target dimensions: 1280x720px (16:9) or 960x720px (4:3)
Use high-contrast color palette (see Accessibility section)
Minimal text; lead with the headline insight, not the data
Embed a plain-language callout box with key takeaway
Deliver as SVG or PNG

### Printable PDF Report

Read /mnt/skills/public/pdf/SKILL.md before building
Structure: Cover > Executive Summary > Visualizations > Data Tables > Methodology note
Use reportlab or weasyprint for generation
Embed alt-text as hidden accessible text layer

## Accessibility Standards

Apply to **every output**, without exception:

| Standard | Requirement |
|---|---|
| WCAG 2.1 AA Color Contrast | Text on background: 4.5:1 minimum. Large text/icons: 3:1 minimum. Never use color alone to encode meaning |
| Alt-text / Captions | Every chart has a descriptive alt-text (what the chart shows + key finding). Every infographic has a caption |
| Screen-reader HTML | Use role="img" + aria-label on chart wrappers. Add a visually-hidden table version of the underlying data |
| Plain-language summary | Every visualization includes a 2-3 sentence plain-language "What this shows" block, written at 8th grade reading level or below |

**Accessible color palettes** (WCAG AA compliant, colorblind-safe):
Primary sequential: #1a4e8c > #2176ae > #57a0d3 > #a8d1f0
Diverging (gap/equity): Red (below) / Blue (above) scale
Categorical (up to 6): High-contrast, colorblind-safe palette

## Output Requirements

**Always include with every visualization:**
State the chart type and rationale used (one sentence)
Provide the plain-language summary (2-3 sentences, 8th grade reading level or below)
Note the framework alignment (e.g., "Aligned to Kirkpatrick Level 4 — Results")
Offer one iteration prompt: "Want me to adjust colors, add a comparison group, or export in a different format?"

## Edge Cases

| Situation | Handling |
|---|---|
| Data has too many categories (>10) | Recommend grouping small values into "Other"; ask user to confirm |
| Data is incomplete / has gaps | Flag explicitly; offer to interpolate, annotate gaps, or exclude — never silently fill |
| Conflicting frameworks in one report | Build modular sections; label each with its framework |
| User wants raw numbers only | Build a styled data table (not a chart); still apply accessibility standards |
| Sensitive subgroup data | Add a data privacy note; avoid displaying cells with N<10 |
| No data provided at all | Generate a realistic sample dataset, label it "Sample Data" and ask user to replace |
