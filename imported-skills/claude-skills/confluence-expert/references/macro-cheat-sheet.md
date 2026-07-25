# Confluence Macro Cheat Sheet

## Overview

Quick reference for the most commonly used Confluence macros. Each entry includes the macro name, storage format syntax, primary use case, and practical tips.

## Navigation & Structure Macros

### Table of Contents
- **Purpose:** Auto-generate a linked table of contents from page headings
- **Syntax:** `<ac:structured-macro ac:name="toc" />`
- **Parameters:** `maxLevel` (1-6), `minLevel` (1-6), `style` (disc, circle, square, none), `type` (list, flat)
- **Use case:** Long documentation pages, meeting notes, specifications
- **Tip:** Set `maxLevel="3"` to avoid overly deep TOC entries

### Children Display
- **Purpose:** List child pages of the current page
- **Syntax:** `<ac:structured-macro ac:name="children" />`
- **Parameters:** `depth` (1-999), `sort` (title, creation, modified), `style` (h2-h6), `all` (true/false)
- **Use case:** Parent hub pages, project homepages, documentation indexes
- **Tip:** Use `depth="1"` for clean navigation, `all="true"` for deep hierarchies

### Include Page
- **Purpose:** Embed content from another page inline
- **Syntax:** `<ac:structured-macro ac:name="include"><ac:parameter ac:name=""><ac:link><ri:page ri:content-title="Page Name" /></ac:link></ac:parameter></ac:structured-macro>`
- **Use case:** Reusable content blocks (headers, footers, disclaimers)
- **Tip:** Changes to the source page are reflected everywhere it is included

### Page Properties
- **Purpose:** Define structured metadata on a page (key-value pairs)
- **Syntax:** `<ac:structured-macro ac:name="details">` with table inside
- **Use case:** Project metadata, status tracking, structured page data
- **Tip:** Combine with Page Properties Report macro to create dashboards

### Page Properties Report
- **Purpose:** Display a table of Page Properties from child pages
- **Syntax:** `<ac:structured-macro ac:name="detailssummary" />`
- **Parameters:** `cql` (CQL filter), `labels` (filter by label)
- **Use case:** Project dashboards, status rollups, portfolio views
- **Tip:** Use labels to scope the report to relevant pages only

## Visual & Formatting Macros

### Info Panel
- **Purpose:** Blue information callout box
- **Syntax:** `<ac:structured-macro ac:name="info"><ac:rich-text-body>Content</ac:rich-text-body></ac:structured-macro>`
- **Use case:** Helpful notes, additional context, best practices

### Warning Panel
- **Purpose:** Yellow warning callout box
- **Syntax:** `<ac:structured-macro ac:name="warning"><ac:rich-text-body>Content</ac:rich-text-body></ac:structured-macro>`
- **Use case:** Important caveats, deprecation notices, breaking changes

### Note Panel
- **Purpose:** Yellow note callout box
- **Syntax:** `<ac:structured-macro ac:name="note"><ac:rich-text-body>Content</ac:rich-text-body></ac:structured-macro>`
- **Use case:** Reminders, action items, things to watch

### Tip Panel
- **Purpose:** Green tip callout box
- **Syntax:** `<ac:structured-macro ac:name="tip"><ac:rich-text-body>Content</ac:rich-text-body></ac:structured-macro>`
- **Use case:** Pro tips, shortcuts, recommended approaches

### Expand
- **Purpose:** Collapsible content section (click to expand)
- **Syntax:** `<ac:structured-macro ac:name="expand"><ac:parameter ac:name="title">Click to expand</ac:parameter><ac:rich-text-body>Hidden content</ac:rich-text-body></ac:structured-macro>`
- **Use case:** Long sections, FAQs, detailed explanations, optional reading
- **Tip:** Use for content that not all readers need

### Status
- **Purpose:** Colored status lozenge (inline label)
- **Syntax:** `<ac:structured-macro ac:name="status"><ac:parameter ac:name="colour">Green</ac:parameter><ac:parameter ac:name="title">DONE</ac:parameter></ac:structured-macro>`
- **Colors:** Grey, Red, Yellow, Green, Blue
- **Use case:** Task status, review state, approval status
- **Tip:** Standardize status values across your team (e.g., TODO, IN PROGRESS, DONE)

## Integration Macros

### Jira Issues
- **Purpose:** Display Jira issues or JQL query results
- **Syntax:** `<ac:structured-macro ac:name="jira"><ac:parameter ac:name="jqlQuery">project = PROJ AND status = Open</ac:parameter></ac:structured-macro>`
- **Parameters:** `jqlQuery`, `columns` (key, summary, status, assignee, etc.), `count` (true/false), `serverId`
- **Use case:** Sprint boards in documentation, requirement traceability, release notes
- **Tip:** Use `columns` parameter to show only relevant fields

### Roadmap Planner
- **Purpose:** Visual timeline/Gantt view of items
- **Syntax:** Available via macro browser (Roadmap Planner)
- **Use case:** Project timelines, release planning, milestone tracking
- **Tip:** Link roadmap items to Jira epics for automatic status updates

### Chart Macro
- **Purpose:** Create charts from table data on the page
- **Syntax:** `<ac:structured-macro ac:name="chart"><ac:parameter ac:name="type">pie</ac:parameter><ac:rich-text-body>Table data</ac:rich-text-body></ac:structured-macro>`
- **Types:** pie, bar, line, area, scatter, timeSeries
- **Use case:** Status distribution, metrics dashboards, trend visualization
- **Tip:** Place a Confluence table inside the macro body as data source

## Content Reuse Macros

### Excerpt
- **Purpose:** Mark a section of content for reuse via Excerpt Include
- **Syntax:** `<ac:structured-macro ac:name="excerpt"><ac:rich-text-body>Reusable content</ac:rich-text-body></ac:structured-macro>`
- **Use case:** Define canonical content blocks (product descriptions, team info)

### Excerpt Include
- **Purpose:** Display an Excerpt from another page
- **Syntax:** `<ac:structured-macro ac:name="excerpt-include"><ac:parameter ac:name=""><ac:link><ri:page ri:content-title="Source Page" /></ac:link></ac:parameter></ac:structured-macro>`
- **Use case:** Embed product descriptions, standard disclaimers, shared definitions

## Advanced Macros

### Code Block
- **Purpose:** Display formatted code with syntax highlighting
- **Syntax:** `<ac:structured-macro ac:name="code"><ac:parameter ac:name="language">python</ac:parameter><ac:plain-text-body>code here</ac:plain-text-body></ac:structured-macro>`
- **Languages:** java, python, javascript, sql, bash, xml, json, and many more
- **Use case:** API documentation, configuration examples, code snippets

### Anchor
- **Purpose:** Create a named anchor point for deep linking
- **Syntax:** `<ac:structured-macro ac:name="anchor"><ac:parameter ac:name="">anchor-name</ac:parameter></ac:structured-macro>`
- **Use case:** Link directly to specific sections within long pages
- **Tip:** Use with TOC macro for custom navigation

### Recently Updated
- **Purpose:** Show recently modified pages in a space
- **Syntax:** `<ac:structured-macro ac:name="recently-updated" />`
- **Parameters:** `spaces`, `labels`, `types`, `max`
- **Use case:** Team dashboards, space homepages, activity feeds

## Macro Selection Guide

| Need | Recommended Macro |
|------|------------------|
| Page navigation | Table of Contents |
| List child pages | Children Display |
| Reuse content | Include Page or Excerpt Include |
| Status tracking | Status + Page Properties |
| Project dashboard | Page Properties Report |
| Hide optional content | Expand |
| Show Jira data | Jira Issues |
| Visualize data | Chart |
| Code documentation | Code Block |
| Important callouts | Info/Warning/Note/Tip panels |
