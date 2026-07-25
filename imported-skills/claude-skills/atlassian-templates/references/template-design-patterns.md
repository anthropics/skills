# Template Design Patterns

## Overview

Well-designed Confluence and Jira templates accelerate team productivity by providing consistent starting points for common documents and workflows. This guide covers design patterns, variable handling, and best practices for creating reusable templates.

## Variable Placeholders

### Confluence Template Variables

**Syntax:** `<at:var at:name="variableName">default value</at:var>`

**Common Variables:**
| Variable | Purpose | Example Default |
|----------|---------|----------------|
| `projectName` | Project identifier | "Project Name" |
| `author` | Document author | "@mention author" |
| `date` | Creation or target date | "YYYY-MM-DD" |
| `status` | Current document status | "Draft" |
| `version` | Document version | "1.0" |
| `owner` | Responsible person | "@mention owner" |
| `reviewers` | Review participants | "@mention reviewers" |

**Best Practices:**
- Use descriptive variable names (camelCase)
- Always provide meaningful default values
- Group related variables together
- Include instruction text that users should replace
- Use Status macro for status variables (visual clarity)

### Jira Template Fields

**Custom Fields for Templates:**
- Text fields for structured input
- Select lists for controlled vocabularies
- Date fields for milestones
- User pickers for assignments
- Labels for categorization

## Conditional Sections

### Pattern: Role-Based Sections

Include or exclude content based on the document's audience:

```
## For Engineering (delete if not applicable)
- Technical requirements
- Architecture decisions
- Performance criteria

## For Design (delete if not applicable)
- User flows
- Wireframes
- Accessibility requirements

## For Business (delete if not applicable)
- ROI analysis
- Market context
- Success metrics
```

### Pattern: Complexity-Based Sections

Scale content depth based on project size:

```
## Required for All Projects
- Problem statement
- Solution overview
- Success metrics

## Required for Medium+ Projects (>2 weeks)
- Detailed requirements
- Technical design
- Test plan

## Required for Large Projects (>1 month)
- Architecture review
- Security review
- Rollback plan
- Communication plan
```

### Pattern: Optional Deep Dives

Use Expand macros for optional detail:

```
[Expand: Detailed Requirements]
  Content that power users may need but casual readers can skip
[/Expand]
```

## Reusable Components

### Header Block
Every template should start with a consistent header:

```
| Field | Value |
|-------|-------|
| Author | @mention |
| Status | [Status Macro: Draft] |
| Created | [Date] |
| Last Updated | [Date] |
| Reviewers | @mention |
| Approver | @mention |
```

### Decision Log Component
Reusable across templates that involve decisions:

```
## Decision Log
| # | Decision | Date | Decided By | Rationale |
|---|----------|------|-----------|-----------|
| 1 | [Decision] | [Date] | [Name] | [Why] |
```

### Change History Component
Track document evolution:

```
## Change History
| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | [Date] | [Name] | Initial version |
```

### Action Items Component
Standard task tracking:

```
## Action Items
- [ ] [Task description] - @assignee - Due: [date]
- [ ] [Task description] - @assignee - Due: [date]
```

## Macro Integration

### Recommended Macros per Template Type

**Meeting Notes Template:**
- Table of Contents (for long meetings)
- Action Items (task list macro)
- Jira Issues (link to discussed tickets)
- Expand (for detailed discussion notes)

**Decision Record Template:**
- Status macro (decision status)
- Page Properties (structured metadata)
- Info/Warning panels (context and caveats)
- Jira Issues (related tickets)

**Project Plan Template:**
- Roadmap Planner (timeline view)
- Jira Issues (JQL for project epics)
- Children Display (sub-pages for phases)
- Chart macro (status distribution)

**Runbook Template:**
- Code Block (commands and scripts)
- Warning panels (danger zones)
- Expand (detailed troubleshooting)
- Anchor links (quick navigation)

## Responsive Layouts

### Two-Column Layout
Use Confluence Section and Column macros:

```
[Section]
  [Column: 60%]
    Main content, description, details
  [/Column]
  [Column: 40%]
    Sidebar: metadata, quick links, status
  [/Column]
[/Section]
```

### Card Layout
For overview pages with multiple items:

```
[Section]
  [Column: 33%]
    [Panel: Card 1]
      Title, summary, link
    [/Panel]
  [/Column]
  [Column: 33%]
    [Panel: Card 2]
  [/Column]
  [Column: 33%]
    [Panel: Card 3]
  [/Column]
[/Section]
```

## Brand Consistency

### Visual Standards
- Use consistent heading levels (H1 for title, H2 for sections, H3 for subsections)
- Apply Info/Warning/Note panels consistently (same meaning across templates)
- Use Status macro colors consistently (Green=done, Yellow=in progress, Red=blocked)
- Maintain consistent table formatting (header row, alignment)

### Content Standards
- Use the same voice and tone across templates
- Standardize date format (YYYY-MM-DD or your organization's preference)
- Use consistent terminology (define terms in a glossary)
- Include the same footer/metadata block in all templates

## Versioning Strategy

### Template Version Control
- Include version number in template metadata
- Maintain a changelog for template updates
- Communicate template changes to users
- Keep previous versions accessible during transition periods

### Version Numbering
- **Major (2.0):** Structural changes, section additions/removals
- **Minor (1.1):** Content updates, improved instructions
- **Patch (1.0.1):** Typo fixes, formatting corrections

### Migration Path
When updating templates:
1. Create new version alongside old version
2. Announce change with migration guide
3. New documents use new template automatically
4. Existing documents do not need to be migrated (optional)
5. Deprecate old template after 90 days
6. Archive old template (do not delete)

## Template Catalog Organization

### Categorization
Organize templates by:
- **Document type:** Meeting notes, decisions, plans, runbooks
- **Team:** Engineering, product, marketing, HR
- **Lifecycle:** Planning, execution, review, retrospective
- **Frequency:** One-time, recurring, as-needed

### Discovery
- Maintain a "Template Index" page with descriptions and links
- Tag templates with consistent labels
- Include a "When to Use" section in each template
- Provide examples of completed documents using the template
