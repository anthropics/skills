# Confluence Space Architecture Patterns

## Overview

Well-organized Confluence spaces dramatically improve information discoverability and team productivity. This guide covers proven space organization patterns, page hierarchy best practices, and governance strategies.

## Space Organization Patterns

### Pattern 1: By Team

Each team or department gets its own space.

**Structure:**
```
Engineering Space (ENG)
Product Space (PROD)
Marketing Space (MKT)
Design Space (DES)
Support Space (SUP)
```

**Pros:**
- Clear ownership and permissions
- Teams control their own content
- Natural permission boundaries
- Easy to find team-specific content

**Cons:**
- Cross-team content duplication
- Silos between departments
- Hard to find project-spanning information
- Inconsistent practices across spaces

**Best for:** Organizations with stable teams and clear departmental boundaries

### Pattern 2: By Project

Each major project or product gets its own space.

**Structure:**
```
Project Alpha Space (ALPHA)
Project Beta Space (BETA)
Platform Infrastructure Space (PLAT)
Internal Tools Space (TOOLS)
```

**Pros:**
- All project context in one place
- Easy onboarding for project members
- Clean archival when project completes
- Natural lifecycle management

**Cons:**
- Team knowledge scattered across spaces
- Permission management per project
- Space proliferation over time
- Ongoing vs project work separation unclear

**Best for:** Project-based organizations, agencies, consulting firms

### Pattern 3: By Domain (Hybrid)

Combine functional spaces with cross-cutting project spaces.

**Structure:**
```
Company Wiki (WIKI) - Shared knowledge
Engineering Standards (ENG) - Team practices
Product Specs (PROD) - Requirements and roadmap
Project Alpha (ALPHA) - Cross-team project
Project Beta (BETA) - Cross-team project
Archive (ARCH) - Completed projects
```

**Pros:**
- Balances team and project needs
- Shared knowledge has a home
- Clear archival path
- Scales with organization growth

**Cons:**
- More complex to set up initially
- Requires governance to maintain
- Some ambiguity about where content belongs

**Best for:** Growing organizations, 50-500 people, multiple concurrent projects

## Page Hierarchy Best Practices

### Recommended Depth
- **Maximum 4 levels deep** - Deeper hierarchies become hard to navigate
- **3 levels ideal** for most content types
- Use flat structures with labels for categorization beyond 4 levels

### Standard Page Hierarchy

```
Space Home (overview, quick links, recent updates)
├── Getting Started
│   ├── Onboarding Guide
│   ├── Tool Setup
│   └── Key Contacts
├── Projects
│   ├── Project Alpha
│   │   ├── Requirements
│   │   ├── Design
│   │   └── Meeting Notes
│   └── Project Beta
├── Processes
│   ├── Development Workflow
│   ├── Release Process
│   └── On-Call Runbook
├── References
│   ├── Architecture Decisions
│   ├── API Documentation
│   └── Glossary
└── Archive
    ├── 2025 Projects
    └── Deprecated Processes
```

### Page Naming Conventions
- Use clear, descriptive titles (not abbreviations)
- Include date for time-sensitive content: "2025-Q1 Planning"
- Prefix meeting notes with date: "2025-03-15 Sprint Review"
- Use consistent casing (Title Case or Sentence case, not both)
- Avoid special characters that break URLs

### Space Homepage Design
Every space homepage should include:
1. **Space purpose** - One paragraph describing what this space is for
2. **Quick links** - 5-7 most accessed pages
3. **Recent updates** - Recently Updated macro filtered to this space
4. **Getting started** - Link to onboarding content for new members
5. **Contact info** - Space owner, key contributors

## Labeling Taxonomy

### Label Categories
- **Content type:** `meeting-notes`, `decision`, `specification`, `runbook`, `retrospective`
- **Status:** `draft`, `in-review`, `approved`, `deprecated`, `archived`
- **Team:** `team-engineering`, `team-product`, `team-design`
- **Project:** `project-alpha`, `project-beta`
- **Priority:** `high-priority`, `p1`, `critical`

### Labeling Best Practices
- Use lowercase, hyphenated labels (no spaces or camelCase)
- Define a standard label vocabulary and document it
- Use labels for cross-space categorization
- Combine labels with CQL for powerful search and reporting
- Audit labels quarterly to remove unused or inconsistent labels
- Limit to 3-5 labels per page (over-labeling reduces value)

### CQL Examples for Label-Based Queries
```
# All meeting notes in a space
type = page AND space = "ENG" AND label = "meeting-notes"

# All approved specifications
type = page AND label = "specification" AND label = "approved"

# Recent decisions across all spaces
type = page AND label = "decision" AND lastModified > now("-30d")
```

## Cross-Space Linking

### When to Link vs Duplicate
- **Link** when content has a single source of truth
- **Duplicate** (Include Page macro) when content must appear in multiple contexts
- **Excerpt Include** when only a portion of a page is needed elsewhere

### Linking Best Practices
- Use full page titles in links for clarity
- Add context around links ("See the [Architecture Decision Record] for rationale")
- Avoid orphan pages - every page should be reachable from space navigation
- Use the Recently Updated macro on hub pages for activity visibility
- Create "Related Pages" sections at the bottom of content pages

## Archive Strategy

### When to Archive
- Project completed more than 90 days ago
- Process or document officially deprecated
- Content not updated in 12+ months
- Replaced by newer content

### Archive Process
1. Add `archived` label to the page
2. Move to Archive section within the space (or dedicated Archive space)
3. Add a note at the top: "This page is archived as of [date]. See [replacement] for current information."
4. Update any incoming links to point to current content
5. Do NOT delete - archived content has historical value

### Archive Space Pattern
- Create a dedicated `Archive` space for completed projects
- Move entire project page trees to Archive space on completion
- Set Archive space to read-only permissions
- Review Archive space annually for content that can be deleted

## Permission Inheritance Patterns

### Pattern 1: Open by Default
- All spaces readable by all employees
- Edit restricted to space members
- Admin restricted to space owners
- **Best for:** Transparency-focused organizations

### Pattern 2: Restricted by Default
- Spaces accessible only to specific groups
- Request access via space admin
- **Best for:** Regulated industries, confidential projects

### Pattern 3: Tiered Access
- Public tier: Company wiki, shared processes
- Team tier: Team-specific spaces with team access
- Restricted tier: HR, finance, legal with limited access
- **Best for:** Most organizations (balanced approach)

### Permission Tips
- Use Confluence groups, not individual users, for permissions
- Align groups with LDAP/SSO groups where possible
- Audit permissions quarterly
- Document permission model on the space homepage
- Use page-level restrictions sparingly (breaks inheritance, hard to audit)

## Scaling Considerations

### < 50 People
- 3-5 spaces total
- Simple by-team pattern
- Light governance

### 50-200 People
- 10-20 spaces
- Hybrid pattern (team + project)
- Formal labeling taxonomy
- Quarterly content reviews

### 200+ People
- 20-50+ spaces
- Full domain pattern with governance
- Space owners and content stewards
- Automated archival policies
- Regular information architecture reviews
