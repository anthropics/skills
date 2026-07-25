---
name: "confluence-expert"
description: Atlassian Confluence expert for creating and managing spaces, knowledge bases, and documentation. Configures space permissions and hierarchies, creates page templates with macros, sets up documentation taxonomies, designs page layouts, and manages content governance. Use when users need to build or restructure a Confluence space, design page hierarchies with permission structures, author or standardise documentation templates, embed Jira reports in pages, run knowledge base audits, or establish documentation standards and collaborative workflows.
---

# Atlassian Confluence Expert

Master-level expertise in Confluence space management, documentation architecture, content creation, macros, templates, and collaborative knowledge management.

## Atlassian MCP Integration

**Primary Tool**: Atlassian Remote MCP server (bundled `.mcp.json`, server key `atlassian`). Tools are camelCase and surface as `mcp__atlassian__<toolName>`. **Canonical tool list**: `project-management/references/atlassian-mcp-tools.md`. Never invent tool names — if a capability isn't in that list, it is not available via MCP.

**Key Operations** (obtain `cloudId` once via `mcp__atlassian__getAccessibleAtlassianResources`):

```
// List spaces (space CREATION is not available via MCP — see below)
mcp__atlassian__getConfluenceSpaces (cloudId)

// Create a page under a parent — body must be storage-format XHTML or ADF, never wiki markup
mcp__atlassian__createConfluencePage (cloudId, space, title="Sprint 42 Notes", parent page id, body="<p>Meeting notes in storage-format XHTML</p>")

// Update an existing page (fetch current version with getConfluencePage, then supply version + 1)
mcp__atlassian__updateConfluencePage (cloudId, pageId="789012", version=5, body="<p>Updated content</p>")

// Read a page (body + current version)
mcp__atlassian__getConfluencePage (cloudId, pageId="789012")

// Search with CQL
mcp__atlassian__searchConfluenceUsingCql (cloudId, cql='space = "TEAM" AND label = "meeting-notes" ORDER BY lastModified DESC')

// Retrieve child pages for hierarchy inspection
mcp__atlassian__getConfluencePageDescendants (cloudId, pageId="123456")

// Comments
mcp__atlassian__getConfluencePageFooterComments / mcp__atlassian__createConfluenceFooterComment (cloudId, pageId)
```

**Not available via MCP — use the web UI or REST API instead:**
- Create/delete a **space** → Confluence UI `Spaces > Create space` or `POST /wiki/api/v2/spaces`
- **Delete** a page → Confluence UI or `DELETE /wiki/api/v2/pages/{id}`
- Apply **labels** → Confluence UI or `/wiki/rest/api/content/{id}/label`
- Space **permissions**, templates/blueprints as first-class objects → Confluence space settings UI

**Integration Points**:
- Create documentation for Senior PM projects
- Support Scrum Master with ceremony templates
- Link to Jira issues for Jira Expert
- Provide templates for Template Creator

> **See also**: `references/macro-cheat-sheet.md` for storage-format macro syntax, `references/templates.md` for the template library, `references/space-architecture-patterns.md` for space structure and permission patterns.

## Workflows

### Space Creation

> Space creation is **not available via MCP** — create the space in the Confluence UI (`Spaces > Create space`) or via REST (`POST /wiki/api/v2/spaces`). The page tree inside it CAN be built via MCP (`mcp__atlassian__createConfluencePage`).

0. Generate the recommended hierarchy from a team description:
   ```bash
   python3 scripts/space_structure_generator.py team_info.json --format json
   ```
   Input: JSON with team `name`, `size`, `type`, `projects`. Consume the output: use the emitted page tree as the creation plan for step 5 — one `mcp__atlassian__createConfluencePage` call per node, passing the parent page id to nest children.
1. Determine space type (Team, Project, Knowledge Base, Personal)
2. Create space with clear name and description (web UI / REST)
3. Set space homepage with overview
4. Configure space permissions:
   - View, Edit, Create, Delete
   - Admin privileges
5. Create initial page tree structure
6. Add space shortcuts for navigation
7. **Verify**: Navigate to the space URL and confirm the homepage loads; check that a non-admin test user sees the correct permission level
8. **HANDOFF TO**: Teams for content population

### Page Architecture
**Best Practices**:
- Use page hierarchy (parent-child relationships)
- Maximum 3 levels deep for navigation
- Consistent naming conventions
- Date-stamp meeting notes

**Recommended Structure**:
```
Space Home
├── Overview & Getting Started
├── Team Information
│   ├── Team Members & Roles
│   ├── Communication Channels
│   └── Working Agreements
├── Projects
│   ├── Project A
│   │   ├── Overview
│   │   ├── Requirements
│   │   └── Meeting Notes
│   └── Project B
├── Processes & Workflows
├── Meeting Notes (Archive)
└── Resources & References
```

### Template Creation
1. Identify repeatable content pattern
2. Create page with structure and placeholders
3. Add instructions in placeholders
4. Format with appropriate macros
5. Save as template
6. Share with space or make global
7. **Verify**: Create a test page from the template and confirm all placeholders render correctly before sharing with the team
8. **USE**: References for advanced template patterns

### Documentation Strategy
1. **Assess** current documentation state
2. **Define** documentation goals and audience
3. **Organize** content taxonomy and structure
4. **Create** templates and guidelines
5. **Migrate** existing documentation
6. **Train** teams on best practices
7. **Monitor** usage and adoption
8. **REPORT TO**: Senior PM on documentation health

### Knowledge Base Management

**Run a content health audit** before any restructure or governance review:
```bash
python3 scripts/content_audit_analyzer.py pages.json --format json
```
Input: a JSON page inventory (`title`, `last_modified`, `view_count`, `author`, `labels`, `word_count`) — build it by exporting page metadata via `mcp__atlassian__getPagesInConfluenceSpace` / `mcp__atlassian__searchConfluenceUsingCql`. Consume the output: the stale/orphaned/low-engagement findings become the archive list (label + move via UI, since label tools aren't on the MCP) and the update backlog for the quality standards below.

**Article Types**:
- How-to guides
- Troubleshooting docs
- FAQs
- Reference documentation
- Process documentation

**Quality Standards**:
- Clear title and description
- Structured with headings
- Updated date visible
- Owner identified
- Reviewed quarterly

## Essential Macros

> **Syntax note**: The `{macro}` shorthand below is **legacy wiki-markup notation**, shown for readability only. Confluence Cloud pages created via MCP (`createConfluencePage` / `updateConfluencePage`) require **storage format (XHTML)** — e.g. `{info}` is really `<ac:structured-macro ac:name="info"><ac:rich-text-body>...</ac:rich-text-body></ac:structured-macro>`. For the storage-format syntax of every macro listed here, see `references/macro-cheat-sheet.md`; for ready-made storage-format page bodies, run the atlassian-templates scaffolder (`python3 ../atlassian-templates/scripts/template_scaffolder.py meeting-notes`).

### Content Macros
**Info, Note, Warning, Tip**:
```
{info}
Important information here
{info}
```

**Expand**:
```
{expand:title=Click to expand}
Hidden content here
{expand}
```

**Table of Contents**:
```
{toc:maxLevel=3}
```

**Excerpt & Excerpt Include**:
```
{excerpt}
Reusable content
{excerpt}

{excerpt-include:Page Name}
```

### Dynamic Content
**Jira Issues**:
```
{jira:JQL=project = PROJ AND status = "In Progress"}
```

**Jira Chart**:
```
{jirachart:type=pie|jql=project = PROJ|statType=statuses}
```

**Recently Updated**:
```
{recently-updated:spaces=@all|max=10}
```

**Content by Label**:
```
{contentbylabel:label=meeting-notes|maxResults=20}
```

### Collaboration Macros
**Status**:
```
{status:colour=Green|title=Approved}
```

**Task List**:
```
{tasks}
- [ ] Task 1
- [x] Task 2 completed
{tasks}
```

**User Mention**:
```
@username
```

**Date**:
```
{date:format=dd MMM yyyy}
```

## Page Layouts & Formatting

**Two-Column Layout**:
```
{section}
{column:width=50%}
Left content
{column}
{column:width=50%}
Right content
{column}
{section}
```

**Panel**:
```
{panel:title=Panel Title|borderColor=#ccc}
Panel content
{panel}
```

**Code Block**:
```
{code:javascript}
const example = "code here";
{code}
```

## Templates Library

> Full template library with complete markup: see `references/templates.md`. Key templates summarised below.

| Template | Purpose | Key Sections |
|----------|---------|--------------|
| **Meeting Notes** | Sprint/team meetings | Agenda, Discussion, Decisions, Action Items (tasks macro) |
| **Project Overview** | Project kickoff & status | Quick Facts panel, Objectives, Stakeholders table, Milestones (Jira macro), Risks |
| **Decision Log** | Architectural/strategic decisions | Context, Options Considered, Decision, Consequences, Next Steps |
| **Sprint Retrospective** | Agile ceremony docs | What Went Well (info), What Didn't (warning), Action Items (tasks), Metrics |

## Space Permissions

> Permission patterns by space type: see `references/space-architecture-patterns.md`. Note: space permissions are configured in the Confluence UI (`Space settings > Permissions`) — not via MCP.

### Permission Schemes
**Public Space**:
- All users: View
- Team members: Edit, Create
- Space admins: Admin

**Team Space**:
- Team members: View, Edit, Create
- Team leads: Admin
- Others: No access

**Project Space**:
- Stakeholders: View
- Project team: Edit, Create
- PM: Admin

## Content Governance

**Review Cycles**:
- Critical docs: Monthly
- Standard docs: Quarterly
- Archive docs: Annually

**Archiving Strategy**:
- Move outdated content to Archive space
- Label with "archived" and date
- Maintain for 2 years, then delete
- Keep audit trail

**Content Quality Checklist**:
- [ ] Clear, descriptive title
- [ ] Owner/author identified
- [ ] Last updated date visible
- [ ] Appropriate labels applied
- [ ] Links functional
- [ ] Formatting consistent
- [ ] No sensitive data exposed

## Decision Framework

**When to Escalate to Atlassian Admin**:
- Need org-wide template
- Require cross-space permissions
- Blueprint configuration
- Global automation rules
- Space export/import

**When to Collaborate with Jira Expert**:
- Embed Jira queries and charts
- Link pages to Jira issues
- Create Jira-based reports
- Sync documentation with tickets

**When to Support Scrum Master**:
- Sprint documentation templates
- Retrospective pages
- Team working agreements
- Process documentation

**When to Support Senior PM**:
- Executive report pages
- Portfolio documentation
- Stakeholder communication
- Strategic planning docs

## Handoff Protocols

**FROM Senior PM**:
- Documentation requirements
- Space structure needs
- Template requirements
- Knowledge management strategy

**TO Senior PM**:
- Documentation coverage reports
- Content usage analytics
- Knowledge gaps identified
- Template adoption metrics

**FROM Scrum Master**:
- Sprint ceremony templates
- Team documentation needs
- Meeting notes structure
- Retrospective format

**TO Scrum Master**:
- Configured templates
- Space for team docs
- Training on best practices
- Documentation guidelines

**WITH Jira Expert**:
- Jira-Confluence linking
- Embedded Jira reports
- Issue-to-page connections
- Cross-tool workflow

## Best Practices

**Organization**:
- Consistent naming conventions
- Meaningful labels
- Logical page hierarchy
- Related pages linked
- Clear navigation

**Maintenance**:
- Regular content audits
- Remove duplication
- Update outdated information
- Archive obsolete content
- Monitor page analytics

## Analytics & Metrics

**Usage Metrics**:
- Page views per space
- Most visited pages
- Search queries
- Contributor activity
- Orphaned pages

**Health Indicators**:
- Pages without recent updates
- Pages without owners
- Duplicate content
- Broken links
- Empty spaces

## Related Skills

- **Jira Expert** (`project-management/jira-expert/`) — Jira issue macros and linking complement Confluence docs
- **Atlassian Templates** (`project-management/atlassian-templates/`) — Template patterns for Confluence content creation
