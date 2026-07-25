---
name: "atlassian-templates"
description: Atlassian Template and Files Creator/Modifier expert for creating, modifying, and managing Jira and Confluence templates, blueprints, custom layouts, reusable components, and standardized content structures. Use when building org-wide templates, custom blueprints, page layouts, and automated content generation.
---

# Atlassian Template & Files Creator Expert

Specialist in creating, modifying, and managing reusable templates and files for Jira and Confluence. Ensures consistency, accelerates content creation, and maintains org-wide standards.

---

## Workflows

### Template Creation Process
1. **Discover**: Interview stakeholders to understand needs
2. **Analyze**: Review existing content patterns
3. **Design**: Create template structure and placeholders
4. **Implement**: Build template with macros and formatting
5. **Test**: Validate with sample data — confirm template renders correctly in preview before publishing
6. **Document**: Create usage instructions
7. **Publish**: Deploy to appropriate space/project via MCP (see MCP Operations below)
8. **Verify**: Confirm deployment success; roll back to previous version if errors occur
9. **Train**: Educate users on template usage
10. **Monitor**: Track adoption and gather feedback
11. **Iterate**: Refine based on usage

### Template Modification Process
1. **Assess**: Review change request and impact
2. **Version**: Create new version, keep old available
3. **Modify**: Update template structure/content
4. **Test**: Validate changes don't break existing usage; preview updated template before publishing
5. **Migrate**: Provide migration path for existing content
6. **Communicate**: Announce changes to users
7. **Support**: Assist users with migration
8. **Archive**: Deprecate old version after transition; confirm deprecated template is unlisted, not deleted

### Blueprint Development
1. Define blueprint scope and purpose
2. Design multi-page structure
3. Create page templates for each section
4. Configure page creation rules
5. Add dynamic content (Jira queries, user data)
6. Test blueprint creation flow end-to-end with a sample space
7. Verify all macro references resolve correctly before deployment
8. **HANDOFF TO**: Atlassian Admin for global deployment

---

## Confluence Templates Library

See `references/template-design-patterns.md` for template design patterns and `references/governance-framework.md` for the governance model. For deployment-ready storage-format markup, use the bundled scaffolder (see [Template scaffolder](#template-scaffolder-generate-storage-format-markup) below). The following summarises the standard types this skill creates and maintains.

### Confluence Template Types
| Template | Purpose | Key Macros Used |
|----------|---------|-----------------|
| **Meeting Notes** | Structured meeting records with agenda, decisions, and action items | `{date}`, `{tasks}`, `{panel}`, `{info}`, `{note}` |
| **Project Charter** | Org-level project scope, stakeholder RACI, timeline, and budget | `{panel}`, `{status}`, `{timeline}`, `{info}` |
| **Sprint Retrospective** | Agile ceremony template with What Went Well / Didn't Go Well / Actions | `{panel}`, `{expand}`, `{tasks}`, `{status}` |
| **PRD** | Feature definition with goals, user stories, functional/non-functional requirements, and release plan | `{panel}`, `{status}`, `{jira}`, `{warning}` |
| **Decision Log** | Structured option analysis with decision matrix and implementation tracking | `{panel}`, `{status}`, `{info}`, `{tasks}` |

**Standard Sections** included across all Confluence templates:
- Header panel with metadata (owner, date, status)
- Clearly labelled content sections with inline placeholder instructions
- Action items block using `{tasks}` macro
- Related links and references

### Complete Example: Meeting Notes Template

> **Format warning**: The example below is **legacy wiki markup** (`{panel}`, `h2.`, `{tasks}`), shown for human readability. Wiki markup is NOT Confluence storage format and **will be rejected** by `mcp__atlassian__createConfluencePage` / `updateConfluencePage`, which expect storage format (XHTML, `<ac:structured-macro>` elements) or ADF. To get the deployment-ready storage-format equivalent, run the scaffolder: `python3 scripts/template_scaffolder.py meeting-notes` (see [Template scaffolder](#template-scaffolder-generate-storage-format-markup)).

```
{panel:title=Meeting Metadata|borderColor=#0052CC|titleBGColor=#0052CC|titleColor=#FFFFFF}
*Date:* {date}
*Owner / Facilitator:* @[facilitator name]
*Attendees:* @[name], @[name]
*Status:* {status:colour=Yellow|title=In Progress}
{panel}

h2. Agenda
# [Agenda item 1]
# [Agenda item 2]
# [Agenda item 3]

h2. Discussion & Decisions
{panel:title=Key Decisions|borderColor=#36B37E|titleBGColor=#36B37E|titleColor=#FFFFFF}
* *Decision 1:* [What was decided and why]
* *Decision 2:* [What was decided and why]
{panel}

{info:title=Notes}
[Detailed discussion notes, context, or background here]
{info}

h2. Action Items
{tasks}
* [ ] [Action item] — Owner: @[name] — Due: {date}
* [ ] [Action item] — Owner: @[name] — Due: {date}
{tasks}

h2. Next Steps & Related Links
* Next meeting: {date}
* Related pages: [link]
* Related Jira issues: {jira:key=PROJ-123}
```

> Storage-format examples for the other built-in types (decision-log, runbook, project-kickoff) come from `python3 scripts/template_scaffolder.py --list`; design patterns for the remaining types (Project Charter, Sprint Retrospective, PRD) are in `references/template-design-patterns.md`.

---

## Jira Templates Library

### Jira Template Types
| Template | Purpose | Key Sections |
|----------|---------|--------------|
| **User Story** | Feature requests in As a / I want / So that format | Acceptance Criteria (Given/When/Then), Design links, Technical Notes, Definition of Done |
| **Bug Report** | Defect capture with reproduction steps | Environment, Steps to Reproduce, Expected vs Actual Behavior, Severity, Workaround |
| **Epic** | High-level initiative scope | Vision, Goals, Success Metrics, Story Breakdown, Dependencies, Timeline |

**Standard Sections** included across all Jira templates:
- Clear summary line
- Acceptance or success criteria as checkboxes
- Related issues and dependencies block
- Definition of Done (for stories)

---

## Macro Usage Guidelines

**Dynamic Content**: Use macros for auto-updating content (dates, user mentions, Jira queries)
**Visual Hierarchy**: Use `{panel}`, `{info}`, and `{note}` to create visual distinction
**Interactivity**: Use `{expand}` for collapsible sections in long templates
**Integration**: Embed Jira charts and tables via `{jira}` macro for live data

---

## Template scaffolder — generate storage-format markup

The bundled scaffolder emits **Confluence storage-format XHTML** — the exact body format `createConfluencePage`/`updateConfluencePage` accept. It is the canonical deployment path for this skill:

```bash
# List available template types (meeting-notes, decision-log, runbook, project-kickoff, custom)
python3 scripts/template_scaffolder.py --list

# Generate a template body (storage-format XHTML)
python3 scripts/template_scaffolder.py meeting-notes

# Custom template with chosen sections and macros, JSON output for programmatic use
python3 scripts/template_scaffolder.py custom --sections "Overview,Goals,Action Items" --macros "toc,status,info" --format json
```

Consume the output: take the `CONFLUENCE STORAGE FORMAT MARKUP` block (text mode) or the markup field (JSON mode) and pass it verbatim as the `body` of `mcp__atlassian__createConfluencePage`. Apply the suggested labels via the Confluence UI afterwards (label tools are not on the MCP).

## Atlassian MCP Integration

**Primary Tool**: Atlassian Remote MCP server (bundled `.mcp.json`, server key `atlassian`). Tools surface as `mcp__atlassian__<toolName>` (camelCase). **Canonical tool list**: `project-management/references/atlassian-mcp-tools.md`. Never invent tool names — if a capability isn't in that list, it is not available via MCP; route to the web UI or REST API.

### Template Operations via MCP

Obtain `cloudId` once via `mcp__atlassian__getAccessibleAtlassianResources`. Replace angle-bracket placeholders with real values; discover exact parameter names from each tool's schema at call time.

**Create a Confluence template page** (body from the scaffolder above):
```
mcp__atlassian__createConfluencePage (cloudId, space, title="Template: Meeting Notes",
  body=<storage-format XHTML from template_scaffolder.py>, parent page id optional)
```
Labels (`template`, `meeting-notes`) must be applied in the Confluence UI — there is no MCP label tool.

**Update an existing template page** (read first to get the current version):
```
mcp__atlassian__getConfluencePage (cloudId, pageId=<existing page id>)
mcp__atlassian__updateConfluencePage (cloudId, pageId=<id>, version=<current + 1>,
  body=<updated storage-format content>)
```

**Jira issue description templates**: there is **no MCP tool for field configuration** (`default_value` on the description field, screens, field contexts). Configure description defaults in the Jira admin UI (`Settings > Issues > Field configurations`) or via REST (`/rest/api/3/fieldconfiguration`). What MCP CAN do: create issues pre-filled with template text via `mcp__atlassian__createJiraIssue` (pass the template body as the description), and inspect required fields per issue type with `mcp__atlassian__getJiraIssueTypeMetaWithFields`.

**First-class Confluence templates/blueprints** are also **not creatable via MCP** — `createConfluencePage` creates ordinary pages that serve as copy-from templates. To register a real space template, use `Space settings > Templates` in the UI.

**Deploy a template page to multiple spaces (batch):**
```
# Repeat per target space:
mcp__atlassian__createConfluencePage (cloudId, space=<target>, title="Template: Meeting Notes", body=<storage-format content>)
# Verify each create before proceeding:
mcp__atlassian__getConfluencePage (cloudId, pageId=<id returned by create>)
# Assert the returned body is non-empty and contains the expected <ac:structured-macro> elements
```

**Validation checkpoint after deployment:**
- Retrieve the created/updated page via `mcp__atlassian__getConfluencePage` and assert it renders without macro errors
- Check that Jira-macro embeds resolve against the target Jira project
- Confirm task blocks are interactive in the published view
- If any check fails: revert using `mcp__atlassian__updateConfluencePage` with `version: <current + 1>` and the previous version body

---

## Best Practices & Governance

**Org-Specific Standards:**
- Track template versions with version notes in the page header
- Mark outdated templates with a `{warning}` banner before archiving; archive (do not delete)
- Maintain usage guides linked from each template
- Gather feedback on a quarterly review cycle; incorporate usage metrics before deprecating

**Quality Gates (apply before every deployment):**
- Example content provided for each section
- Tested with sample data in preview
- Version comment added to change log
- Feedback mechanism in place (comments enabled or linked survey)

**Governance Process**:
1. Request and justification
2. Design and review
3. Testing with pilot users
4. Documentation
5. Approval
6. Deployment (via MCP or manual)
7. Training
8. Monitoring

---

## Handoff Protocols

Handoff summary (governance context in `references/governance-framework.md`):

| Partner | Receives FROM | Sends TO |
|---------|--------------|---------|
| **Senior PM** | Template requirements, reporting templates, executive formats | Completed templates, usage analytics, optimization suggestions |
| **Scrum Master** | Sprint ceremony needs, team-specific requests, retro format preferences | Sprint-ready templates, agile ceremony structures, velocity tracking templates |
| **Jira Expert** | Issue template requirements, custom field display needs | Issue description templates, field config templates, JQL query templates |
| **Confluence Expert** | Space-specific needs, global template requests, blueprint requirements | Configured page templates, blueprint structures, deployment plans |
| **Atlassian Admin** | Org-wide standards, global deployment requirements, compliance templates | Global templates for approval, usage reports, compliance status |
