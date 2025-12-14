---
name: linear
description: Managing Linear issues, projects, and teams. Use when working with Linear tasks, creating issues, updating status, querying projects, or managing team workflows.
license: Complete terms in LICENSE.txt
allowed-tools:
  - mcp__linear
  - WebFetch(domain:linear.app)
  - Bash
---

# Linear

Tools and workflows for managing issues, projects, and teams in Linear.

## Tool Selection

Choose the right tool for the task:

1. **MCP tools** - Use for simple operations (create/update/query single issues, basic filters)
2. **SDK scripts** - Use for complex operations (loops, bulk updates, conditional logic, data transformations)
3. **GraphQL API** - Fallback for operations not supported by MCP or SDK

## Conventions

### Issue Status

When creating issues, set the appropriate status based on assignment:

- **Assigned to me** (`assignee: "me"`): Set `state: "Todo"`
- **Unassigned**: Set `state: "Backlog"`

Example:
```typescript
// Issue for myself
await linear.create_issue({
  team: "ENG",
  title: "Fix authentication bug",
  assignee: "me",
  state: "Todo"
})

// Unassigned issue
await linear.create_issue({
  team: "ENG",
  title: "Research API performance",
  state: "Backlog"
})
```

### Querying Issues

Use `assignee: "me"` to filter issues assigned to the authenticated user:

```typescript
// My issues
await linear.list_issues({ assignee: "me" })

// Team backlog
await linear.list_issues({ team: "ENG", state: "Backlog" })
```

### Labels

You can use label names directly in `create_issue` and `update_issue` - no need to look up IDs:

```typescript
await linear.create_issue({
  team: "ENG",
  title: "Update documentation",
  labels: ["documentation", "high-priority"]
})
```

## SDK Automation Scripts

**Use only when MCP tools are insufficient.** For complex operations involving loops, mapping, or bulk updates, write TypeScript scripts using `@linear/sdk`. See `sdk.md` for:

- Complete script patterns and templates
- Common automation examples (bulk updates, filtering, reporting)
- Tool selection criteria

Scripts provide full type hints and are easier to debug than raw GraphQL for multi-step operations.

## GraphQL API

**Fallback only.** Use when operations aren't supported by MCP or SDK. See `api.md` for documentation on using the Linear GraphQL API directly.

### Ad-Hoc Queries

Use `scripts/query.ts` to execute GraphQL queries:

```bash
LINEAR_API_KEY=lin_api_xxx node scripts/query.ts "query { viewer { id name } }"
```

If `LINEAR_API_KEY` is not provided to the Claude process, inform the user that GraphQL queries cannot be executed without an API key.

## Projects & Initiatives

### Content vs Description (CRITICAL)

Linear has **two text fields** - using the wrong one causes blank displays:

| Field | Limit | Shows In | Use For |
|-------|-------|----------|---------|
| `description` | 255 chars | List views, tooltips | Short summary |
| `content` | Unlimited | **Main detail panel** | Full markdown documentation |

**Always set BOTH when creating/updating projects:**

```graphql
# Content is what users see in the main panel!
mutation {
  projectUpdate(id: "<uuid>", input: {
    content: "# Project Title\n\nFull markdown description...",
    description: "Short 255 char summary for list views"
  }) { success }
}
```

### New Phase Project Pattern

When creating a new phase, follow this complete workflow:

```bash
# 1. Create project via CLI
linear projects create --name "Phase N: Name" --description "Short summary"

# 2. Link to initiative
node scripts/linear-helpers.mjs link-project <project-id>

# 3. Set content (main UI panel)
# Use GraphQL to set full markdown content

# 4. Add resource link to implementation doc
# Use entityExternalLinkCreate mutation

# 5. Create milestone for Definition of Done
# Use projectMilestoneCreate mutation

# 6. Create issues via MCP
# 7. Add issues to project
```

### Resource Links

Add clickable links to projects/initiatives (shows in Resources section):

```graphql
mutation {
  entityExternalLinkCreate(input: {
    url: "https://github.com/org/repo/blob/main/docs/implementation/phase-N.md",
    label: "Implementation Doc",
    projectId: "<project-uuid>"
  }) { success }
}
```

**Standard resource links for phases:**
- `Implementation Doc` → docs/implementation/phase-N-*.md
- `Production Site` → deployment URL (for initiative)
- `Repository` → GitHub repo link (for initiative)

### Project Milestones (Definition of Done)

Track completion criteria with milestones:

```graphql
mutation {
  projectMilestoneCreate(input: {
    projectId: "<uuid>",
    name: "DoD: Testing",
    description: "Unit tests, E2E tests, 100% coverage"
  }) { success }
}
```

**Standard DoD milestones:**
- `DoD: Core Feature` - Main functionality complete
- `DoD: Testing` - All tests pass, coverage met
- `DoD: Security` - Security requirements verified
- `DoD: Accessibility` - A11y requirements met

### Project Status UUIDs

Projects have status independent of issue progress:

```
Backlog:     1ed7da89-db44-4339-b0d7-ce37d8ff9604
Planned:     33ebbb84-53ea-4dd8-a8db-49a8b3b9c502
In Progress: 71d18c8f-53de-4752-be37-a6d529cb9c97
Completed:   54294a72-010d-4ae7-9829-bed76232fb66
Canceled:    562050cc-bb71-4b81-bf3d-8bed7cc44153
```

```graphql
mutation {
  projectUpdate(id: "<project-uuid>", input: { statusId: "<status-uuid>" }) { success }
}
```

## Reference

- Linear MCP: https://linear.app/docs/mcp.md
- GraphQL API: See `api.md`
