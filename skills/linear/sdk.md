# Linear SDK Automation Scripts

Reference for writing TypeScript automation scripts using the Linear SDK.

## Tool Selection Hierarchy

Always prefer simpler tools first:

1. **MCP tools (first choice)** - For simple operations like creating/updating single issues, basic queries
2. **SDK scripts (complex operations)** - For loops, bulk updates, conditional logic, data transformations
3. **GraphQL API (fallback)** - Only when MCP and SDK don't support the operation

## Overview

For complex Linear operations involving loops, mapping, or conditional logic, write TypeScript scripts using `@linear/sdk`. The SDK provides:

- Full TypeScript type hints and autocomplete
- Simpler syntax for iteration and data transformation
- Better error handling than raw GraphQL
- Easier debugging

Run scripts with: `npx tsx script.ts`

## Basic Setup

```typescript
import { LinearClient } from '@linear/sdk'

const client = new LinearClient({
  apiKey: process.env.LINEAR_API_KEY
})

async function main() {
  // Your automation logic here
}

main().catch(console.error)
```

**Authentication**: Set `LINEAR_API_KEY` environment variable or pass directly to client.

## Common Patterns

### Fetching and Filtering Issues

```typescript
// Get all issues from a team
const team = await client.team('TEAM-KEY')
const issues = await team.issues()

// Filter with TypeScript instead of complex GraphQL
const highPriorityOpen = issues.nodes.filter(issue =>
  issue.priority === 1 &&
  issue.state.type === 'started'
)

console.log(`Found ${highPriorityOpen.length} high priority issues`)
```

### Bulk Updates with Loops

```typescript
// Update multiple issues based on conditions
const team = await client.team('ENG')
const issues = await team.issues({
  filter: { state: { name: { eq: 'In Review' } } }
})

for (const issue of issues.nodes) {
  // Check condition with full type safety
  if (issue.assignee && issue.estimate && issue.estimate > 5) {
    await issue.update({
      priority: 2, // Set to high priority
      labels: ['needs-split']
    })
    console.log(`Updated ${issue.identifier}: ${issue.title}`)
  }
}
```

### Mapping Issues to Custom Format

```typescript
// Extract and transform issue data
const team = await client.team('PRODUCT')
const issues = await team.issues()

const report = issues.nodes.map(issue => ({
  id: issue.identifier,
  title: issue.title,
  assignee: issue.assignee?.name ?? 'Unassigned',
  daysOld: Math.floor(
    (Date.now() - issue.createdAt.getTime()) / (1000 * 60 * 60 * 24)
  ),
  labels: issue.labels.nodes.map(l => l.name).join(', ')
}))

// Output as JSON or CSV
console.log(JSON.stringify(report, null, 2))
```

### Working with Projects and Milestones

```typescript
// Get project and all its issues
const project = await client.project('PROJECT-ID')
const projectData = await project.issues()

// Group by state
const byState = projectData.nodes.reduce((acc, issue) => {
  const stateName = issue.state.name
  acc[stateName] = (acc[stateName] || 0) + 1
  return acc
}, {} as Record<string, number>)

console.log('Issues by state:', byState)
```

### Creating Multiple Issues from Data

```typescript
interface TaskTemplate {
  title: string
  description: string
  assigneeEmail: string
}

const tasks: TaskTemplate[] = [
  { title: 'Task 1', description: 'Do thing', assigneeEmail: 'user@example.com' },
  { title: 'Task 2', description: 'Do other', assigneeEmail: 'user@example.com' }
]

const team = await client.team('ENG')
const users = await client.users()

for (const task of tasks) {
  const assignee = users.nodes.find(u => u.email === task.assigneeEmail)

  await client.createIssue({
    teamId: team.id,
    title: task.title,
    description: task.description,
    assigneeId: assignee?.id,
    priority: 3
  })

  console.log(`Created: ${task.title}`)
}
```

### Pagination for Large Datasets

```typescript
// Handle paginated results
let hasMore = true
let after: string | undefined

const allIssues = []

while (hasMore) {
  const response = await client.issues({
    first: 50,
    after
  })

  allIssues.push(...response.nodes)

  hasMore = response.pageInfo.hasNextPage
  after = response.pageInfo.endCursor
}

console.log(`Total issues: ${allIssues.length}`)
```

### Conditional Logic with Type Safety

```typescript
const issues = await client.issues({
  filter: { team: { key: { eq: 'ENG' } } }
})

for (const issue of issues.nodes) {
  // TypeScript knows all available properties
  const needsAttention =
    !issue.assignee ||
    (issue.priority === 1 && issue.state.type !== 'started') ||
    (issue.dueDate && new Date(issue.dueDate) < new Date())

  if (needsAttention) {
    await issue.addComment({
      body: '⚠️ This issue needs attention'
    })
  }
}
```

## Script Template

```typescript
#!/usr/bin/env tsx
import { LinearClient } from '@linear/sdk'

const LINEAR_API_KEY = process.env.LINEAR_API_KEY
if (!LINEAR_API_KEY) {
  console.error('LINEAR_API_KEY environment variable required')
  process.exit(1)
}

const client = new LinearClient({ apiKey: LINEAR_API_KEY })

async function main() {
  // Your automation logic
  const me = await client.viewer
  console.log(`Running as: ${me.name}`)

  // Example: Get my open issues
  const myIssues = await client.issues({
    filter: {
      assignee: { id: { eq: me.id } },
      state: { type: { eq: 'started' } }
    }
  })

  console.log(`You have ${myIssues.nodes.length} in-progress issues`)

  for (const issue of myIssues.nodes) {
    console.log(`- ${issue.identifier}: ${issue.title}`)
  }
}

main().catch(error => {
  console.error('Error:', error.message)
  process.exit(1)
})
```

## Running Scripts

```bash
# Direct execution
npx tsx automation.ts

# With environment variable
LINEAR_API_KEY=lin_api_xxx npx tsx automation.ts

# Make executable (requires shebang)
chmod +x automation.ts
./automation.ts
```

## When to Use Each Tool

**Use MCP tools (prefer first):**
- Single issue operations (get, create, update)
- Simple queries with known parameters
- Basic filtering (by assignee, team, state, labels)
- Interactive workflows in conversation
- Creating/updating projects

**Use SDK scripts (when MCP insufficient):**
- Iterating over multiple items with complex logic
- Mapping/transforming data for export or reports
- Bulk updates with conditional logic
- Multi-step operations requiring intermediate state
- Operations needing debugging or iteration

**Use GraphQL API (fallback only):**
- Operations not supported by MCP or SDK
- When you need specific fields not exposed by SDK

## Dependencies

Scripts require:
- `@linear/sdk` package
- `tsx` for execution (via npx or installed)
- `LINEAR_API_KEY` environment variable

Install in project: `npm install @linear/sdk`

## API Reference

Full SDK documentation: https://linear.app/developers/sdk.md

The SDK is auto-generated from Linear's GraphQL API and includes type definitions for all operations.
