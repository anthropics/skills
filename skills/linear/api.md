# Linear GraphQL API

Documentation for querying the Linear API directly when the MCP tools don't support a specific operation.

## Authentication

**Endpoint**: `https://api.linear.app/graphql`

**Authentication Header**:
```
Authorization: <API_KEY>
```

Personal API keys are available in Linear under Security & access settings.

## Using the Linear SDK

For ad-hoc queries and automation, use the `@linear/sdk` package with `npx` and TypeScript.

### Setup

The skill includes `scripts/query.ts` for executing GraphQL queries. Run it with:

```bash
LINEAR_API_KEY=lin_api_xxx npx tsx scripts/query.ts "query { viewer { id name } }"
```

**Environment Variable**: The script requires `LINEAR_API_KEY` to be set. If not provided to the Claude process, you cannot execute GraphQL queries automatically.

### Example Queries

**Get authenticated user:**
```graphql
query Me {
  viewer {
    id
    name
    email
  }
}
```

**Get team issues:**
```graphql
query Team($teamId: String!) {
  team(id: $teamId) {
    issues {
      nodes {
        id
        title
        state { name }
        assignee { name }
      }
    }
  }
}
```

**Get user's assigned issues:**
```graphql
query MyIssues {
  viewer {
    assignedIssues {
      nodes {
        id
        title
        state { name }
        team { key }
      }
    }
  }
}
```

### Mutations

**Create issue:**
```graphql
mutation CreateIssue($input: IssueCreateInput!) {
  issueCreate(input: $input) {
    success
    issue {
      id
      identifier
      title
    }
  }
}
```

With variables:
```json
{
  "input": {
    "teamId": "TEAM_ID",
    "title": "Issue title",
    "description": "Issue description",
    "stateId": "STATE_ID"
  }
}
```

**Update issue:**
```graphql
mutation UpdateIssue($id: String!, $input: IssueUpdateInput!) {
  issueUpdate(id: $id, input: $input) {
    success
    issue {
      id
      title
      state { name }
    }
  }
}
```

## Rate Limiting

Monitor HTTP status codes and handle rate limits appropriately. For real-time updates, Linear recommends using webhooks instead of polling.

## Key Concepts

- **Team IDs**: Required for most operations involving issues and projects
- **State IDs**: Issues default to the team's first Backlog state unless specified
- **Archived Resources**: Hidden by default; use `includeArchived: true` to retrieve
- **Error Handling**: Always check the `errors` array in responses before assuming success

## Using linear-sdk Directly

For more complex automation, you can use the Linear SDK programmatically:

```typescript
import { LinearClient } from '@linear/sdk';

const client = new LinearClient({
  apiKey: process.env.LINEAR_API_KEY
});

// Get viewer
const me = await client.viewer;
console.log(me.name);

// Get issues
const issues = await client.issues({
  filter: { assignee: { id: { eq: me.id } } }
});

for (const issue of issues.nodes) {
  console.log(`${issue.identifier}: ${issue.title}`);
}
```

## Reference

- [Linear GraphQL Documentation](https://linear.app/developers/graphql)
- [Linear SDK](https://github.com/linear/linear/tree/master/packages/sdk)

Use GraphQL introspection to discover the API schema:

```bash
LINEAR_API_KEY=lin_api_xxx npx tsx scripts/query.ts "{ __schema { types { name description } } }"
```
