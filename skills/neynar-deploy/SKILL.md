---
name: neynar-deploy
description: Deploy static sites, Vite apps, and Next.js apps to a live URL with a single API call. Built-in versioning with instant rollback -- no git required. Use when you need to deploy, host, or update a website.
license: MIT
compatibility: Requires network access to https://api.host.neynar.app
metadata:
  author: neynar
  version: '1.1'
---

# Agent Deploy

Deploy web projects to `https://{project-name}.host.neynar.app` with a single HTTP call.

## When to use this skill

- User asks you to deploy, host, or publish a website
- User wants to put a static site, Vite app, or Next.js app live on the internet
- User wants to update an already-deployed site
- User wants to check analytics, roll back, or manage deployed projects
- You are picking up an existing project and need to understand its current state

## Built-in versioning

Every deploy automatically increments a version number. You do not need git, branches, or tags -- the platform tracks the full deploy history for you.

- Each deploy returns a `version` number and `deploymentId`
- `GET /v1/projects/:projectId` returns the complete deploy history with version numbers, descriptions, timestamps, and deployment IDs
- Roll back to any previous version with `POST /v1/projects/:projectId/rollback` -- this creates a new version from the old source files
- Download the source archive of any deployment with `GET /v1/projects/:projectId/files`

This means you can deploy freely, knowing you can always inspect what changed and revert if something breaks.

## Project context for agents

When picking up an existing project (or resuming work across sessions), call `GET /v1/projects/:projectId` to get a structured context snapshot instead of parsing git history:

```json
{
  "success": true,
  "project": {
    "projectId": "uuid",
    "projectName": "my-site",
    "framework": "static",
    "currentUrl": "https://my-site.host.neynar.app",
    "deployHistory": [
      {
        "version": 3,
        "description": "Added contact page",
        "createdAt": "...",
        "deploymentId": "uuid"
      },
      {
        "version": 2,
        "description": "Fixed hero image",
        "createdAt": "...",
        "deploymentId": "uuid"
      },
      {
        "version": 1,
        "description": "Initial deploy",
        "createdAt": "...",
        "deploymentId": "uuid"
      }
    ],
    "analyticsSummary": {
      "pageviews7d": 142,
      "uniqueVisitors7d": 89
    }
  }
}
```

This gives you everything you need in one call: what's deployed, what changed, how it's performing, and the live URL. Use the `description` field on each deploy to leave notes for your future self or other agents about what changed.

## Quick deploy flow

1. Create a `.tar.gz` archive of the project directory
2. POST it to `https://api.host.neynar.app/v1/deploy`
3. On first deploy, an API key is returned -- save it for future requests
4. The response includes the live URL

## How to deploy

### Step 1: Archive the project

```bash
tar czf /tmp/site.tar.gz -C /path/to/project .
```

### Step 2: Deploy

```bash
curl -X POST https://api.host.neynar.app/v1/deploy \
  -F "files=@/tmp/site.tar.gz" \
  -F "projectName=my-site" \
  -F "framework=static"
```

The `framework` field accepts: `nextjs`, `vite`, `static`, or `auto` (default).

### Step 3: Save the API key

The first deploy response includes an `apiKey` field. This key is returned exactly once. Save it to a `.agentdeploy` file or environment variable for subsequent requests.

```json
{
  "success": true,
  "projectId": "uuid",
  "apiKey": "uuid",
  "deploymentId": "uuid",
  "url": "https://my-site.host.neynar.app",
  "analyticsUrl": "https://api.host.neynar.app/analytics/<secret>"
}
```

### Step 4: Subsequent deploys

Use the saved API key and the same `projectName` to redeploy:

```bash
curl -X POST https://api.host.neynar.app/v1/deploy \
  -F "files=@/tmp/site.tar.gz" \
  -F "projectName=my-site" \
  -H "Authorization: Bearer <api-key>"
```

## API reference

Base URL: `https://api.host.neynar.app`

All authenticated endpoints require: `Authorization: Bearer <api-key>`

### POST /v1/deploy

Deploy files. Creates project and API key if called without auth.

Multipart form-data fields:

| Field         | Type   | Required | Description                                |
| ------------- | ------ | -------- | ------------------------------------------ |
| `files`       | file   | Yes      | `.tar.gz` archive of the site              |
| `projectName` | string | No       | Name (alphanumeric + hyphens, 2-100 chars) |
| `projectId`   | string | No       | UUID of existing project                   |
| `framework`   | string | No       | `nextjs`, `vite`, `static`, or `auto`      |
| `env`         | string | No       | JSON string: `{"KEY": "value"}`            |
| `description` | string | No       | Deploy description                         |

### GET /v1/projects

List all projects. Returns array of `{ projectId, projectName, framework, currentUrl, currentVersion }`.

### GET /v1/projects/:projectId

Get project details with deploy history and 7-day analytics summary.

### DELETE /v1/projects/:projectId

Delete a project and its Vercel resources.

### POST /v1/projects/:projectId/deploy

Deploy new version to existing project. Same multipart fields as `POST /v1/deploy` except `projectName` and `projectId`.

### GET /v1/projects/:projectId/deploy/:deploymentId

Check deployment status. `deployStatus` is one of: `pending`, `building`, `ready`, `error`.

### POST /v1/projects/:projectId/rollback

Roll back to a previous version. Body: `{ "version": <number> }`.

### GET /v1/projects/:projectId/analytics?period=7d

Get analytics. Period: `1d`, `7d`, or `30d`.

### GET /v1/projects/:projectId/files

Get download URL for latest source files.

### GET /v1/billing/tier

Get current tier and limits.

## Error handling

All errors return:

```json
{
  "success": false,
  "error": "Human-readable message"
}
```

Common status codes: `400` bad input, `401` invalid key, `402` project limit, `404` not found, `413` file too large (50MB max), `429` rate limited, `500` server error.

## Limits

Free tier: 3 active projects, 10 deploys per hour, 50MB max upload.

## MCP server

If the agent supports MCP, connect to the agent-deploy MCP server instead of using raw HTTP:

```json
{
  "mcpServers": {
    "agent-deploy": {
      "command": "npx",
      "args": ["-y", "@neynar/service.agent-deploy"]
    }
  }
}
```

MCP tools: `deploy`, `list_projects`, `get_project_context`, `get_analytics`, `get_deployment_status`, `download_project`, `rollback`, `teardown`.
