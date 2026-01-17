---
name: nx-executor
description: |
  Nx monorepo workspace management for sgc-monorepo and other Nx workspaces. Use when exploring project structure, running builds/tests, checking affected projects, understanding dependencies, or generating code. Triggers for: (1) "what projects", "list apps", "show workspace", (2) "run build/test/lint", "nx run", (3) "what changed", "affected projects", (4) "generate component/service", "nx generate", (5) project dependencies, "who depends on".
---

# Nx Executor - Monorepo Workspace Management

Manage Nx monorepo workspaces via the **nx executor** (code-execution MCP).

## Scope

**Auto-Detected Workspaces**:
- Current Claude Code session directory (via `MCP_PROJECT_DIR`)
- `~/Code/sgc-monorepo` (primary personal workspace)

**Does NOT apply to**:
- Non-Nx projects (no nx.json)
- Standalone applications

## When to Use This Executor

| User Request | Use nx Executor |
|-------------|-----------------|
| "What projects are in this repo?" | `getWorkspace()` |
| "Show me the project structure" | `getProjectGraphSummary()` |
| "What changed since main?" | `getAffectedProjects({ base: 'main' })` |
| "Run tests for harvest-backend" | `runTarget('harvest-backend', 'test')` |
| "Build all affected projects" | `runAffected('build')` |
| "What depends on harvest-kit?" | `getProjectDependents('harvest-kit')` |
| "Generate a new component" | `listGenerators()`, then prompt user |

## Common Patterns

### Explore Workspace

```typescript
// Get workspace overview
const workspace = await getWorkspace();
console.log(`Workspace: ${workspace.workspacePath}`);
console.log(`Nx Version: ${workspace.nxVersion}`);
console.log(`Projects: ${workspace.projects.length}`);

// List all projects with types
workspace.projects.forEach(p => {
  console.log(`- ${p.name} (${p.projectType})`);
});

return {
  path: workspace.workspacePath,
  nxVersion: workspace.nxVersion,
  projectCount: workspace.projects.length,
  projects: workspace.projects.map(p => ({
    name: p.name,
    type: p.projectType,
    root: p.root
  }))
};
```

### Get Project Details

```typescript
// Get full project configuration
const project = await getProjectDetails('harvest-backend');

return {
  name: project.name,
  root: project.root,
  sourceRoot: project.sourceRoot,
  projectType: project.projectType,
  targets: Object.keys(project.targets || {}),
  tags: project.tags,
  implicitDependencies: project.implicitDependencies
};
```

### Run Targets

```typescript
// Run a single target
const result = await runTarget('harvest-backend', 'serve');
console.log(`Success: ${result.success}`);
console.log(`Output:\n${result.output}`);

return {
  success: result.success,
  cached: result.output?.includes('[local cache]') || false
};
```

```typescript
// Run for multiple projects
const result = await runMany(['harvest-web', 'sgc-web'], 'build');
return { success: result.success };
```

```typescript
// Run for all affected projects
const result = await runAffected('test', { base: 'main' });
return { success: result.success };
```

### Affected Analysis

```typescript
// Get projects affected by recent changes
const affected = await getAffectedProjects({ base: 'main' });

return {
  affectedCount: affected.length,
  projects: affected,
  message: affected.length === 0
    ? 'No projects affected since main'
    : `${affected.length} projects affected`
};
```

### Dependency Graph

```typescript
// Get project graph summary
const graph = await getProjectGraphSummary({ limit: 20 });

return {
  totalProjects: graph.totalProjects,
  totalDependencies: graph.totalDependencies,
  topProjects: graph.projects.slice(0, 5).map(p => ({
    name: p.name,
    dependencies: p.dependencies?.length || 0,
    dependents: p.dependents?.length || 0
  }))
};
```

```typescript
// Get dependencies of a specific project
const deps = await getProjectDependencies('harvest-backend');
return {
  project: 'harvest-backend',
  dependencies: deps
};
```

```typescript
// Get projects that depend on a library
const dependents = await getProjectDependents('harvest-kit');
return {
  library: 'harvest-kit',
  dependents: dependents
};
```

### Generators

```typescript
// List available generators
const generators = await listGenerators();
return generators.slice(0, 10).map(g => ({
  name: `${g.collection}:${g.name}`,
  description: g.description
}));
```

```typescript
// Search for generators
const results = await searchGenerators('component');
return results.map(r => ({
  name: `${r.generator.collection}:${r.generator.name}`,
  description: r.generator.description
}));
```

```typescript
// Get generator schema (for prompting user)
const schema = await getGeneratorSchema('@nx/react:component');
return {
  name: schema.name,
  required: schema.required,
  properties: Object.keys(schema.properties)
};
```

## sgc-monorepo Project Structure

| Project | Type | Purpose |
|---------|------|---------|
| `harvest-ios` | app | iOS app (Swift) |
| `harvest-macos` | app | macOS app (Swift) |
| `harvest-watch` | app | watchOS app (Swift) |
| `harvest-web` | app | Web dashboard (Next.js 14) |
| `harvest-console` | app | Log viewer (Python Flask) |
| `harvest-backend` | service | Core API (Python FastAPI) |
| `harvest-stt` | service | Speech-to-Text (Python MLX) |
| `drizzle-site` | app | Drizzle website (Next.js 16) |
| `drizzle-api` | service | Catering API (Python FastAPI) |
| `sgc-web` | app | SGC website (Next.js 16) |
| `harvest-kit` | lib | Swift package (shared code) |

## Available Functions

### Workspace
- `getWorkspacePath()` - Auto-detect workspace root
- `getWorkspace()` - Full workspace info (nx.json + projects)
- `getWorkspaceInfo()` - Workspace summary
- `getProjectGraphSummary(options)` - Project graph with dependencies
- `getAffectedProjects(options)` - Git-affected projects

### Projects
- `getProjectDetails(name)` - Full project configuration
- `getProjectTargets(name)` - Project targets
- `getProjectDependencies(name)` - What this project depends on
- `getProjectDependents(name)` - What depends on this project
- `findProjects(options)` - Search projects by criteria

### Generators
- `listGenerators(options)` - List available generators
- `getGeneratorSchema(name)` - Get generator schema
- `searchGenerators(query)` - Search generators

### Tasks
- `runTarget(project, target)` - Run a target
- `runMany(projects, target)` - Run target for multiple projects
- `runAffected(target, options)` - Run target for affected projects
- `getProjectsWithTarget(target)` - Find projects with target

### Documentation
- `searchDocs(query)` - Search Nx documentation
- `listPlugins()` - List available plugins
- `getPluginInfo(name)` - Get plugin details

## Workflow Examples

### "What needs to be rebuilt?"

```typescript
// Check what's affected since main
const affected = await getAffectedProjects({ base: 'main' });

if (affected.length === 0) {
  return { message: 'Nothing changed - all up to date!' };
}

// Get details for each affected project
const details = await Promise.all(
  affected.map(name => getProjectDetails(name))
);

return {
  affectedCount: affected.length,
  projects: details.map(p => ({
    name: p.name,
    type: p.projectType,
    targets: Object.keys(p.targets || {})
  }))
};
```

### "Build and test everything that changed"

```typescript
// Build affected
const buildResult = await runAffected('build', { base: 'main' });
if (!buildResult.success) {
  return { success: false, phase: 'build', output: buildResult.output };
}

// Test affected
const testResult = await runAffected('test', { base: 'main' });
return {
  success: testResult.success,
  buildOutput: buildResult.output,
  testOutput: testResult.output
};
```

## Notes

- **Auto-detection**: Workspace is auto-detected from Claude Code session
- **Caching**: Nx caches task results; repeated runs are fast
- **Parallel execution**: `runMany` and `runAffected` run in parallel by default
- **Tags**: Use tags to filter projects (e.g., `scope:harvest`, `type:app`)

---

## Nx Deployment Patterns (CRITICAL)

**NEVER create separate workflow files for individual projects in an Nx monorepo.**

### The Nx Way

In an Nx monorepo, ALL projects should use the unified `nx affected -t deploy` pattern:

1. **Main CI workflow** runs `pnpm nx affected -t deploy`
2. **Each project** defines a `deploy` target in its configuration
3. **Nx determines** which projects need deployment based on git changes

### Anti-Pattern (DO NOT DO THIS)

```yaml
# ❌ WRONG: .github/workflows/my-project.yml
name: Deploy My Project
on:
  push:
    paths:
      - 'apps/my-project/**'
# This defeats the purpose of Nx monorepo!
```

### Correct Pattern

```json
// ✅ CORRECT: apps/my-project/package.json (or project.json)
{
  "nx": {
    "targets": {
      "deploy": {
        "executor": "@sg-ai/nx-deploy-executor:deploy",
        "options": {
          "type": "lambda",  // or "s3-static" or "ecs-codedeploy"
          // ...options
        }
      }
    }
  }
}
```

### Available Deployment Types

The `@sg-ai/nx-deploy-executor:deploy` executor supports three deployment types:

#### 1. Lambda Functions (`type: "lambda"`)

Deploys Lambda functions via S3 artifact upload:

```json
{
  "deploy": {
    "executor": "@sg-ai/nx-deploy-executor:deploy",
    "dependsOn": ["package-lambda"],
    "options": {
      "type": "lambda",
      "functionName": "my-function-{stage}",
      "bucket": "sg-codepipeline-artifacts",
      "artifactKey": "deploys/my-project-{stage}/my-project.zip",
      "localArtifactPath": "dist/apps/my-project/lambda.zip"
    },
    "configurations": {
      "development": { "stage": "development" },
      "production": { "stage": "production" }
    }
  }
}
```

**Lambda Build Chain:**
1. `build` - esbuild bundles to single JS file (with deps)
2. `package-lambda` - zip the bundle
3. `deploy` - upload to S3 + update Lambda function code

#### 2. Static Sites (`type: "s3-static"`)

Syncs static files to S3 with smart cache control:

```json
{
  "deploy": {
    "executor": "@sg-ai/nx-deploy-executor:deploy",
    "dependsOn": ["build"],
    "options": {
      "type": "s3-static",
      "bucket": "my-static-site-bucket",
      "distPath": "dist/apps/my-site",
      "cacheControl": "max-age=31536000,immutable",
      "htmlCacheControl": "max-age=0,no-cache,no-store,must-revalidate"
    }
  }
}
```

#### 3. ECS with CodeDeploy (`type: "ecs-codedeploy"`)

Confirms ECR push; CodeDeploy auto-triggers on image update:

```json
{
  "deploy": {
    "executor": "@sg-ai/nx-deploy-executor:deploy",
    "dependsOn": ["docker"],
    "options": {
      "type": "ecs-codedeploy"
    }
  }
}
```

### Stage Substitution

Use `{stage}` placeholder in options - it gets replaced with the configuration name:

- `--configuration=development` → `{stage}` becomes `development`
- `--configuration=production` → `{stage}` becomes `production`

### Main CI Workflow Pattern

```yaml
# .github/workflows/main.yml
- name: Deploy affected projects
  run: |
    pnpm nx affected -t deploy \
      --configuration=development \
      --parallel=1

# For production (on release)
- name: Deploy to production
  run: |
    pnpm nx affected -t deploy \
      --configuration=production \
      --parallel=1
```

### Why This Matters

| Separate Workflows | Nx Affected Deploy |
|-------------------|-------------------|
| ❌ Duplicate CI logic | ✅ Single source of truth |
| ❌ Path filters miss deps | ✅ Graph-aware changes |
| ❌ Manual maintenance | ✅ Automatic detection |
| ❌ Inconsistent deployments | ✅ Unified patterns |
| ❌ Can't share cache | ✅ Full Nx caching |

### Checklist for New Projects

When adding a deployable project to an Nx monorepo:

1. ✅ Add `deploy` target to project config (package.json or project.json)
2. ✅ Use `@sg-ai/nx-deploy-executor:deploy` (or appropriate executor)
3. ✅ Set `dependsOn` for build chain (`build`, `docker`, `package-lambda`)
4. ✅ Define `configurations` for development/production stages
5. ❌ Do NOT create a separate workflow file
6. ❌ Do NOT add path filters in workflows
