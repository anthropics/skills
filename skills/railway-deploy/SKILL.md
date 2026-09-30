---
name: railway-deploy
description: Deploy any project to Railway fully autonomously — init project, configure services, set environment variables, deploy code, provision a domain, and monitor build logs. Handles Node, Python, Go, Rust, Ruby, Java, PHP, Deno, Elixir automatically via Railpack detection. Supports first-time deploys and redeployments. Also manages environments (production/staging), service linking, and variable management. Triggers on phrases like "deploy to railway", "push to railway", "ship this to railway", "railway deploy", "set up railway", "launch on railway".
license: Complete terms in LICENSE.txt
allowed-tools: Bash(railway:*) Bash(git:*) Bash(ls:*) Bash(cat:*) Bash(find:*)
---

# Railway Deploy Skill

Deploy any project to Railway end-to-end without human intervention. From zero to live URL in one shot.

## What This Skill Does

Autonomously handles the full Railway deployment lifecycle:
1. Detects project type and validates readiness
2. Authenticates and selects/creates project
3. Links service or creates new one
4. Sets environment variables
5. Deploys and streams build logs
6. Provisions a public domain
7. Verifies deployment health

## CRITICAL: Always Do These

- **NEVER ask "should I deploy?"** — execute immediately on deploy intent
- **Check `railway whoami` first** — if not logged in, instruct user to run `railway login`
- **Stream build logs** — always use `railway logs --build` after deploy, never leave user blind
- **Provision domain automatically** — always run `railway domain` after successful deploy
- **Report the live URL** — final output must include the public URL

## Detection: What Can Be Deployed

Railpack auto-detects these languages from project files:

| Language | Detection Trigger |
|----------|-------------------|
| Node.js | `package.json` |
| Python | `requirements.txt`, `Pipfile`, `pyproject.toml` |
| Go | `go.mod` |
| Rust | `Cargo.toml` |
| Ruby | `Gemfile` |
| Java | `pom.xml`, `build.gradle` |
| PHP | `composer.json` |
| Deno | `deno.json`, `deno.jsonc` |
| Elixir | `mix.exs` |
| Static HTML | `index.html` |

If none detected: ask user for runtime, then create `railway.json` with explicit config.

## Workflow: First Deploy

```
Step 1: Validate
  - run: railway whoami
  - if error → tell user to run `railway login` and stop
  - run: ls -la to detect project type
  - check for .railwayignore or railway.json

Step 2: Project Setup
  - run: railway list
  - if project exists for this repo → run: railway link -p <project>
  - if new project → run: railway init -n <project-name>

Step 3: Service Setup
  - run: railway service
  - if no service linked → railway will prompt; use -s flag if service name known

Step 4: Environment Variables
  - ask user: "Any environment variables to set before deploy?"
  - if yes → run: railway variables --set "KEY=value" --set "KEY2=value2"
  - if .env file exists → parse and set each variable (NEVER log secret values)

Step 5: Deploy
  - run: railway up --detach
  - then: railway logs --build --lines 50

Step 6: Domain
  - run: railway domain
  - capture the generated URL

Step 7: Verify
  - run: railway status
  - run: railway logs --lines 20
  - report: URL + build status + any errors
```

## Workflow: Redeploy Existing Project

```
Step 1: Link (if not linked)
  - run: railway link

Step 2: Check current state
  - run: railway status
  - run: railway deployment list

Step 3: Deploy
  - run: railway up --detach
  - run: railway logs --build --lines 50

Step 4: Verify
  - run: railway logs --lines 20
```

## Workflow: Environment Management

When user asks for staging/production split:
```
1. Create staging: railway environment new staging
2. Link to staging: railway environment staging
3. Set staging vars: railway variables --set "NODE_ENV=staging" -e staging
4. Deploy to staging: railway up -e staging
5. Promote to prod: In Railway dashboard sync staging → production
   (CLI promotion not yet available — instruct user to use dashboard)
```

## Workflow: Database Provisioning

When app needs a database:
```
1. Add Postgres: railway add --database postgres
2. Add Redis: railway add --database redis
3. Add MySQL: railway add --database mysql
4. Variables injected automatically as DATABASE_URL, REDIS_URL etc.
```

## Common Patterns

### Node.js Express App
```bash
railway init -n my-api
railway up --detach
railway domain
railway logs --build --lines 100
```

### Python FastAPI / Flask
```bash
# Ensure Procfile or railway.json exists for start command
# railway.json example:
# {"build": {"builder": "NIXPACKS"}, "deploy": {"startCommand": "uvicorn main:app --host 0.0.0.0 --port $PORT"}}
railway init -n my-python-api
railway variables --set "PYTHON_VERSION=3.11"
railway up --detach
railway domain
```

### Static Site
```bash
railway init -n my-site
railway up --detach
railway domain
```

### With Secrets / Env Vars
```bash
railway variables --set "DATABASE_URL=postgres://..." --set "SECRET_KEY=xxx"
railway up --detach
```

## CI/CD Mode (No Browser)

For headless environments (GitHub Actions, scripts):
```bash
# Set token as env var — user must provide RAILWAY_TOKEN
export RAILWAY_TOKEN=<project-token>
railway up --ci --service my-service
```

## Error Handling

| Error | Fix |
|-------|-----|
| "not logged in" | Run `railway login` |
| Build fails — missing start command | Create `Procfile` or `railway.json` with startCommand |
| PORT binding error | Ensure app listens on `process.env.PORT` or `$PORT` |
| Out of memory | Scale service: `railway scale` or upgrade plan |
| Domain already exists | Domain already provisioned, run `railway domain` to show it |
| Deploy succeeds but app crashes | Check `railway logs --lines 50` for runtime errors |

## railway.json Reference

Full config file for explicit control:
```json
{
  "build": {
    "builder": "NIXPACKS",
    "buildCommand": "npm run build"
  },
  "deploy": {
    "startCommand": "npm start",
    "healthcheckPath": "/health",
    "healthcheckTimeout": 100,
    "restartPolicyType": "ON_FAILURE",
    "restartPolicyMaxRetries": 3
  }
}
```

## Key Commands Reference

See `references/railway-commands.md` for full command reference.
