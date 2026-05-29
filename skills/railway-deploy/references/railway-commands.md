# Railway CLI Complete Command Reference

## Authentication
```bash
railway login                          # Browser-based login
railway login --browserless            # Headless/CI login via token
railway whoami                         # Show current user
railway logout                         # Log out
```

## Project Management
```bash
railway init                           # Create new project (interactive)
railway init -n "project-name"         # Create with name
railway init -n "name" -w "workspace"  # Create in specific workspace
railway list                           # List all projects
railway link                           # Link current dir to project (interactive)
railway link -p <projectId>            # Link to specific project
railway link -p <id> -e production     # Link to project + environment
railway unlink                         # Remove project association
railway open                           # Open project in browser dashboard
```

## Service Management
```bash
railway service                        # Link to a service (interactive)
railway service <name-or-id>           # Link to specific service
railway add                            # Add service (interactive)
railway add --database postgres        # Add PostgreSQL
railway add --database redis           # Add Redis
railway add --database mysql           # Add MySQL
railway add --database mongo           # Add MongoDB
railway add --repo user/repo           # Add from GitHub repo
```

## Deployment
```bash
railway up                             # Deploy current directory (attaches to logs)
railway up --detach                    # Deploy without attaching to log stream
railway up --ci                        # CI mode: stream build logs then exit
railway up -s my-service               # Deploy to specific service
railway up -e staging                  # Deploy to specific environment
railway up --no-gitignore              # Include .gitignore'd files
railway redeploy                       # Redeploy latest deployment
railway down                           # Remove most recent deployment
railway deployment list                # List deployments with IDs and status
railway deployment list -s my-service  # List for specific service
```

## Environment Variables
```bash
railway variables                      # Show all variables (current env)
railway variables -s my-service        # Show for specific service
railway variables -e staging           # Show for specific environment
railway variables --json               # Output as JSON
railway variables --kv                 # Output as KEY=value pairs
railway variables --set "KEY=value"                    # Set one variable
railway variables --set "A=1" --set "B=2"              # Set multiple
railway variables --set "KEY=value" --skip-deploys     # Set without triggering deploy
railway variables -s api --set "PORT=3000"             # Set for specific service
```

## Logs
```bash
railway logs                           # Stream live logs (latest deployment)
railway logs --build                   # Stream build logs
railway logs --deployment              # Stream deployment logs
railway logs -n 100                    # Fetch last 100 lines (no streaming)
railway logs --lines 50 --filter "error"               # Filtered logs
railway logs --filter "@level:error"                   # Error logs only
railway logs --filter "@level:warn AND rate limit"     # Warn + text filter
railway logs --json                    # Logs as JSON objects
railway logs -s backend -e production  # Specific service + environment
railway logs <deploymentId>            # Logs from specific deployment
```

## Domains
```bash
railway domain                         # Generate Railway-provided domain
railway domain my-app.example.com      # Add custom domain
railway domain --port 8080             # Domain on specific port
railway domain -s my-service           # Domain for specific service
railway domain --json                  # Output domain info as JSON
```

## Environments
```bash
railway environment                    # Switch environment (interactive)
railway environment production         # Switch to production
railway environment new staging        # Create new environment
railway environment delete staging     # Delete environment
```

## Status & Info
```bash
railway status                         # Show project/service/environment info
railway whoami                         # Current user info
```

## Local Development
```bash
railway run npm start                  # Run command with Railway env vars injected
railway run python app.py              # Any command with Railway vars
railway shell                          # Open subshell with Railway vars loaded
railway connect postgres               # Connect to Postgres shell (psql)
railway connect redis                  # Connect to Redis shell
railway ssh                            # SSH into service container
```

## Volumes
```bash
railway volume                         # Manage persistent volumes
```

## Functions (Edge)
```bash
railway functions                      # Manage Railway Functions
```

## CI/CD Authentication

Two token types:
- **Project token** (`RAILWAY_TOKEN`): Scoped to one project, use in project CI
- **Account token** (`RAILWAY_API_TOKEN`): Full account access, use for multi-project automation

```bash
# In CI environment:
export RAILWAY_TOKEN=<your-project-token>
railway up --ci --service my-service

# Or set in shell:
RAILWAY_TOKEN=xxx railway up --ci
```

## Common Workflows

### Zero to Deploy
```bash
railway login
railway init -n my-app
railway up --detach
railway domain
railway logs --lines 50
```

### Update Existing App
```bash
railway link
railway up --detach
railway logs --build --lines 100
```

### Add Postgres + Deploy
```bash
railway link
railway add --database postgres
# DATABASE_URL auto-injected
railway up --detach
railway domain
```

### Staging → Production Flow
```bash
# Deploy to staging
railway up -e staging --detach
railway logs -e staging --lines 50

# Verify staging works, then promote via dashboard:
# Dashboard → Select production env → Sync → Select staging → Review → Approve
```

### Debug a Failing Deploy
```bash
railway deployment list                # Find failed deployment ID
railway logs <deploymentId> --build    # Check build logs
railway logs --lines 100              # Check runtime logs
railway status                         # Check service health
```

## Port Configuration

Apps MUST bind to `$PORT` (Railway injects this):
- Node.js: `app.listen(process.env.PORT || 3000)`
- Python: `uvicorn main:app --host 0.0.0.0 --port $PORT`
- Go: `http.ListenAndServe(":"+os.Getenv("PORT"), nil)`
- Generic: any `$PORT` reference in start command

## railway.json Reference

```json
{
  "$schema": "https://railway.com/railway.schema.json",
  "build": {
    "builder": "NIXPACKS",
    "buildCommand": "npm run build",
    "watchPatterns": ["src/**"]
  },
  "deploy": {
    "numReplicas": 1,
    "startCommand": "npm start",
    "healthcheckPath": "/health",
    "healthcheckTimeout": 100,
    "restartPolicyType": "ON_FAILURE",
    "restartPolicyMaxRetries": 3,
    "cronSchedule": null,
    "region": "us-west2"
  }
}
```

## Procfile Reference (Alternative to railway.json)

```
web: npm start
worker: node worker.js
release: python manage.py migrate
```

## Supported Regions

- `us-west1` (Oregon)
- `us-west2` (Los Angeles)
- `us-east4` (Virginia)
- `eu-west4` (Netherlands)
- `asia-southeast1` (Singapore)
- `asia-east1` (Taiwan)
- `sa-east1` (São Paulo)
- `ap-northeast1` (Tokyo)
- `ap-south1` (Mumbai)
