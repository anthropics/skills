# Docker Compose Patterns For Worktrees

## Pattern 1: Override File Per Worktree

Base compose file remains shared; each worktree has a local override.

`docker-compose.worktree.yml`:

```yaml
services:
  app:
    ports:
      - "3010:3000"
  db:
    ports:
      - "5442:5432"
  redis:
    ports:
      - "6389:6379"
```

Run:

```bash
docker compose -f docker-compose.yml -f docker-compose.worktree.yml up -d
```

## Pattern 2: `.env` Driven Ports

Use compose variable substitution and write worktree-specific values into `.env.local`.

`docker-compose.yml` excerpt:

```yaml
services:
  app:
    ports: ["${APP_PORT:-3000}:3000"]
  db:
    ports: ["${DB_PORT:-5432}:5432"]
```

Worktree `.env.local`:

```env
APP_PORT=3010
DB_PORT=5442
REDIS_PORT=6389
```

## Pattern 3: Project Name Isolation

Use unique compose project name so container, network, and volume names do not collide.

```bash
docker compose -p myapp_wt_auth up -d
```

## Common Mistakes

- Reusing default `5432` from multiple worktrees simultaneously
- Sharing one database volume across incompatible migration branches
- Forgetting to scope compose project name per worktree
