---
name: deploy-check
description: Pre-flight check before pushing to production. Catches TypeScript errors, accidentally staged secrets, pending migrations, and hygiene gaps. Use when about to deploy, push to production, or merge to main branch.
license: Apache-2.0
---


Run a pre-flight check before pushing to production. Works with any stack.

## Steps

### 1. Check what's being pushed
```bash
git status
git diff origin/main...HEAD --stat
git log origin/main..HEAD --oneline
```
Show the user: "X commits, Y files about to go live." List the commit messages so they can see at a glance what's shipping.

### 2. TypeScript check (if applicable)
Look for `tsconfig.json` in the repo. If found:
```bash
npx tsc --noEmit
```
Run from the directory that contains `tsconfig.json` (could be root or a `frontend/` subfolder — check first).

If errors: list every error with file + line number. Do NOT recommend pushing until fixed.
If no TypeScript in project: skip this step and note it.

### 3. Check for accidentally staged secrets
```bash
git diff --cached --name-only | grep -iE '\.env|secret|key|credential|token|password'
```
If ANY file matches: STOP. Warn loudly. Never let secrets get committed.

Also check unstaged changes:
```bash
git diff --name-only | grep -iE '\.env'
```

### 4. Dependency / schema changes
- Look for migration files (common patterns: `migrations/`, `schema.sql`, `*.migration.ts`, `db/migrate/`). If any changed since last commit, remind user to run migrations before deploying.
- Check `package.json`, `requirements.txt`, `go.mod`, `Cargo.toml` — if dependencies changed, flag which ones are new so user can confirm they're available in the production environment.
- If new environment variables appear in the diff (search for `os.getenv`, `process.env`, `ENV[`), list them and ask: are these set in your production environment?

### 5. Hygiene reminders (not blockers)
Read the commit messages and changed files, then surface these as gentle reminders:

- **Changelog / release notes**: Did anything user-visible ship (new feature, fix, UI change)? If yes, remind them to update their changelog.
- **README**: Did the setup steps, architecture, or env vars change? If yes, remind them to update the README.
- **Docs / API docs**: If new endpoints were added, remind them to document them.

These do NOT block the push. Just surface them.

### 6. Output the verdict

**Green:**
```
✅ TypeScript: no errors
✅ No secrets staged
✅ No migrations pending
✅ Dependencies: no new packages
📝 Changelog: [reminded / not needed]
→ safe to push
```

**Red:**
```
❌ TypeScript: 3 errors — fix these first
   src/auth.ts:42 — Property 'user' does not exist on type 'Session'
⚠️  .env.local is staged — remove it before committing
⚠️  schema.sql changed — run migrations in prod first
📝 2 new env vars in diff — confirm they're set in production
→ fix blockers before pushing
```
