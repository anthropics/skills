---
name: ship-gate
description: >
  Pre-production audit that scans a codebase for security, database,
  deployment, code quality, AI/LLM, dependency, frontend, and observability
  issues. Intercepts deploy commands and blocks until critical items pass.
  Stack-agnostic. Use for "run ship gate", "am I ready to ship",
  "pre-launch audit", "can I deploy", "push to production", "go live
  checklist", "preflight check". Not for CI/CD setup or infra provisioning.
license: MIT
metadata:
  author: Rajaraman Arumugam
  version: 1.0.0
---

# Ship Gate

Pre-production audit that scans a codebase and reports pass/fail/manual
across 8 categories before anything ships.

## Intercept Behavior

When the user says "push to production", "deploy", "ship it", "go live",
or similar deploy-intent phrases, do NOT proceed with deployment. Instead:

1. Ask: "Have you run the ship gate? Want me to scan now?"
2. If yes, run the full audit below.
3. If the user says they already ran it, ask when. If more than 24 hours
   ago or if code changed since, recommend re-running.

## How It Works

### Step 1: Detect Stack

Run these checks in order to identify the project stack:

```
Framework detection:
  package.json exists        -> Node.js project
    "next" in dependencies   -> Next.js
    "react" in dependencies  -> React (if not Next.js)
    "vue" in dependencies    -> Vue
    "svelte" in dependencies -> Svelte
    "astro" in dependencies  -> Astro
    "express" in dependencies -> Express
    "fastify" in dependencies -> Fastify
    "hono" in dependencies   -> Hono
  requirements.txt or pyproject.toml -> Python project
    "django" present         -> Django
    "flask" present          -> Flask
    "fastapi" present        -> FastAPI
  go.mod exists              -> Go project
  Cargo.toml exists          -> Rust project

Database detection:
  "@supabase/supabase-js" in package.json -> Supabase
  supabase/ directory exists              -> Supabase
  "prisma" in dependencies                -> Prisma (check schema for DB type)
  "mongoose" in dependencies              -> MongoDB
  "pg" or "postgres" in dependencies      -> PostgreSQL
  firebase.json or .firebaserc exists     -> Firebase

Deploy target detection:
  vercel.json or .vercel/ exists          -> Vercel
  netlify.toml exists                     -> Netlify
  Dockerfile exists                       -> Docker/VPS
  fly.toml exists                         -> Fly.io
  railway.json exists                     -> Railway
  .platform/applications.yaml            -> Platform.sh

Auth detection:
  "@clerk" in dependencies                -> Clerk
  "next-auth" in dependencies             -> NextAuth
  "@supabase/auth-helpers" in deps        -> Supabase Auth
  "firebase/auth" in imports              -> Firebase Auth

AI/LLM detection:
  "openai" in dependencies                -> OpenAI
  "@anthropic-ai/sdk" in dependencies     -> Claude API
  "@google/generative-ai" in deps         -> Gemini
```

Report detected stack before proceeding. This determines which checks
are relevant. Checks tagged with a specific stack in `references/checks.md`
are skipped if that stack is not detected.

### Step 2: Run Automated Checks

Run categories in this order: SEC, DB, CODE, DEP, AI, DEPLOY, FE, OBS.
Security and database first because they produce the most critical findings.

For each category, run every auto-scannable check from
`references/checks.md` using the patterns in `references/patterns.md`.

Report progress after each category completes:
```
[1/8] Security: 3 FAIL, 12 PASS, 3 SKIP
[2/8] Database: 1 FAIL, 5 PASS, 6 SKIP
...
```

Report results as:
- PASS: check passed
- FAIL: issue found (with file path and line number)
- SKIP: not applicable to this stack

### Step 3: Manual Confirmation

For checks that cannot be automated (backup restore tested, rollback plan
exists, staging test passed), present them as a checklist and ask the user
to confirm each one.

### Step 4: Verdict

Classify results into three severities:
- CRITICAL: must fix before shipping (secrets exposed, no auth on routes,
  no HTTPS, SQL injection vectors, no RLS on Supabase tables)
- HIGH: should fix before shipping (no error boundaries, no rate limiting,
  console.logs in production, no pagination)
- ADVISORY: recommended but not blocking (no OG tags, no custom 404,
  no analytics, no SBOM)

Final output:

```
SHIP GATE REPORT
================
Stack: Next.js + Supabase + Vercel
Scan time: 12s

CRITICAL (3 items, must fix)
  FAIL  [SEC-01] API key found in src/lib/api.ts:14
  FAIL  [DB-07] RLS not enabled on "profiles" table
  FAIL  [SEC-05] No CSRF protection on /api/checkout

HIGH (5 items, should fix)
  FAIL  [CODE-01] 12 console.log statements in production code
  FAIL  [CODE-03] Empty catch block in src/utils/auth.ts:45
  FAIL  [DEP-04] 3 critical npm audit vulnerabilities
  FAIL  [DEPLOY-05] No rollback plan documented
  MANUAL [DEPLOY-06] Staging test not confirmed

ADVISORY (4 items, recommended)
  FAIL  [FE-01] Missing OG meta tags
  FAIL  [FE-03] No custom 404 page
  PASS  [OBS-01] Error monitoring configured
  SKIP  [AI-01] No AI/LLM usage detected

VERDICT: DO NOT SHIP (3 critical issues)
Fix critical items and re-run.
```

If zero critical items remain, verdict is: CLEAR TO SHIP.
If only high items remain, verdict is: SHIP WITH CAUTION (acknowledge risks).

## Categories

Eight categories, each with a code prefix. Full check details in
`references/checks.md`.

| Prefix | Category | Auto | Manual | Tool |
|--------|----------|------|--------|------|
| SEC | Security | 15 | 3 | 0 |
| DB | Database | 7 | 5 | 0 |
| DEPLOY | Deployment | 3 | 8 | 0 |
| CODE | Code Quality | 11 | 0 | 1 |
| AI | AI/LLM Security | 5 | 3 | 0 |
| DEP | Dependencies | 5 | 0 | 1 |
| FE | Frontend Quality | 7 | 3 | 0 |
| OBS | Observability | 2 | 5 | 0 |

## Scope

This skill audits. It does not fix. When it finds issues, it reports
them with file locations and remediation guidance. The user or another
skill (systematic-debugging, backend-patterns, shadcn-stack) handles
the fix.

This skill does not:
- Set up CI/CD pipelines
- Provision infrastructure
- Configure monitoring tools
- Run after deployment (it is pre-deploy only)

## Integration Points

- **karpathy-coder**: run ship-gate after karpathy-check passes — simplicity first, then production readiness
- **adversarial-reviewer**: deep security review for items ship-gate flags as critical
- **security-pen-testing**: penetration testing methodology for SEC-category findings
- **code-reviewer**: general code quality review complements ship-gate's automated checks
