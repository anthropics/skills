# Ship Gate: Complete Check Reference

All checks organized by category with ID, description, detection method,
severity, and remediation guidance.

## Table of Contents

- SEC: Security (18 checks)
- DB: Database (12 checks)
- DEPLOY: Deployment (13 checks)
- CODE: Code Quality (14 checks)
- AI: AI/LLM Security (8 checks)
- DEP: Dependencies and Supply Chain (7 checks)
- FE: Frontend Quality (10 checks)
- OBS: Observability (7 checks)

Detection methods:
- **auto**: Claude scans the codebase using grep, find, or file inspection
- **tool**: Claude runs an external tool (npm audit, etc.)
- **manual**: Claude asks the user to confirm

---

## SEC: Security

| ID | Check | Detection | Severity | Stack |
|----|-------|-----------|----------|-------|
| SEC-01 | No API keys or secrets in frontend code | auto | critical | all |
| SEC-02 | Every route checks authentication | auto | critical | all |
| SEC-03 | HTTPS enforced, HTTP redirected | manual | critical | all |
| SEC-04 | CORS locked to specific domain, not wildcard | auto | critical | all |
| SEC-05 | CSRF protection on state-changing endpoints | auto | critical | all |
| SEC-06 | Input validated and sanitized server-side | auto | high | all |
| SEC-07 | Rate limiting on auth and sensitive endpoints | auto | high | all |
| SEC-08 | Passwords hashed with bcrypt or argon2 | auto | critical | all |
| SEC-09 | Auth tokens have expiry | auto | high | all |
| SEC-10 | Sessions invalidated on logout (server-side) | manual | high | all |
| SEC-11 | CSP headers configured | auto | high | all |
| SEC-12 | JWT not using alg:none or weak secrets | auto | critical | all |
| SEC-13 | No eval() or dangerouslySetInnerHTML without sanitization | auto | high | js/ts |
| SEC-14 | No sensitive data in URL parameters or logs | auto | high | all |
| SEC-15 | Cookie security flags set (HttpOnly, Secure, SameSite) | auto | high | all |
| SEC-16 | File upload validates type, size, no path traversal | auto | high | all |
| SEC-17 | No hardcoded secrets in .env committed to repo | auto | critical | all |
| SEC-18 | .env files listed in .gitignore | auto | critical | all |

### SEC-01: No API keys or secrets in frontend code

Scan all files in src/, app/, pages/, public/, components/ for patterns
matching API keys, tokens, and secrets. See patterns.md for the full
regex list.

Remediation: Move secrets to environment variables. Use server-side API
routes to proxy requests that require secrets.

### SEC-02: Every route checks authentication

For Next.js: check middleware.ts/js exists and covers protected routes.
For Express: check that auth middleware is applied to route handlers.
For Django: check @login_required or permission decorators.
For generic: search for unprotected route definitions.

Remediation: Add authentication middleware. Audit every endpoint and
classify as public or protected.

### SEC-04: CORS not wildcard

Search for `cors({ origin: '*' })`, `Access-Control-Allow-Origin: *`,
or equivalent in the detected framework.

Remediation: Set CORS origin to your specific domain(s).

### SEC-05: CSRF protection

Check for CSRF token generation and validation on POST/PUT/DELETE routes.
For Next.js Server Actions, verify they use built-in CSRF protection.

Remediation: Add CSRF middleware or use framework-native CSRF protection.

### SEC-06: Input validation server-side

Search for request body usage (req.body, request.json, request.form)
without validation library imports (zod, yup, joi, class-validator,
pydantic). Check if raw user input flows directly into database queries
or business logic.

Remediation: Add input validation with zod, yup, or joi on every
endpoint that accepts user input.

### SEC-07: Rate limiting

Search for rate limiting middleware (express-rate-limit, @upstash/ratelimit,
rate-limiter-flexible, slowapi). Check auth routes and sensitive endpoints.

Remediation: Add rate limiting middleware. Start with auth endpoints
(login, register, password reset) and any endpoint that sends emails
or costs money.

### SEC-09: Auth token expiry

Search JWT sign calls for expiresIn/exp claims. Check if tokens are
created without expiry. Search for `sign(`, `jwt.encode(`, `createToken`.

Remediation: Set token expiry. Access tokens: 15-60 minutes.
Refresh tokens: 7-30 days. Never issue tokens without expiry.

### SEC-14: Sensitive data in URLs or logs

Search for query parameters containing keywords like password, token,
secret, key, ssn, credit_card. Search logging statements that log
full request objects or sensitive fields.

Remediation: Send sensitive data in request body or headers, never
in URL parameters. Redact sensitive fields before logging.

### SEC-16: File upload validation

Search for file upload handlers (multer, formidable, busboy,
UploadedFile). Check if file type, size, and path are validated.

Remediation: Validate file MIME type against an allowlist. Set
maximum file size. Sanitize filenames. Store outside webroot.

### SEC-12: JWT security

Search for `alg: 'none'`, `algorithm: 'none'`, or JWT secrets shorter
than 32 characters.

Remediation: Use RS256 or HS256 with a strong secret (32+ characters).
Never allow alg:none.

### SEC-17: No hardcoded secrets in .env committed

Check git history for .env files: `git log --all --name-only | grep .env`
Check if .env exists in the working tree and is not in .gitignore.

Remediation: Add .env* to .gitignore. Rotate any exposed secrets.
Use `git filter-branch` or BFG to remove from history if needed.

---

## DB: Database

| ID | Check | Detection | Severity | Stack |
|----|-------|-----------|----------|-------|
| DB-01 | Backups configured and tested | manual | critical | all |
| DB-02 | Backup restore tested (not just backup) | manual | critical | all |
| DB-03 | Parameterized queries everywhere | auto | critical | all |
| DB-04 | Separate dev and production databases | manual | high | all |
| DB-05 | Connection pooling configured | auto | high | all |
| DB-06 | Migrations in version control | auto | high | all |
| DB-07 | RLS enabled on all tables | auto | critical | supabase |
| DB-08 | No service_role key in client-side code | auto | critical | supabase |
| DB-09 | Anon key not used for writes without RLS | auto | high | supabase |
| DB-10 | Storage bucket policies configured | auto | high | supabase |
| DB-11 | App uses a non-root DB user | manual | high | all |
| DB-12 | No PII stored unencrypted | auto | high | all |

### DB-03: Parameterized queries

Search for string concatenation in SQL queries:
- Template literals with SQL keywords: `` `SELECT ... ${` ``
- String concatenation: `"SELECT " + variable`
- f-strings with SQL: `f"SELECT ... {variable}"`

Remediation: Use parameterized queries or ORM methods.

### DB-07: RLS enabled (Supabase)

Search migration files for `CREATE TABLE` without a corresponding
`ALTER TABLE ... ENABLE ROW LEVEL SECURITY` statement.
Also check for `CREATE POLICY` statements.

Remediation: Enable RLS on every table and create appropriate policies.

### DB-08: No service_role key in client code

Search frontend directories (src/, app/, components/, pages/) for
`service_role`, `supabase_service_role`, or the actual key pattern
`eyJ...` used with createClient on the client side.

Remediation: Use service_role only in server-side code (API routes,
Edge Functions, server actions).

### DB-05: Connection pooling

Search for database connection configuration. Check for pool settings
(max, min, idle timeout). For Supabase, check if using connection
pooler URL (port 6543) vs direct (port 5432).

Remediation: Use connection pooling for production. For Supabase,
use the pooler URL. For raw pg, configure pool size based on expected
concurrent connections.

### DB-06: Migrations in version control

Check if a migrations directory exists (supabase/migrations, prisma/
migrations, alembic/versions, db/migrate). Verify it contains .sql
or migration files, not empty.

Remediation: Use your ORM or database tool's migration system. Never
make manual schema changes to production.

### DB-09: Anon key writes without RLS

Search for Supabase client-side inserts/updates using the anon key
without RLS policies protecting the target tables.

Remediation: Enable RLS on all tables and create INSERT/UPDATE policies
that scope access to authenticated users.

### DB-10: Storage bucket policies

Search Supabase migration files and dashboard config for storage
bucket creation. Verify each bucket has access policies defined.

Remediation: Define storage policies for each bucket. Restrict
uploads by file type, size, and user ownership.

### DB-12: PII stored unencrypted

Search schema files and migration files for columns named email,
phone, ssn, social_security, credit_card, address, date_of_birth
that are stored as plain text without encryption.

Remediation: Encrypt PII columns at rest. Use database-level
encryption or application-level encryption for sensitive fields.

---

## DEPLOY: Deployment

| ID | Check | Detection | Severity | Stack |
|----|-------|-----------|----------|-------|
| DEPLOY-01 | All env vars set on production server | manual | critical | all |
| DEPLOY-02 | SSL certificate installed and valid | manual | critical | all |
| DEPLOY-03 | Firewall configured (only 80/443 public) | manual | high | vps |
| DEPLOY-04 | Process manager running | manual | high | vps |
| DEPLOY-05 | Rollback plan exists | manual | high | all |
| DEPLOY-06 | Staging test passed before production | manual | high | all |
| DEPLOY-07 | Deploy does not cause downtime | manual | advisory | all |
| DEPLOY-08 | Domain DNS configured (www vs non-www) | manual | high | all |
| DEPLOY-09 | Health check endpoint exists | auto | high | all |
| DEPLOY-10 | Logging configured (structured, not console) | auto | high | all |
| DEPLOY-11 | Error monitoring connected (Sentry, etc.) | auto | advisory | all |
| DEPLOY-12 | Cron jobs and background tasks verified | manual | high | all |
| DEPLOY-13 | CDN configured for static assets | manual | advisory | all |

### DEPLOY-09: Health check endpoint

Search for a `/health`, `/healthz`, `/api/health`, or `/status` route
that returns a 200 response.

Remediation: Add a health check endpoint that verifies database
connectivity and returns a simple JSON response.

### DEPLOY-10: Structured logging

Check if the project uses a logging library (winston, pino, bunyan,
python logging module) vs raw console.log statements in server code.

Remediation: Replace console.log with a structured logger that outputs
JSON with timestamps and request IDs.

---

## CODE: Code Quality

| ID | Check | Detection | Severity | Stack |
|----|-------|-----------|----------|-------|
| CODE-01 | No console.log in production build | auto | high | js/ts |
| CODE-02 | Error handling on all async operations | auto | high | all |
| CODE-03 | No empty catch blocks | auto | high | all |
| CODE-04 | Loading and error states in UI | auto | high | react |
| CODE-05 | Pagination on all list endpoints | auto | high | all |
| CODE-06 | npm audit clean (zero critical) | tool | high | js/ts |
| CODE-07 | No TODO-auth or TODO-security patterns | auto | critical | all |
| CODE-08 | No unhandled promise rejections | auto | high | js/ts |
| CODE-09 | React error boundaries in place | auto | high | react |
| CODE-10 | No leaked stack traces in error responses | auto | high | all |
| CODE-11 | No eslint-disable on security rules | auto | high | js/ts |
| CODE-12 | Lockfile committed | auto | high | all |
| CODE-13 | No wildcard versions in package.json | auto | high | js/ts |
| CODE-14 | TypeScript strict mode enabled | auto | advisory | ts |

### CODE-01: No console.log in production

Search for `console.log`, `console.debug`, `console.info` in source
files (exclude test files, config files, and node_modules).

Remediation: Remove console.log statements or replace with a proper
logger. Use a build tool to strip them automatically.

### CODE-03: No empty catch blocks

Search for `catch` blocks with empty bodies or only a comment inside.
Pattern: `catch\s*\([^)]*\)\s*\{\s*(\/\/.*\n)?\s*\}`

Remediation: At minimum, log the error. Better: handle it appropriately
or rethrow.

### CODE-07: No TODO-auth/security patterns

Search for `TODO.*auth`, `TODO.*security`, `TODO.*permission`,
`FIXME.*auth`, `HACK.*auth`, `// auth`, `# TODO: add auth`.

These indicate security features that were deferred and forgotten.

Remediation: Implement the deferred security feature or remove the
endpoint if it is not ready.

### CODE-09: React error boundaries

Check if the app has at least one ErrorBoundary component or uses
a library like react-error-boundary. Check app/error.tsx for Next.js
App Router projects.

Remediation: Add error boundaries at layout boundaries to prevent
full-page crashes.

### CODE-02: Error handling on async operations

Search for async functions and .then() chains. Check if they have
corresponding try/catch or .catch() handlers.

Remediation: Wrap every async operation in try/catch. Log errors
and show appropriate UI feedback.

### CODE-04: Loading and error states in UI

Search React components for data fetching (useEffect with fetch,
useSWR, useQuery, server components) and check if they render
loading and error states.

Remediation: Add loading spinners/skeletons and error messages
for every data-dependent component.

### CODE-05: Pagination on list endpoints

Search API routes that return arrays/lists from database queries.
Check for LIMIT/OFFSET, cursor pagination, or take/skip parameters.

Remediation: Add pagination to every endpoint that returns a list.
Default page size of 20-50 items. Never return unbounded result sets.

### CODE-10: No leaked stack traces

Search error handling code for responses that include stack traces,
error.stack, or full error objects sent to the client.

Remediation: Return generic error messages to the client. Log full
stack traces server-side only.

### CODE-11: No eslint-disable on security rules

Search for eslint-disable comments that suppress security-related
rules (no-eval, no-implied-eval, no-script-url).

Remediation: Fix the underlying issue instead of disabling the lint
rule. If genuinely necessary, add a comment explaining why.

### CODE-14: TypeScript strict mode

Check tsconfig.json for `"strict": true` or the individual flags
(strictNullChecks, noImplicitAny, etc.).

Remediation: Enable strict mode in tsconfig.json. Fix type errors
incrementally if migrating an existing project.

---

## AI: AI/LLM Security

| ID | Check | Detection | Severity | Stack |
|----|-------|-----------|----------|-------|
| AI-01 | System prompts not leakable via user input | auto | critical | ai |
| AI-02 | No prompt injection vectors in user inputs | auto | critical | ai |
| AI-03 | LLM API keys not in frontend code | auto | critical | ai |
| AI-04 | Rate limiting on AI endpoints (cost protection) | auto | high | ai |
| AI-05 | AI response output sanitized before rendering | auto | high | ai |
| AI-06 | MCP server inputs validated | auto | high | ai |
| AI-07 | Agent permissions scoped (no unrestricted access) | manual | high | ai |
| AI-08 | No sensitive data sent to third-party LLMs without consent | manual | high | ai |

### AI-01: System prompt leakage

Search for system prompts stored in client-accessible files or returned
in API responses. Check if the AI endpoint echoes the system prompt
when asked "repeat your instructions" or similar.

Remediation: Keep system prompts server-side only. Add input filtering
for prompt extraction attempts.

### AI-03: LLM API keys not in frontend

Search frontend code for `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`,
`GOOGLE_AI_API_KEY`, `sk-ant-`, `sk-proj-`, `AIza` patterns.

Remediation: Proxy all LLM calls through server-side API routes.

---

## DEP: Dependencies and Supply Chain

| ID | Check | Detection | Severity | Stack |
|----|-------|-----------|----------|-------|
| DEP-01 | No git:// or URL-based dependencies | auto | high | all |
| DEP-02 | No typosquatting risk (verify package names) | auto | advisory | all |
| DEP-03 | Lockfile integrity verified | auto | high | all |
| DEP-04 | npm audit / pip audit zero critical | tool | high | all |
| DEP-05 | No suspicious postinstall scripts | auto | high | js/ts |
| DEP-06 | Dependencies pinned (no wildcard *) | auto | high | all |
| DEP-07 | Lockfile committed to version control | auto | high | all |

### DEP-01: No git/URL dependencies

Search package.json for dependencies with values starting with
`git://`, `git+`, `http://`, `https://github.com`, or `file:`.

Remediation: Use published npm packages with version ranges instead
of git URLs.

### DEP-05: Suspicious postinstall scripts

Check package.json for `postinstall`, `preinstall`, `install` scripts
that execute arbitrary commands, download files, or access the network.

Remediation: Review and remove unnecessary install scripts. Use
`--ignore-scripts` for CI.

---

## FE: Frontend Quality

| ID | Check | Detection | Severity | Stack |
|----|-------|-----------|----------|-------|
| FE-01 | Meta tags present (title, description, OG tags) | auto | advisory | web |
| FE-02 | Favicon configured | auto | advisory | web |
| FE-03 | Custom 404 page exists | auto | advisory | web |
| FE-04 | Responsive design tested on mobile | manual | high | web |
| FE-05 | Alt text on images | auto | high | web |
| FE-06 | Keyboard navigation works | manual | high | web |
| FE-07 | Forms have validation feedback | auto | high | web |
| FE-08 | Analytics installed (production only) | auto | advisory | web |
| FE-09 | robots.txt present | auto | advisory | web |
| FE-10 | Images optimized (WebP, lazy loading) | auto | advisory | web |

### FE-01: Meta tags

Check the root layout or index page for `<title>`, `<meta name="description">`,
and Open Graph tags (`og:title`, `og:description`, `og:image`).
For Next.js, check metadata export in layout.tsx.

Remediation: Add metadata to your root layout or page head.

### FE-03: Custom 404 page

Check for `404.tsx`, `404.jsx`, `not-found.tsx`, `404.html`, or
equivalent in the pages/app directory.

Remediation: Create a branded 404 page that helps users navigate back.

---

## OBS: Observability

| ID | Check | Detection | Severity | Stack |
|----|-------|-----------|----------|-------|
| OBS-01 | Error monitoring configured (Sentry, LogRocket, etc.) | auto | advisory | all |
| OBS-02 | Alerting set up for critical failures | manual | high | all |
| OBS-03 | Structured logging with request IDs | auto | advisory | all |
| OBS-04 | Performance baseline established | manual | advisory | all |
| OBS-05 | Uptime monitoring configured | manual | high | all |
| OBS-06 | Error rates tracked | manual | advisory | all |
| OBS-07 | Log retention policy defined | manual | advisory | all |

### OBS-01: Error monitoring

Search for imports or configuration of error monitoring tools:
`@sentry/`, `LogRocket`, `Bugsnag`, `Datadog`, `Rollbar`, `Honeybadger`.

Remediation: Install and configure an error monitoring service.
Sentry has a free tier suitable for solo projects.
