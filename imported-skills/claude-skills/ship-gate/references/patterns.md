# Ship Gate: Detection Patterns

Grep and regex patterns for auto-scannable checks. Claude runs these
against the codebase to detect issues.

## Table of Contents

- SEC: Security Patterns
- DB: Database Patterns
- CODE: Code Quality Patterns
- AI: AI/LLM Security Patterns
- DEP: Dependency Patterns
- FE: Frontend Quality Patterns
- OBS: Observability Patterns
- DEPLOY: Deployment Patterns

All patterns use `grep -rn` with `--include` filters. Exclude
node_modules, .next, dist, build, .git, __pycache__, venv directories
from all scans.

Base exclude flags:
```bash
EXCLUDE="--exclude-dir=node_modules --exclude-dir=.next --exclude-dir=dist --exclude-dir=build --exclude-dir=.git --exclude-dir=__pycache__ --exclude-dir=venv --exclude-dir=.venv --exclude-dir=vendor --exclude-dir=coverage"
```

---

## SEC: Security Patterns

### SEC-01: Secrets in frontend code

Scan directories that serve client-side code:

```bash
# Generic API key patterns
grep -rnE $EXCLUDE \
  "(sk-[a-zA-Z0-9]{20,}|sk-ant-[a-zA-Z0-9-]+|sk-proj-[a-zA-Z0-9-]+|AIza[a-zA-Z0-9_-]{35}|ghp_[a-zA-Z0-9]{36}|glpat-[a-zA-Z0-9_-]{20,}|xox[bsap]-[a-zA-Z0-9-]+)" \
  src/ app/ pages/ components/ public/ lib/ utils/ 2>/dev/null

# AWS keys
grep -rnE $EXCLUDE \
  "AKIA[0-9A-Z]{16}" \
  src/ app/ pages/ components/ public/ 2>/dev/null

# Stripe keys (live, not test)
grep -rnE $EXCLUDE \
  "sk_live_[a-zA-Z0-9]{24,}" \
  src/ app/ pages/ components/ public/ 2>/dev/null

# Generic secret assignment
grep -rnE $EXCLUDE \
  "(api_key|apikey|api_secret|secret_key|auth_token|access_token)\s*[:=]\s*['\"][a-zA-Z0-9_-]{16,}" \
  src/ app/ pages/ components/ public/ 2>/dev/null
```

### SEC-04: CORS wildcard

```bash
grep -rnE $EXCLUDE \
  "(origin:\s*['\"]?\*['\"]?|Access-Control-Allow-Origin.*\*|cors\(\s*\))" \
  . 2>/dev/null
```

### SEC-05: CSRF protection missing

```bash
# Check for state-changing routes without CSRF
grep -rnE $EXCLUDE \
  "(app\.(post|put|patch|delete)|router\.(post|put|patch|delete))" \
  . 2>/dev/null
# Then verify csrf middleware exists
grep -rnE $EXCLUDE \
  "(csrf|csrfToken|_csrf|CSRF_COOKIE)" \
  . 2>/dev/null
```

### SEC-08: Weak password hashing

```bash
# Check for weak hashing (md5, sha1, sha256 for passwords)
grep -rnE $EXCLUDE \
  "(md5|sha1|sha256)\s*\(" \
  . 2>/dev/null
# Verify bcrypt/argon2 usage
grep -rnE $EXCLUDE \
  "(bcrypt|argon2|scrypt)" \
  . 2>/dev/null
```

### SEC-11: CSP headers

```bash
# Check for Content-Security-Policy configuration
grep -rnE $EXCLUDE \
  "(Content-Security-Policy|contentSecurityPolicy|csp)" \
  . 2>/dev/null
# Next.js: check next.config for headers
grep -rn $EXCLUDE \
  "Content-Security-Policy" \
  next.config.* 2>/dev/null
```

### SEC-13: Unsafe eval/innerHTML

```bash
# eval usage
grep -rnE $EXCLUDE \
  "(\beval\s*\(|new\s+Function\s*\()" \
  --include="*.js" --include="*.ts" --include="*.jsx" --include="*.tsx" \
  . 2>/dev/null

# dangerouslySetInnerHTML without sanitizer
grep -rnE $EXCLUDE \
  "dangerouslySetInnerHTML" \
  --include="*.jsx" --include="*.tsx" \
  . 2>/dev/null
# Then check if DOMPurify or similar is imported in same file
```

### SEC-15: Cookie security flags

```bash
grep -rnE $EXCLUDE \
  "(set-cookie|setCookie|cookie\()" \
  . 2>/dev/null
# Verify HttpOnly, Secure, SameSite flags are present
grep -rnE $EXCLUDE \
  "(httpOnly|HttpOnly|secure:\s*true|sameSite)" \
  . 2>/dev/null
```

### SEC-06: Input validation

```bash
# Check for validation library usage
grep -rnE $EXCLUDE \
  "(from 'zod'|from 'yup'|from 'joi'|from 'class-validator'|from pydantic)" \
  . 2>/dev/null

# Check for raw req.body usage without validation
grep -rnE $EXCLUDE \
  "(req\.body\.|request\.json|request\.form)" \
  --include="*.ts" --include="*.js" --include="*.py" \
  . 2>/dev/null
```

### SEC-07: Rate limiting

```bash
grep -rnE $EXCLUDE \
  "(express-rate-limit|@upstash/ratelimit|rate-limiter|slowapi|throttle)" \
  package.json requirements.txt . 2>/dev/null
```

### SEC-09: Token expiry

```bash
grep -rnE $EXCLUDE \
  "(sign\(|jwt\.encode|createToken|signToken)" \
  --include="*.ts" --include="*.js" --include="*.py" \
  . 2>/dev/null
# Then check if expiresIn/exp is set in those calls
grep -rnE $EXCLUDE \
  "(expiresIn|exp:|expires_in|expires_delta)" \
  . 2>/dev/null
```

### SEC-14: Sensitive data in URLs/logs

```bash
# Sensitive query parameters
grep -rnE $EXCLUDE \
  "(password|token|secret|key|ssn|credit.card)=" \
  --include="*.ts" --include="*.js" --include="*.py" \
  . 2>/dev/null

# Logging full request objects
grep -rnE $EXCLUDE \
  "console\.(log|info|debug)\s*\(\s*(req|request)\s*\)" \
  . 2>/dev/null
```

### SEC-16: File upload validation

```bash
grep -rnE $EXCLUDE \
  "(multer|formidable|busboy|UploadedFile|upload\.single|upload\.array)" \
  . 2>/dev/null
# Check for file type/size validation near upload handlers
grep -rnE $EXCLUDE \
  "(fileFilter|limits|maxFileSize|allowedTypes|mimetype)" \
  . 2>/dev/null
```

### SEC-17/18: .env in repo

```bash
# Check if .env files exist in working tree
find . -maxdepth 3 -name ".env*" -not -path "*/node_modules/*" \
  -not -name ".env.example" -not -name ".env.sample" 2>/dev/null

# Check if .env is in .gitignore
grep -n "\.env" .gitignore 2>/dev/null

# Check git history for .env commits
git log --all --name-only --diff-filter=A 2>/dev/null | grep "\.env" || true
```

---

## DB: Database Patterns

### DB-03: SQL injection (string concatenation)

```bash
# Template literal SQL
grep -rnE $EXCLUDE \
  "(SELECT|INSERT|UPDATE|DELETE|FROM|WHERE).*\$\{" \
  --include="*.js" --include="*.ts" --include="*.jsx" --include="*.tsx" \
  . 2>/dev/null

# String concat SQL
grep -rnE $EXCLUDE \
  "(SELECT|INSERT|UPDATE|DELETE|FROM|WHERE).*\+\s*(req\.|params\.|body\.|query\.)" \
  . 2>/dev/null

# Python f-string SQL
grep -rnE $EXCLUDE \
  "f['\"].*\b(SELECT|INSERT|UPDATE|DELETE|FROM|WHERE)\b.*\{" \
  --include="*.py" \
  . 2>/dev/null
```

### DB-07: Supabase RLS

```bash
# Find CREATE TABLE without RLS
grep -rnl $EXCLUDE "CREATE TABLE" \
  --include="*.sql" . 2>/dev/null | while read f; do
  tables=$(grep -oP "CREATE TABLE\s+\K\S+" "$f")
  for t in $tables; do
    if ! grep -q "ENABLE ROW LEVEL SECURITY" "$f" || \
       ! grep -q "$t" <<< "$(grep 'ENABLE ROW LEVEL SECURITY' "$f")"; then
      echo "FAIL: $f - table $t missing RLS"
    fi
  done
done
```

### DB-08: service_role in client code

```bash
grep -rnE $EXCLUDE \
  "(service_role|serviceRole|SUPABASE_SERVICE_ROLE)" \
  src/ app/ pages/ components/ public/ lib/client 2>/dev/null
```

### DB-05: Connection pooling

```bash
# Check for pool configuration
grep -rnE $EXCLUDE \
  "(pool|connectionLimit|max_connections|poolSize)" \
  --include="*.ts" --include="*.js" --include="*.py" --include="*.env*" \
  . 2>/dev/null

# Supabase: check if using pooler port
grep -rnE $EXCLUDE \
  "(6543|pooler)" \
  --include="*.env*" --include="*.ts" --include="*.js" \
  . 2>/dev/null
```

### DB-06: Migrations in version control

```bash
# Check for migration directories
find . -maxdepth 3 -type d \
  \( -name "migrations" -o -name "migrate" -o -name "versions" \) \
  -not -path "*/node_modules/*" 2>/dev/null

# Check if migrations contain files
find . -path "*/migrations/*.sql" -o -path "*/migrations/*.ts" \
  -o -path "*/migrations/*.py" 2>/dev/null | head -5
```

### DB-12: PII stored unencrypted

```bash
# Search schema files for PII column names
grep -rnEi $EXCLUDE \
  "(ssn|social_security|credit_card|card_number|passport)" \
  --include="*.sql" --include="*.prisma" --include="*.py" \
  . 2>/dev/null
```

---

## CODE: Code Quality Patterns

### CODE-01: console.log in production

```bash
grep -rnE $EXCLUDE \
  "console\.(log|debug|info)\(" \
  --include="*.js" --include="*.ts" --include="*.jsx" --include="*.tsx" \
  --exclude="*.test.*" --exclude="*.spec.*" --exclude="*.config.*" \
  src/ app/ pages/ components/ lib/ utils/ 2>/dev/null
```

### CODE-03: Empty catch blocks

```bash
grep -rnPzo $EXCLUDE \
  "catch\s*\([^)]*\)\s*\{\s*\}" \
  --include="*.js" --include="*.ts" --include="*.jsx" --include="*.tsx" \
  . 2>/dev/null
```

### CODE-07: TODO-auth patterns

```bash
grep -rnEi $EXCLUDE \
  "(TODO|FIXME|HACK|XXX).*(auth|security|permission|validation|sanitiz)" \
  . 2>/dev/null
```

### CODE-08: Unhandled promise rejections

```bash
# Async functions without try-catch
grep -rnE $EXCLUDE \
  "async\s+\w+\s*\(" \
  --include="*.js" --include="*.ts" --include="*.jsx" --include="*.tsx" \
  . 2>/dev/null
# Check for .catch() or try/catch wrapping
```

### CODE-09: React error boundaries

```bash
# Check for error boundary in Next.js App Router
find . -path "*/app/error.tsx" -o -path "*/app/error.jsx" \
  -o -path "*/app/global-error.tsx" 2>/dev/null

# Check for ErrorBoundary component
grep -rnE $EXCLUDE \
  "(ErrorBoundary|error-boundary|componentDidCatch|getDerivedStateFromError)" \
  --include="*.jsx" --include="*.tsx" \
  . 2>/dev/null
```

### CODE-12: Lockfile committed

```bash
# Check for lockfile existence
ls package-lock.json pnpm-lock.yaml yarn.lock bun.lockb \
  Pipfile.lock poetry.lock Gemfile.lock go.sum Cargo.lock 2>/dev/null

# Check if lockfile is gitignored
for f in package-lock.json pnpm-lock.yaml yarn.lock; do
  if git check-ignore "$f" 2>/dev/null; then
    echo "FAIL: $f is gitignored"
  fi
done
```

### CODE-13: Wildcard versions

```bash
# Check for * or empty version in package.json
grep -nE '"[^"]+"\s*:\s*"\*"' package.json 2>/dev/null
```

### CODE-02: Async without error handling

```bash
# Find async functions
grep -rnE $EXCLUDE \
  "async\s+(function\s+)?\w+\s*\(" \
  --include="*.ts" --include="*.js" --include="*.tsx" --include="*.jsx" \
  . 2>/dev/null
# Count try/catch usage nearby
grep -rnc $EXCLUDE "try\s*{" \
  --include="*.ts" --include="*.js" --include="*.tsx" --include="*.jsx" \
  . 2>/dev/null
```

### CODE-04: Loading and error states

```bash
# Check for loading state patterns in React
grep -rnE $EXCLUDE \
  "(isLoading|loading|Skeleton|Spinner|fallback)" \
  --include="*.tsx" --include="*.jsx" \
  . 2>/dev/null

# Check for Suspense boundaries
grep -rnE $EXCLUDE \
  "(<Suspense|loading\.tsx|loading\.jsx)" \
  . 2>/dev/null
```

### CODE-05: Pagination on list endpoints

```bash
# Check API routes for unbounded queries
grep -rnE $EXCLUDE \
  "(\.findMany|\.find\(\)|\.select\(\)|SELECT \*)" \
  --include="*.ts" --include="*.js" --include="*.py" \
  . 2>/dev/null

# Check for pagination parameters
grep -rnE $EXCLUDE \
  "(limit|offset|page|skip|take|cursor|per_page)" \
  --include="*.ts" --include="*.js" --include="*.py" \
  . 2>/dev/null
```

### CODE-10: Leaked stack traces

```bash
grep -rnE $EXCLUDE \
  "(error\.stack|\.stack\)|err\.message.*res\.(json|send)|traceback)" \
  --include="*.ts" --include="*.js" --include="*.py" \
  . 2>/dev/null
```

### CODE-11: eslint-disable on security rules

```bash
grep -rnE $EXCLUDE \
  "eslint-disable.*(no-eval|no-implied-eval|no-script-url|security)" \
  --include="*.ts" --include="*.js" --include="*.tsx" --include="*.jsx" \
  . 2>/dev/null
```

### CODE-14: TypeScript strict mode

```bash
grep -n '"strict"' tsconfig.json 2>/dev/null
# Check if strict is true
grep -n '"strict":\s*true' tsconfig.json 2>/dev/null
```

---

## AI: AI/LLM Security Patterns

### AI-01: System prompt leakage

```bash
# System prompts in client-accessible files
grep -rnEi $EXCLUDE \
  "(system.?prompt|system.?message|system_instruction)" \
  src/ app/ pages/ components/ public/ 2>/dev/null

# System prompts returned in API responses
grep -rnE $EXCLUDE \
  "(system.*role|role.*system)" \
  src/ app/ pages/ components/ public/ 2>/dev/null
```

### AI-02: Prompt injection vectors

```bash
# User input concatenated directly into prompts
grep -rnE $EXCLUDE \
  "(messages\.push|content:.*\$\{|content:.*\+\s*user|prompt.*\+)" \
  --include="*.ts" --include="*.js" --include="*.py" \
  . 2>/dev/null
```

### AI-03: LLM API keys in frontend

```bash
grep -rnE $EXCLUDE \
  "(OPENAI_API_KEY|ANTHROPIC_API_KEY|GOOGLE_AI_API_KEY|sk-ant-|sk-proj-|AIza[a-zA-Z0-9_-]{35})" \
  src/ app/ pages/ components/ public/ 2>/dev/null
```

### AI-04: Rate limiting on AI endpoints

```bash
# Find AI-related API routes
grep -rnlE $EXCLUDE \
  "(openai|anthropic|claude|gpt|completion|chat/api|ai/api)" \
  --include="*.ts" --include="*.js" \
  . 2>/dev/null
# Then check for rate limiting middleware in those files
```

### AI-05: AI output sanitization

```bash
# Check if AI responses are rendered with dangerouslySetInnerHTML
grep -rnE $EXCLUDE \
  "dangerouslySetInnerHTML.*\b(response|result|completion|message|content)\b" \
  --include="*.tsx" --include="*.jsx" \
  . 2>/dev/null
```

### AI-06: MCP server input validation

```bash
# Check MCP server tool handlers for input validation
grep -rnE $EXCLUDE \
  "(tool_input|toolInput|tool_call|CallToolRequest)" \
  --include="*.ts" --include="*.js" --include="*.py" \
  . 2>/dev/null
# Check if zod/validation is applied to tool inputs
```

---

## DEP: Dependency Patterns

### DEP-01: Git/URL dependencies

```bash
grep -nE '"(git|git\+|http|https|file):' package.json 2>/dev/null
grep -nE '"github:' package.json 2>/dev/null
```

### DEP-04: npm audit

```bash
# Run npm audit and capture critical/high counts
npm audit --json 2>/dev/null | grep -c '"severity":"critical"'
npm audit --json 2>/dev/null | grep -c '"severity":"high"'
# Or for pip
pip audit --format json 2>/dev/null
```

### DEP-05: Suspicious install scripts

```bash
grep -A2 '"preinstall"\|"postinstall"\|"install"' package.json 2>/dev/null
```

### DEP-06: Wildcard versions

```bash
grep -nE '"\*"' package.json 2>/dev/null
grep -nE '"latest"' package.json 2>/dev/null
```

---

## FE: Frontend Quality Patterns

### FE-01: Meta tags

```bash
# Next.js App Router metadata
grep -rnE $EXCLUDE \
  "(export\s+(const|async\s+function)\s+metadata|generateMetadata)" \
  --include="*.tsx" --include="*.ts" \
  app/layout.* app/page.* 2>/dev/null

# HTML meta tags
grep -rnE $EXCLUDE \
  '(<title>|<meta\s+name="description"|og:title|og:description|og:image)' \
  . 2>/dev/null
```

### FE-02: Favicon

```bash
find . -maxdepth 3 \( -name "favicon.*" -o -name "icon.*" \) \
  -not -path "*/node_modules/*" 2>/dev/null
```

### FE-03: Custom 404 page

```bash
find . -maxdepth 4 \( -name "404.*" -o -name "not-found.*" \) \
  -not -path "*/node_modules/*" 2>/dev/null
```

### FE-05: Image alt text

```bash
# Find img tags without alt attribute
grep -rnE $EXCLUDE \
  '<img\s+(?![^>]*\balt\b)[^>]*>' \
  --include="*.html" --include="*.jsx" --include="*.tsx" \
  . 2>/dev/null

# Next.js Image without alt
grep -rnE $EXCLUDE \
  '<Image\s+(?![^>]*\balt\b)[^>]*/?>' \
  --include="*.jsx" --include="*.tsx" \
  . 2>/dev/null
```

### FE-09: robots.txt

```bash
find . -maxdepth 2 -name "robots.txt" \
  -not -path "*/node_modules/*" 2>/dev/null
```

### FE-07: Form validation feedback

```bash
# Check for form elements without validation attributes
grep -rnE $EXCLUDE \
  '(<input|<textarea|<select)' \
  --include="*.tsx" --include="*.jsx" --include="*.html" \
  . 2>/dev/null

# Check for validation library usage
grep -rnE $EXCLUDE \
  "(useForm|react-hook-form|formik|yup|zod.*form)" \
  --include="*.tsx" --include="*.jsx" \
  . 2>/dev/null
```

### FE-10: Image optimization

```bash
# Check for unoptimized img tags (not using Next/Image or similar)
grep -rnE $EXCLUDE \
  '<img\s' \
  --include="*.tsx" --include="*.jsx" \
  . 2>/dev/null

# Check for lazy loading
grep -rnE $EXCLUDE \
  '(loading="lazy"|lazy|lazyload)' \
  --include="*.tsx" --include="*.jsx" --include="*.html" \
  . 2>/dev/null
```

---

## OBS: Observability Patterns

### OBS-01: Error monitoring

```bash
grep -rnE $EXCLUDE \
  "(@sentry|sentry-|LogRocket|Bugsnag|datadogRum|Rollbar|Honeybadger|newrelic)" \
  package.json . 2>/dev/null
```

### OBS-03: Structured logging

```bash
# Check for logging libraries
grep -rnE $EXCLUDE \
  "(winston|pino|bunyan|morgan|log4js)" \
  package.json 2>/dev/null
# Python
grep -rnE $EXCLUDE \
  "import logging|from loguru" \
  --include="*.py" . 2>/dev/null
```

---

## DEPLOY: Deployment Patterns

### DEPLOY-09: Health check endpoint

```bash
grep -rnE $EXCLUDE \
  "(\/health|\/healthz|\/api\/health|\/status|\/readyz)" \
  --include="*.ts" --include="*.js" --include="*.py" \
  . 2>/dev/null
```

### DEPLOY-10: Console vs structured logging (server)

```bash
# Count console.log vs logger usage in API/server code
echo "console.log count:"
grep -rnc $EXCLUDE "console\.log" \
  --include="*.ts" --include="*.js" \
  api/ server/ pages/api/ app/api/ 2>/dev/null | tail -1

echo "structured logger count:"
grep -rnc $EXCLUDE "(logger\.|log\.(info|warn|error|debug))" \
  --include="*.ts" --include="*.js" \
  api/ server/ pages/api/ app/api/ 2>/dev/null | tail -1
```
