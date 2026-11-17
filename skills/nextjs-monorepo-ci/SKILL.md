---
name: nextjs-monorepo-ci
description: Design, fix, and extend GitLab CI/CD pipelines for Next.js monorepos — multi-stage pipelines (validate, security, build, obfuscate, package, notify), Kaniko image builds, Semgrep SAST/secrets, gitleaks, javascript-obfuscator standalone output, Harbor registry, and IndexNow notify stage. Use this skill whenever the user mentions GitLab CI, a failing CI job, gitleaks, Kaniko, javascript-obfuscator, Harbor push, or any pipeline work in a Next.js monorepo — even if they just say "CI is broken" or "add a new app to the pipeline" without more detail.
---

# nextjs-monorepo-ci

GitLab CI/CD for Next.js monorepos: six-stage pipeline from lint to deploy notification. Covers security scanning, standalone-output obfuscation, unprivileged Kaniko builds, and post-deploy IndexNow pings.

## When to use

- Adding or fixing CI stages (validate / security / build / obfuscate / package / notify)
- Debugging `npm ci` failures, artifact paths, or `cd`-then-`cp` path issues
- Tuning `javascript-obfuscator` settings on Next.js `.next/standalone` output
- Switching from Docker-in-Docker to Kaniko for unprivileged builds
- Configuring gitleaks with allowlists for public tokens (IndexNow keys, GA IDs)
- Adding a new app (e.g., `kb`) to an existing multi-app pipeline

Do NOT use for:
- GitHub Actions pipelines (different syntax and runner model)
- Non-Next.js Node.js apps

## Pipeline structure

```
validate → security → build → obfuscate → package → notify
```

Each stage uses YAML anchors (`.app_build`, `.app_obfuscate`, `.kaniko_package`) that concrete jobs extend with a single `APP_NAME` variable.

### Stage: validate

```yaml
lint-web:
  stage: validate
  image: node:24-alpine
  cache:
    key: web-${CI_COMMIT_REF_SLUG}
    paths: [apps/web/node_modules/]
    policy: pull
  before_script:
    - cd apps/web && npm ci
  script:
    - npm run lint
    - npx tsc --noEmit

test-web:
  stage: validate
  image: node:24-alpine
  cache:
    key: web-${CI_COMMIT_REF_SLUG}
    paths: [apps/web/node_modules/]
    policy: pull-push
  before_script:
    - cd apps/web && npm ci
  script:
    - npm test -- --reporter=default --reporter=junit --outputFile.junit=junit/results.xml
  artifacts:
    reports:
      junit: apps/web/junit/results.xml
    expire_in: 7 days
    when: always
  allow_failure: true
```

### Stage: security

Uses Semgrep (secrets + SAST), gitleaks, and hadolint. Gitleaks requires a `.gitleaks.toml` for public-token allowlists:

```toml
# .gitleaks.toml — allowlist public tokens that are not secrets
[allowlist]
  description = "Public tokens that are not secrets"
  paths = [
    '''apps/.*/public/.*\.txt''',
  ]
  regexes = [
    '''G-[A-Z0-9]{8,}''',          # Google Analytics Measurement IDs
    '''[0-9a-f]{32}''',             # IndexNow verification keys
  ]
```

```yaml
gitleaks:
  stage: security
  image:
    name: zricethezav/gitleaks:latest
    entrypoint: [""]
  script:
    - gitleaks detect --source . --config .gitleaks.toml --report-format json --report-path gitleaks.json --exit-code 1
```

### Stage: build

```yaml
.app_build:
  stage: build
  image: node:24-alpine
  script:
    - cd apps/${APP_NAME} && npm ci && npm run build
  artifacts:
    paths:
      - apps/${APP_NAME}/.next/
      - apps/${APP_NAME}/public/
    expire_in: 1 day
  rules:
    - if: $CI_COMMIT_BRANCH == "main"
```

**Critical**: artifacts must collect `.next/` and `public/` from the same directory `cd` moved to. Do NOT use a subsequent `cp` — artifacts paths are relative to `$CI_PROJECT_DIR`, not the shell's cwd.

### Stage: obfuscate

Obfuscates Next.js standalone output with `javascript-obfuscator`. **Must exclude** Turbopack runtime and instrumentation chunks or the server will crash at startup:

```yaml
.app_obfuscate:
  stage: obfuscate
  image: node:24-alpine
  script:
    - npm install -g javascript-obfuscator
    - |
      find apps/${APP_NAME}/.next/standalone -name "*.js" \
          -not -path "*/node_modules/*" \
          -not -name "instrumentation.js" \
          -not -path "*[turbopack]*" \
          -not -path "*[externals]*" | while read jsfile; do
        javascript-obfuscator "$jsfile" \
          --output "$jsfile" \
          --compact true \
          --control-flow-flattening true \
          --control-flow-flattening-threshold 0.4 \
          --string-array true \
          --string-array-threshold 0.5 \
          --string-array-encoding base64 \
          --rename-globals false \
          --self-defending false \
          --target node
      done
```

> **Why exclude `[turbopack]*` and `[externals]*`?** These chunks contain dynamic module loaders. Obfuscating them breaks `_0x…` function references at runtime, causing `ChunkLoadError: Failed to load chunk` on the instrumentation hook.

### Stage: package (Kaniko)

Kaniko runs unprivileged — no DinD, no privileged pods:

```yaml
.kaniko_package:
  stage: package
  image:
    name: gcr.io/kaniko-project/executor:debug
    entrypoint: [""]
  before_script:
    - |
      mkdir -p /kaniko/.docker
      AUTH="$(printf '%s:%s' "$HARBOR_USERNAME" "$HARBOR_PASSWORD" | base64 | tr -d '\n')"
      printf '{"auths":{"%s":{"auth":"%s"}}}' "$HARBOR_REGISTRY" "$AUTH" \
        > /kaniko/.docker/config.json
  rules:
    - if: $CI_COMMIT_BRANCH == "main"
```

Dockerfiles are minimal — they package pre-built artifacts, not build from source:

```dockerfile
FROM node:22-alpine
RUN apk upgrade --no-cache && \
    rm -rf /usr/local/lib/node_modules/npm /usr/local/bin/npm /usr/local/bin/npx
WORKDIR /app
ENV NODE_ENV=production
COPY .next/standalone ./
COPY .next/static ./.next/static
COPY public ./public
RUN addgroup -g 1001 -S nodejs && adduser -S nextjs -u 1001
USER nextjs
EXPOSE 3000
CMD ["node", "server.js"]
```

**`.dockerignore` must NOT exclude `.next/`** — the pre-built standalone output is needed in the build context.

### Stage: notify (IndexNow)

```yaml
indexnow:
  stage: notify
  image: alpine:latest
  needs: [package-web, package-buy, package-kb]
  before_script:
    - apk add --no-cache curl
  script:
    - |
      curl -sf -o /dev/null -X POST "https://api.indexnow.org/IndexNow" \
        -H "Content-Type: application/json; charset=utf-8" \
        -d '{"host":"www.example.com","key":"YOUR_KEY","urlList":["https://www.example.com/"]}'
  rules:
    - if: $CI_COMMIT_BRANCH == "main"
  allow_failure: true
```

Serve the IndexNow key file from `public/` in the Next.js app:

```bash
echo -n "YOUR_KEY" > apps/web/public/YOUR_KEY.txt
```

## Common failure patterns

| Symptom | Cause | Fix |
|---------|-------|-----|
| `cp: cannot stat 'apps/web/.next'` | `cd apps/web` shifts cwd; subsequent `cp` uses relative path | Remove the `cp` — use artifacts `paths` instead |
| `.next/standalone not found` in Docker build | `.dockerignore` excludes `.next` | Remove `.next` from `.dockerignore` |
| `ChunkLoadError: _0x… is not a function` | Obfuscator mangled Turbopack runtime chunks | Exclude `*[turbopack]*` and `*[externals]*` from find |
| `npm ci` fails: no lockfile | New app scaffolded but `npm install` never run | Run `npm install` locally first, commit `package-lock.json` |
| gitleaks blocks on IndexNow key | 32-char hex looks like generic API key | Add regex allowlist to `.gitleaks.toml` |

## Example prompts

- *"My CI is failing with `cp: cannot stat 'apps/web/.next'`. What's the fix?"*
- *"How do I add the new `apps/kb` app to the existing six-stage pipeline?"*
- *"gitleaks is blocking on an IndexNow key — how do I add it to the allowlist?"*
- *"The app crashes with `ChunkLoadError: _0x… is not a function` after obfuscation. What's happening?"*
- *"Show me how to configure Kaniko to push to our Harbor registry."*
- *"I want to add Semgrep SAST scanning to our validate stage."*

## Related skills

- [`k8s-nextjs-deploy`](./k8s-nextjs-deploy/SKILL.md) — deploy the Docker images built by this pipeline
- [`confluence-to-nextjs`](./confluence-to-nextjs/SKILL.md) — when adding a `kb` app to the monorepo
