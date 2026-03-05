---
name: github-actions-builder
description: Create and optimize GitHub Actions CI/CD workflows. Use when users need to set up automated testing, deployment pipelines, release automation, or any GitHub Actions workflow. Triggers on requests like "create a GitHub Action", "set up CI/CD", "automate deployment", "github workflow", "actions pipeline", or "automate releases".
---

# GitHub Actions Builder

Create efficient, maintainable CI/CD workflows for GitHub repositories.

## Workflow Structure

### Basic Workflow Anatomy

```yaml
name: CI                          # Display name in GitHub UI

on:                               # Trigger events
  push:
    branches: [main]
  pull_request:
    branches: [main]

permissions:                      # Explicit permissions (security best practice)
  contents: read

jobs:
  build:                          # Job identifier
    runs-on: ubuntu-latest        # Runner environment

    steps:
      - uses: actions/checkout@v4 # Clone repository

      - name: Setup Node.js
        uses: actions/setup-node@v4
        with:
          node-version: '20'
          cache: 'npm'

      - name: Install dependencies
        run: npm ci

      - name: Run tests
        run: npm test
```

## Common Workflow Patterns

### Pull Request Checks

```yaml
name: PR Checks

on:
  pull_request:
    branches: [main]

permissions:
  contents: read
  pull-requests: write

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: actions/setup-node@v4
        with:
          node-version: '20'
          cache: 'npm'

      - run: npm ci
      - run: npm run lint
      - run: npm test

  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: '20'
          cache: 'npm'
      - run: npm ci
      - run: npm run build
```

### Release on Tag

```yaml
name: Release

on:
  push:
    tags:
      - 'v*'

permissions:
  contents: write

jobs:
  release:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: actions/setup-node@v4
        with:
          node-version: '20'
          cache: 'npm'

      - run: npm ci
      - run: npm run build

      - name: Create Release
        uses: softprops/action-gh-release@v1
        with:
          files: dist/*
          generate_release_notes: true
```

### Scheduled Jobs

```yaml
name: Nightly Build

on:
  schedule:
    - cron: '0 0 * * *'  # Daily at midnight UTC
  workflow_dispatch:      # Allow manual trigger

jobs:
  nightly:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: npm ci
      - run: npm run build
      - run: npm run e2e-tests
```

### Matrix Builds

```yaml
jobs:
  test:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, windows-latest, macos-latest]
        node-version: [18, 20, 22]
      fail-fast: false  # Continue other jobs if one fails

    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: ${{ matrix.node-version }}
      - run: npm ci
      - run: npm test
```

## Language-Specific Patterns

### Node.js

```yaml
- uses: actions/setup-node@v4
  with:
    node-version: '20'
    cache: 'npm'

- run: npm ci              # Use ci for reproducible builds
- run: npm run build
- run: npm test
```

### Python

```yaml
- uses: actions/setup-python@v5
  with:
    python-version: '3.12'
    cache: 'pip'

- run: pip install -r requirements.txt
- run: pytest
```

### Go

```yaml
- uses: actions/setup-go@v5
  with:
    go-version: '1.22'

- run: go mod download
- run: go build ./...
- run: go test ./...
```

### Rust

```yaml
- uses: dtolnay/rust-toolchain@stable

- uses: Swatinem/rust-cache@v2

- run: cargo build --release
- run: cargo test
```

### Docker

```yaml
- uses: docker/setup-buildx-action@v3

- uses: docker/login-action@v3
  with:
    registry: ghcr.io
    username: ${{ github.actor }}
    password: ${{ secrets.GITHUB_TOKEN }}

- uses: docker/build-push-action@v5
  with:
    push: ${{ github.event_name != 'pull_request' }}
    tags: ghcr.io/${{ github.repository }}:latest
    cache-from: type=gha
    cache-to: type=gha,mode=max
```

## Job Dependencies and Outputs

### Sequential Jobs

```yaml
jobs:
  build:
    runs-on: ubuntu-latest
    outputs:
      version: ${{ steps.version.outputs.version }}
    steps:
      - id: version
        run: echo "version=$(cat VERSION)" >> $GITHUB_OUTPUT

  deploy:
    needs: build  # Waits for build to complete
    runs-on: ubuntu-latest
    steps:
      - run: echo "Deploying version ${{ needs.build.outputs.version }}"
```

### Conditional Jobs

```yaml
jobs:
  test:
    runs-on: ubuntu-latest
    # ... test steps

  deploy-staging:
    needs: test
    if: github.ref == 'refs/heads/main'
    runs-on: ubuntu-latest
    # ... deploy steps

  deploy-production:
    needs: deploy-staging
    if: github.event_name == 'release'
    runs-on: ubuntu-latest
    # ... deploy steps
```

## Secrets and Environment Variables

### Using Secrets

```yaml
jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
      - name: Deploy
        env:
          API_KEY: ${{ secrets.API_KEY }}
        run: ./deploy.sh
```

### Environments

```yaml
jobs:
  deploy:
    runs-on: ubuntu-latest
    environment: production  # Uses secrets from "production" environment
    steps:
      - name: Deploy to production
        run: ./deploy.sh
```

## Caching Strategies

### Dependency Caching

```yaml
# Node.js (automatic with setup-node)
- uses: actions/setup-node@v4
  with:
    cache: 'npm'

# Manual cache
- uses: actions/cache@v4
  with:
    path: ~/.npm
    key: ${{ runner.os }}-node-${{ hashFiles('**/package-lock.json') }}
    restore-keys: |
      ${{ runner.os }}-node-
```

### Build Artifact Caching

```yaml
- uses: actions/cache@v4
  with:
    path: |
      .next/cache
      node_modules/.cache
    key: ${{ runner.os }}-build-${{ hashFiles('**/package-lock.json') }}-${{ hashFiles('**/*.ts', '**/*.tsx') }}
    restore-keys: |
      ${{ runner.os }}-build-${{ hashFiles('**/package-lock.json') }}-
```

## Reusable Workflows

### Define Reusable Workflow

```yaml
# .github/workflows/reusable-deploy.yml
name: Reusable Deploy

on:
  workflow_call:
    inputs:
      environment:
        required: true
        type: string
    secrets:
      deploy_key:
        required: true

jobs:
  deploy:
    runs-on: ubuntu-latest
    environment: ${{ inputs.environment }}
    steps:
      - uses: actions/checkout@v4
      - run: ./deploy.sh
        env:
          DEPLOY_KEY: ${{ secrets.deploy_key }}
```

### Use Reusable Workflow

```yaml
jobs:
  deploy-staging:
    uses: ./.github/workflows/reusable-deploy.yml
    with:
      environment: staging
    secrets:
      deploy_key: ${{ secrets.STAGING_DEPLOY_KEY }}
```

## Security Best Practices

### Minimal Permissions

```yaml
permissions:
  contents: read      # Only what's needed
  pull-requests: write

# Or per-job
jobs:
  build:
    permissions:
      contents: read
```

### Pin Action Versions

```yaml
# Good: pinned to commit SHA
- uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11

# Acceptable: pinned to major version
- uses: actions/checkout@v4

# Avoid: unpinned or mutable tags
- uses: actions/checkout@main
```

### Secrets in Pull Requests

```yaml
# Don't expose secrets to PRs from forks
jobs:
  test:
    if: github.event_name != 'pull_request' || github.event.pull_request.head.repo.full_name == github.repository
    steps:
      - run: ./test.sh
        env:
          SECRET: ${{ secrets.MY_SECRET }}
```

## Debugging

### Enable Debug Logging

Set repository secret:
- `ACTIONS_STEP_DEBUG` = `true`
- `ACTIONS_RUNNER_DEBUG` = `true`

### Debug Step

```yaml
- name: Debug info
  run: |
    echo "Event: ${{ github.event_name }}"
    echo "Ref: ${{ github.ref }}"
    echo "SHA: ${{ github.sha }}"
    echo "Actor: ${{ github.actor }}"
```

## Workflow Checklist

- [ ] Explicit `permissions` block (least privilege)
- [ ] Actions pinned to specific versions
- [ ] Dependency caching enabled
- [ ] `fail-fast: false` for matrix if appropriate
- [ ] Timeouts set for long-running jobs
- [ ] Concurrency controls if needed
- [ ] Secrets not exposed to fork PRs
