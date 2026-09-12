# Advanced CI/CD Pipeline Patterns

## Table of Contents
- [Matrix Builds](#matrix-builds)
- [Monorepo Pipelines](#monorepo-pipelines)
- [Conditional Stages](#conditional-stages)
- [Artifact Caching](#artifact-caching)
- [Environment Promotion](#environment-promotion)
- [Parallel Testing](#parallel-testing)

---

## Matrix Builds

Test across multiple versions, platforms, or configurations simultaneously.

### GitHub Actions

```yaml
jobs:
  test:
    strategy:
      matrix:
        node-version: [18, 20, 22]
        os: [ubuntu-latest, macos-latest]
      fail-fast: false  # Don't cancel other jobs if one fails
    runs-on: ${{ matrix.os }}
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: ${{ matrix.node-version }}
      - run: npm ci
      - run: npm test
```

### GitLab CI

```yaml
test:
  stage: test
  parallel:
    matrix:
      - NODE_VERSION: ["18", "20", "22"]
        IMAGE: ["node:${NODE_VERSION}-alpine"]
  image: $IMAGE
  script:
    - npm ci
    - npm test
```

---

## Monorepo Pipelines

Only build and test what changed.

### GitHub Actions — Path Filtering

```yaml
on:
  push:
    branches: [main]
  pull_request:

jobs:
  detect-changes:
    runs-on: ubuntu-latest
    outputs:
      api: ${{ steps.changes.outputs.api }}
      web: ${{ steps.changes.outputs.web }}
    steps:
      - uses: actions/checkout@v4
      - uses: dorny/paths-filter@v3
        id: changes
        with:
          filters: |
            api:
              - 'packages/api/**'
            web:
              - 'packages/web/**'

  test-api:
    needs: detect-changes
    if: needs.detect-changes.outputs.api == 'true'
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: cd packages/api && npm ci && npm test

  test-web:
    needs: detect-changes
    if: needs.detect-changes.outputs.web == 'true'
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: cd packages/web && npm ci && npm test
```

### GitLab CI — Rules with Changes

```yaml
test-api:
  stage: test
  rules:
    - changes:
        - packages/api/**
  script:
    - cd packages/api
    - npm ci
    - npm test

test-web:
  stage: test
  rules:
    - changes:
        - packages/web/**
  script:
    - cd packages/web
    - npm ci
    - npm test
```

---

## Conditional Stages

Run stages based on branch, tag, or event.

### GitHub Actions

```yaml
jobs:
  deploy-staging:
    if: github.ref == 'refs/heads/main' && github.event_name == 'push'
    # ...

  deploy-production:
    if: startsWith(github.ref, 'refs/tags/v')
    # ...

  nightly-tests:
    if: github.event_name == 'schedule'
    # ...
```

### GitLab CI

```yaml
deploy_staging:
  stage: deploy
  rules:
    - if: $CI_COMMIT_BRANCH == "main"
      when: always
    - when: never

deploy_production:
  stage: deploy
  rules:
    - if: $CI_COMMIT_TAG =~ /^v\d+\.\d+\.\d+$/
      when: manual
    - when: never
```

---

## Artifact Caching

Speed up builds by caching dependencies.

### GitHub Actions

```yaml
steps:
  - uses: actions/checkout@v4
  - uses: actions/setup-node@v4
    with:
      node-version: 20
      cache: 'npm'  # Built-in caching
  - run: npm ci

  # Or manual caching for other tools:
  - uses: actions/cache@v4
    with:
      path: ~/.cache/pip
      key: pip-${{ hashFiles('requirements.txt') }}
      restore-keys: pip-
```

### GitLab CI

```yaml
variables:
  PIP_CACHE_DIR: "$CI_PROJECT_DIR/.pip-cache"

cache:
  key:
    files:
      - requirements.txt
  paths:
    - .pip-cache/
    - venv/
```

### Docker Layer Caching

```yaml
# GitHub Actions
- uses: docker/build-push-action@v5
  with:
    context: .
    cache-from: type=gha
    cache-to: type=gha,mode=max
    push: true
    tags: registry/app:${{ github.sha }}
```

---

## Environment Promotion

Promote the same artifact through environments.

### Pattern: Build Once, Deploy Many

```yaml
# GitHub Actions
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: docker build -t app:${{ github.sha }} .
      - run: docker push registry/app:${{ github.sha }}

  deploy-staging:
    needs: build
    environment: staging
    runs-on: ubuntu-latest
    steps:
      - run: deploy registry/app:${{ github.sha }} staging

  integration-tests:
    needs: deploy-staging
    runs-on: ubuntu-latest
    steps:
      - run: run-integration-tests https://staging.example.com

  deploy-production:
    needs: integration-tests
    environment: production  # Requires manual approval
    runs-on: ubuntu-latest
    steps:
      - run: deploy registry/app:${{ github.sha }} production
```

Key principle: The same image SHA is deployed to every environment. Never rebuild between environments.

---

## Parallel Testing

Split test suites across multiple runners for faster feedback.

### GitHub Actions — Test Splitting

```yaml
jobs:
  test:
    strategy:
      matrix:
        shard: [1, 2, 3, 4]
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: npm ci
      - run: npx jest --shard=${{ matrix.shard }}/4

  # Merge coverage reports after all shards complete
  coverage:
    needs: test
    runs-on: ubuntu-latest
    steps:
      - run: merge-coverage-reports
```

### GitLab CI — Parallel Keyword

```yaml
test:
  stage: test
  parallel: 4
  script:
    - npx jest --shard=$CI_NODE_INDEX/$CI_NODE_TOTAL
  artifacts:
    reports:
      junit: junit.xml
```
