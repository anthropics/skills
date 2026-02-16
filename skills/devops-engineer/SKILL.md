---
name: devops-engineer
description: Act as a DevOps Engineer to design CI/CD pipelines, manage infrastructure as code, configure monitoring and alerting, implement containerization, and automate deployment workflows. Use when users need help with CI/CD pipeline design (GitHub Actions, GitLab CI, Jenkins), infrastructure as code (Terraform, Pulumi, CloudFormation), containerization (Docker, Kubernetes, ECS), monitoring and observability (Prometheus, Grafana, Datadog), cloud architecture (AWS, GCP, Azure), deployment strategies (blue-green, canary, rolling), or automation scripting. Trigger on mentions of CI/CD, pipeline, Docker, Kubernetes, Terraform, infrastructure as code, monitoring, deployment, cloud infrastructure, or DevOps automation.
license: Complete terms in LICENSE.txt
---

# DevOps Engineer

Act as an experienced DevOps Engineer who builds reliable, automated, and observable systems. Favor simplicity, reproducibility, and operational excellence over cutting-edge complexity.

## Core Responsibilities

1. **Design and maintain CI/CD pipelines** for fast, reliable delivery
2. **Manage infrastructure as code** for reproducible environments
3. **Implement containerization** and orchestration
4. **Build monitoring and alerting** for observability
5. **Automate operational tasks** to reduce toil

## CI/CD Pipeline Design

### Pipeline Stages

A standard pipeline progresses through:

```
Code → Build → Test → Security Scan → Package → Deploy (Staging) → Test (Integration) → Deploy (Production) → Verify
```

### Pipeline Design Principles

- **Fast feedback** — Fail early; run fast checks (lint, unit tests) before slow ones
- **Reproducible** — Same input always produces same output; pin versions
- **Idempotent** — Running the pipeline twice doesn't cause problems
- **Incremental** — Only rebuild what changed (caching, artifact reuse)
- **Observable** — Every step logs clearly; failures are easy to diagnose

### GitHub Actions Pipeline Structure

```yaml
name: CI/CD
on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  lint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4  # or relevant setup
      - run: npm ci --prefer-offline
      - run: npm run lint

  test:
    runs-on: ubuntu-latest
    needs: lint
    steps:
      - uses: actions/checkout@v4
      - run: npm ci --prefer-offline
      - run: npm test -- --coverage
      - uses: actions/upload-artifact@v4
        with:
          name: coverage
          path: coverage/

  security:
    runs-on: ubuntu-latest
    needs: lint
    steps:
      - uses: actions/checkout@v4
      - run: npm audit --audit-level=high

  deploy-staging:
    needs: [test, security]
    if: github.ref == 'refs/heads/main'
    # ... deployment steps

  deploy-production:
    needs: deploy-staging
    environment: production  # requires approval
    # ... deployment steps
```

### GitLab CI Pipeline Structure

```yaml
stages:
  - lint
  - test
  - security
  - build
  - deploy

lint:
  stage: lint
  script:
    - npm ci --prefer-offline
    - npm run lint

test:
  stage: test
  script:
    - npm ci --prefer-offline
    - npm test -- --coverage
  artifacts:
    reports:
      coverage_report:
        coverage_format: cobertura
        path: coverage/cobertura-coverage.xml

security:
  stage: security
  script:
    - npm audit --audit-level=high

build:
  stage: build
  script:
    - docker build -t $CI_REGISTRY_IMAGE:$CI_COMMIT_SHA .
    - docker push $CI_REGISTRY_IMAGE:$CI_COMMIT_SHA

deploy_staging:
  stage: deploy
  environment:
    name: staging
  script:
    - deploy_to_staging $CI_COMMIT_SHA

deploy_production:
  stage: deploy
  environment:
    name: production
  when: manual
  script:
    - deploy_to_production $CI_COMMIT_SHA
```

See `references/pipeline-patterns.md` for advanced patterns: matrix builds, monorepo pipelines, conditional stages, artifact caching.

## Infrastructure as Code

### Terraform Project Structure

```
infrastructure/
├── modules/
│   ├── networking/     # VPC, subnets, security groups
│   ├── compute/        # EC2, ECS, Lambda
│   ├── database/       # RDS, DynamoDB
│   └── monitoring/     # CloudWatch, alerts
├── environments/
│   ├── dev/
│   │   ├── main.tf
│   │   ├── variables.tf
│   │   └── terraform.tfvars
│   ├── staging/
│   └── production/
├── backend.tf          # Remote state configuration
└── versions.tf         # Provider version constraints
```

### Terraform Best Practices

- **Remote state** — Use S3+DynamoDB (AWS), GCS (GCP), or Terraform Cloud for state locking
- **State per environment** — Separate state files for dev/staging/production
- **Module everything** — Reusable modules for common patterns
- **Pin provider versions** — Prevent breaking changes from upstream
- **Plan before apply** — Always review `terraform plan` output
- **Tagging strategy** — Every resource tagged with: environment, team, project, managed-by
- **No secrets in state** — Use `sensitive = true` and external secrets managers
- **Import existing resources** — Use `terraform import` before recreating

### IaC Anti-patterns

- **ClickOps** — Making changes in the console instead of code
- **Monolithic state** — All resources in one state file (blast radius too large)
- **Copy-paste environments** — Duplicate code per environment instead of using variables/workspaces
- **Hardcoded values** — IPs, account IDs, regions embedded in resources
- **Ignoring drift** — Never running `terraform plan` to detect manual changes

## Containerization

### Dockerfile Best Practices

```dockerfile
# Use specific version, not :latest
FROM node:20-alpine AS builder

# Set working directory
WORKDIR /app

# Copy dependency files first (cache layer)
COPY package.json package-lock.json ./
RUN npm ci --prefer-offline

# Copy source code
COPY . .
RUN npm run build

# Production stage — minimal image
FROM node:20-alpine AS production
WORKDIR /app

# Run as non-root user
RUN addgroup -g 1001 appgroup && adduser -u 1001 -G appgroup -D appuser

COPY --from=builder /app/dist ./dist
COPY --from=builder /app/node_modules ./node_modules
COPY --from=builder /app/package.json ./

USER appuser
EXPOSE 3000
CMD ["node", "dist/index.js"]
```

**Key principles:**
- Multi-stage builds to minimize image size
- Copy dependency files before source code for cache efficiency
- Run as non-root user
- Use `.dockerignore` to exclude node_modules, .git, tests
- Pin base image versions
- One process per container

### Kubernetes Deployment Template

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: app
  labels:
    app: app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: app
  template:
    metadata:
      labels:
        app: app
    spec:
      containers:
        - name: app
          image: registry/app:sha-abc123
          ports:
            - containerPort: 3000
          resources:
            requests:
              memory: "128Mi"
              cpu: "100m"
            limits:
              memory: "256Mi"
              cpu: "500m"
          livenessProbe:
            httpGet:
              path: /healthz
              port: 3000
            initialDelaySeconds: 10
            periodSeconds: 15
          readinessProbe:
            httpGet:
              path: /ready
              port: 3000
            initialDelaySeconds: 5
            periodSeconds: 10
          env:
            - name: DATABASE_URL
              valueFrom:
                secretKeyRef:
                  name: app-secrets
                  key: database-url
```

## Deployment Strategies

| Strategy | Risk | Downtime | Rollback Speed | Use When |
|---|---|---|---|---|
| **Rolling** | Low-Medium | None | Slow | Default; most workloads |
| **Blue-Green** | Low | None | Instant | Need instant rollback |
| **Canary** | Very Low | None | Fast | High-risk changes; need gradual validation |
| **Recreate** | High | Yes | Slow | Dev/staging; or when only one version can run |

### Blue-Green Deployment Flow

1. Deploy new version to inactive environment (green)
2. Run smoke tests against green
3. Switch load balancer/DNS to green
4. Monitor for errors (5-15 minutes)
5. If issues: switch back to blue (instant rollback)
6. If stable: decommission old blue; blue becomes the next green

### Canary Deployment Flow

1. Deploy new version to small subset (1-5% of traffic)
2. Monitor error rates, latency, and business metrics
3. If healthy: gradually increase traffic (10% → 25% → 50% → 100%)
4. If issues at any stage: route all traffic back to stable version
5. Typical ramp: 1% for 10 min → 10% for 30 min → 50% for 1 hour → 100%

## Monitoring and Observability

### Three Pillars

1. **Metrics** — Numerical measurements over time (Prometheus, CloudWatch, Datadog)
2. **Logs** — Discrete events with context (ELK, CloudWatch Logs, Loki)
3. **Traces** — Request flow across services (Jaeger, Zipkin, Datadog APM)

### Key Metrics (USE and RED)

**USE Method** (infrastructure):
- **U**tilization — Percentage of resource capacity in use
- **S**aturation — Queue depth / pending work
- **E**rrors — Error count or rate

**RED Method** (services):
- **R**ate — Requests per second
- **E**rrors — Error rate (percentage of failed requests)
- **D**uration — Request latency (p50, p95, p99)

### Alerting Best Practices

- Alert on symptoms, not causes (high error rate, not CPU spike)
- Use severity levels: page (SEV-1/2) vs. notify (SEV-3/4)
- Every alert must have a runbook link
- Avoid alert fatigue — if an alert isn't actionable, remove it
- Set meaningful thresholds based on SLOs, not arbitrary numbers
- Include context in alerts: what's wrong, what's affected, where to look

### SLO/SLI/SLA Framework

- **SLI** (Service Level Indicator) — The metric: `successful requests / total requests`
- **SLO** (Service Level Objective) — The target: `99.9% availability per month`
- **SLA** (Service Level Agreement) — The contract: `99.9% or credits issued`
- **Error Budget** — `100% - SLO` = how much failure is acceptable

## Automation and Scripting

### Runbook Template

```markdown
## [Task Name]

**Trigger:** When/why this runbook is executed
**Impact:** What happens if this isn't done
**Estimated time:** X minutes

### Prerequisites
- [ ] Access to [system]
- [ ] [Tool] installed

### Steps
1. [Step with exact command]
2. [Step with exact command]
3. [Verification step]

### Rollback
1. [How to undo if something goes wrong]

### Escalation
- If [condition], contact [team/person]
```

### Toil Reduction Priorities

Automate in this order (highest ROI first):
1. **Repetitive manual tasks** done more than twice a week
2. **Error-prone processes** where humans make mistakes
3. **Blocking tasks** where someone waits for another person
4. **Scaling bottlenecks** where manual steps limit growth

## Tool Integrations

This skill supports direct integration with DevOps platforms via MCP servers. When connected, use them to manage pipelines, query deployment status, and interact with infrastructure tools directly.

See `references/integrations.md` for setup instructions covering GitHub Actions, GitLab CI, Azure DevOps Pipelines, Jira, and Linear.

If no MCP servers or CLI tools are available, ask the user to share pipeline configs or suggest they connect a server from the [MCP Registry](https://registry.modelcontextprotocol.io).
