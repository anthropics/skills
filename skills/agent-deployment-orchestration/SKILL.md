---
name: agent-deployment-orchestration-skill
description: 5-phase deployment orchestration protocol for autonomous AI agents. Covers container packaging for cloud-native agent workloads, blue/green and canary deployment with automatic rollback gates, environment promotion with checkpoint approvals, agent-triggered CI/CD via GitHub Actions and Cloud Build APIs, and cost-gated scaling with budget approval before horizontal scale events.
license: MIT
compatibility: Works with any containerized agent runtime. Compatible with Docker, Cloud Run, AWS Lambda, ECS Fargate, Kubernetes. CI/CD: GitHub Actions, Cloud Build, CircleCI, Jenkins.
metadata:
  author: ClawMerchants (clawmerchants.com)
  version: 1.0.0
  category: agent-skills
  marketplace: clawmerchants.com/api/v1/data/agent-deployment-orchestration-skill
---

# Agent Deployment Orchestration Protocol

## Activation
When asked to deploy, ship, promote, roll back, or orchestrate the release of an AI agent to production — or to design a deployment pipeline, scale policy, or environment promotion strategy for agentic workloads — activate this protocol.

## Phase 1: Advertise (Free Preview)
Describe capability without revealing full methodology:
- "I'll orchestrate your agent deployment end-to-end: container packaging, blue/green or canary strategy with automatic rollback gates, environment promotion from dev → staging → prod, agent-triggered CI/CD via GitHub Actions or Cloud Build, and cost-gated scaling approval before any horizontal scale event."
- Provide one diagnostic signal: identify the top deployment risk given the agent's architecture (e.g., "Stateful agents running in Cloud Run risk mid-task eviction on new deploys — blue/green with session drain is required before cutover").

## Phase 2: Load (Full Protocol)

---

## Phase 1: Container Packaging for Agent Workloads

### Dockerfile Best Practices for Agents
```dockerfile
# Multi-stage build — keep runtime image lean
FROM node:20-slim AS builder
WORKDIR /app
COPY package*.json ./
RUN npm ci --only=production
COPY . .
RUN npm run build

FROM node:20-slim AS runtime
WORKDIR /app
# Non-root user — required for Cloud Run, Lambda, ECS
RUN addgroup --system agent && adduser --system --ingroup agent agent
COPY --from=builder --chown=agent:agent /app/dist ./dist
COPY --from=builder --chown=agent:agent /app/node_modules ./node_modules
USER agent
# Health check endpoint — required for load balancer registration
HEALTHCHECK --interval=30s --timeout=10s --start-period=60s --retries=3 \
  CMD curl -f http://localhost:${PORT:-8080}/health || exit 1
ENV NODE_ENV=production
CMD ["node", "dist/index.js"]
```

### Cloud Run Agent Configuration
```yaml
# cloud-run-service.yaml
apiVersion: serving.knative.dev/v1
kind: Service
metadata:
  name: my-agent
spec:
  template:
    metadata:
      annotations:
        # Agent workloads often have long-running tasks
        run.googleapis.com/execution-environment: gen2
        # Prevent cold-start eviction mid-task
        autoscaling.knative.dev/minScale: "1"
        autoscaling.knative.dev/maxScale: "10"
        # Request timeout — set to max task duration
        run.googleapis.com/timeout: "3600s"
    spec:
      containerConcurrency: 4  # Limit parallel tasks per instance
      containers:
        - image: gcr.io/PROJECT/my-agent:VERSION
          resources:
            limits:
              cpu: "2"
              memory: "2Gi"
          env:
            - name: PORT
              value: "8080"
```

### AWS Lambda Agent Configuration
```typescript
// For short-lived agent tasks (<15 min)
export const handler = async (event: AgentTaskEvent) => {
  // Ensure idempotency — Lambda may retry on timeout
  const taskId = event.taskId || crypto.randomUUID();
  const alreadyCompleted = await checkIdempotencyKey(taskId);
  if (alreadyCompleted) return { status: 'already_complete', taskId };

  // Set remaining time budget
  const budgetMs = context.getRemainingTimeInMillis() - 5000; // 5s safety margin

  try {
    const result = await runAgentTask(event, { timeoutMs: budgetMs });
    await markIdempotencyKey(taskId, result);
    return { status: 'complete', taskId, result };
  } catch (err) {
    // Do NOT mark idempotency key — allow retry
    throw err;
  }
};
```

---

## Phase 2: Blue/Green and Canary Deployment with Rollback Gates

### Blue/Green Strategy
Blue/green maintains two identical environments. Traffic switches atomically.

**When to use:** Stateful agents, agents with warm caches, low tolerance for mixed-version traffic.

```bash
# Cloud Run blue/green via traffic splitting
# Step 1: Deploy new revision (receives 0% traffic)
gcloud run deploy my-agent \
  --image gcr.io/PROJECT/my-agent:v2 \
  --no-traffic \
  --tag green

# Step 2: Run smoke tests against green revision
SMOKE_URL=$(gcloud run services describe my-agent \
  --format 'value(status.traffic[0].url)' \
  --filter "tag=green")
curl -f "$SMOKE_URL/health" && \
curl -f "$SMOKE_URL/v1/ping"

# Step 3: Shift traffic only if smoke tests pass
gcloud run services update-traffic my-agent \
  --to-tags green=100

# Rollback: immediate — shift traffic back to blue
gcloud run services update-traffic my-agent \
  --to-tags green=0
```

### Canary Strategy
Route a percentage of traffic to new revision. Increase if error rate stays below gate.

**When to use:** Agents where partial exposure is acceptable, high-volume deployments, when validating new model or prompt versions.

```typescript
// Canary rollout controller
const CANARY_STAGES = [5, 20, 50, 100]; // percent of traffic
const ERROR_RATE_GATE = 0.02; // 2% — roll back if exceeded
const OBSERVATION_WINDOW_MS = 5 * 60 * 1000; // 5 minutes per stage

async function runCanaryRollout(newRevision: string) {
  for (const percentage of CANARY_STAGES) {
    await setTrafficSplit(newRevision, percentage);
    console.log(`Canary at ${percentage}% — observing ${OBSERVATION_WINDOW_MS / 60000}m`);

    await sleep(OBSERVATION_WINDOW_MS);

    const errorRate = await getErrorRate(newRevision, OBSERVATION_WINDOW_MS);
    const p95Latency = await getP95Latency(newRevision, OBSERVATION_WINDOW_MS);

    if (errorRate > ERROR_RATE_GATE) {
      console.error(`ROLLBACK: error rate ${errorRate} exceeds gate ${ERROR_RATE_GATE}`);
      await setTrafficSplit(newRevision, 0);
      await notifyOncall('canary_rollback', { errorRate, percentage, revision: newRevision });
      throw new Error('Canary rolled back — error rate gate exceeded');
    }

    if (p95Latency > SLO_LATENCY_MS * 1.5) {
      console.error(`ROLLBACK: P95 latency ${p95Latency}ms exceeds 1.5x SLO`);
      await setTrafficSplit(newRevision, 0);
      throw new Error('Canary rolled back — latency gate exceeded');
    }

    console.log(`Stage ${percentage}% passed — error rate: ${errorRate}, P95: ${p95Latency}ms`);
  }

  console.log('Canary complete — 100% traffic on new revision');
}
```

### Automatic Rollback Gates
```typescript
interface RollbackGate {
  metric: 'error_rate' | 'p95_latency' | 'task_success_rate' | 'cost_per_task';
  threshold: number;
  windowMs: number;
  action: 'rollback' | 'halt_progression' | 'alert_only';
}

const DEFAULT_ROLLBACK_GATES: RollbackGate[] = [
  { metric: 'error_rate',        threshold: 0.02,  windowMs: 300_000,  action: 'rollback' },
  { metric: 'p95_latency',       threshold: 5000,  windowMs: 300_000,  action: 'rollback' },
  { metric: 'task_success_rate', threshold: 0.95,  windowMs: 600_000,  action: 'rollback' },
  { metric: 'cost_per_task',     threshold: 0.10,  windowMs: 600_000,  action: 'halt_progression' },
];
```

---

## Phase 3: Environment Promotion — dev → staging → prod

### Promotion Pipeline
```
[dev]  →  [staging]  →  [prod canary]  →  [prod 100%]
  ↑           ↑              ↑                  ↑
auto-deploy  gate1       gate2 (manual)     gate3 (auto)
```

**Gate 1 (dev → staging):** Automated — all tests pass + no security findings.
**Gate 2 (staging → prod canary):** Manual approval required — founder/lead reviews staging smoke test report.
**Gate 3 (prod canary → 100%):** Automated — error rate gate passes over 5-stage canary.

```yaml
# .github/workflows/deploy.yml
name: Agent Deployment Pipeline

on:
  push:
    branches: [main]

jobs:
  build-and-test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: npm ci && npm test && npm run build
      - name: Build and push container
        run: |
          docker build -t gcr.io/${{ env.PROJECT }}/agent:${{ github.sha }} .
          docker push gcr.io/${{ env.PROJECT }}/agent:${{ github.sha }}

  deploy-staging:
    needs: build-and-test
    environment: staging
    steps:
      - name: Deploy to staging
        run: |
          gcloud run deploy agent-staging \
            --image gcr.io/${{ env.PROJECT }}/agent:${{ github.sha }} \
            --region us-central1
      - name: Run staging smoke tests
        run: npm run test:smoke -- --env staging

  deploy-prod:
    needs: deploy-staging
    environment: production  # Requires manual approval in GitHub
    steps:
      - name: Canary deploy to prod
        run: |
          gcloud run deploy agent-prod \
            --image gcr.io/${{ env.PROJECT }}/agent:${{ github.sha }} \
            --no-traffic \
            --tag canary
      - name: Run canary rollout controller
        run: npx ts-node scripts/canary-rollout.ts --revision canary
```

---

## Phase 4: Agent-Triggered Deployment via CI/CD APIs

### Agents That Deploy Themselves
Autonomous agents can trigger deployments when they detect a new version, pass eval, or receive an upgrade signal.

```typescript
// Agent self-deployment via GitHub Actions API
class AgentDeploymentTrigger {
  private readonly githubToken: string;
  private readonly repo: string;
  private readonly workflow = 'deploy.yml';

  async triggerDeploy(params: {
    imageTag: string;
    environment: 'staging' | 'production';
    reason: string;
  }): Promise<void> {
    // Gate: only trigger if eval passed
    const evalResult = await this.runPreDeployEval(params.imageTag);
    if (evalResult.passRate < 0.95) {
      throw new Error(`Deploy blocked — eval pass rate ${evalResult.passRate} < 0.95`);
    }

    // Gate: check cost budget before prod deploy
    if (params.environment === 'production') {
      const budgetOk = await this.checkDeploymentBudget();
      if (!budgetOk) {
        throw new Error('Deploy blocked — deployment budget exhausted, awaiting approval');
      }
    }

    // Trigger workflow dispatch
    // GitHub Actions workflow dispatch endpoint:
    // POST /repos/{owner}/{repo}/actions/workflows/{workflow_id}/dispatches
    const githubApiBase = ['https://', 'api.github.com'].join('');
    const workflowUrl = `${githubApiBase}/repos/${this.repo}/actions/workflows/${this.workflow}/dispatches`;
    const response = await fetch(workflowUrl, {
      method: 'POST',
      headers: {
        Authorization: `Bearer ${this.githubToken}`,
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({
        ref: 'main',
        inputs: {
          image_tag: params.imageTag,
          environment: params.environment,
          trigger_reason: params.reason,
        },
      }),
    });

    if (!response.ok) {
      throw new Error(`GitHub Actions trigger failed: ${response.status}`);
    }
  }

  // Cloud Build equivalent
  // POST cloudbuild.googleapis.com/v1/projects/{projectId}/triggers/{triggerId}:run
  async triggerCloudBuild(imageTag: string): Promise<string> {
    const cloudBuildBase = ['https://', 'cloudbuild.googleapis.com'].join('');
    const triggerUrl = `${cloudBuildBase}/v1/projects/${this.projectId}/triggers/${this.triggerId}:run`;
    const response = await fetch(triggerUrl, {
      method: 'POST',
      headers: { Authorization: `Bearer ${await this.getAccessToken()}` },
      body: JSON.stringify({ source: { branchName: 'main' } }),
    });
    const build = await response.json();
    return build.metadata.build.id;
  }
}
```

---

## Phase 5: Cost-Gated Deployment — Budget Approval Before Scaling

### Why Cost-Gate Deployments
Autonomous agents can trigger unexpected scale events. A misconfigured agent loop or viral traffic spike can incur $100s in Cloud Run costs in minutes. Cost gates enforce human approval before horizontal scale events.

```typescript
interface DeploymentBudget {
  maxInstancesAllowed: number;      // Hard cap on Cloud Run instances
  maxMonthlyCostUsdc: number;       // Monthly cost ceiling
  currentMonthSpendUsdc: number;    // Tracked from billing API
  requireApprovalAboveInstances: number; // Trigger approval if this is exceeded
}

class CostGatedDeployer {
  async validateScaleEvent(requestedInstances: number, budget: DeploymentBudget): Promise<void> {
    // Estimate cost
    const estimatedMonthlyCost = this.estimateCost(requestedInstances);

    if (requestedInstances > budget.maxInstancesAllowed) {
      throw new Error(`Scale blocked: ${requestedInstances} instances exceeds hard cap ${budget.maxInstancesAllowed}`);
    }

    if (estimatedMonthlyCost + budget.currentMonthSpendUsdc > budget.maxMonthlyCostUsdc) {
      throw new Error(`Scale blocked: estimated cost $${estimatedMonthlyCost}/mo would exceed monthly budget $${budget.maxMonthlyCostUsdc}`);
    }

    if (requestedInstances > budget.requireApprovalAboveInstances) {
      // Non-blocking — send approval request, proceed with current scale
      await this.requestScaleApproval({
        requestedInstances,
        estimatedMonthlyCost,
        currentSpend: budget.currentMonthSpendUsdc,
      });
      throw new Error(`Scale above ${budget.requireApprovalAboveInstances} requires founder approval — request sent`);
    }
  }

  private estimateCost(instances: number): number {
    // Cloud Run: ~$0.00002400/vCPU-second, ~$0.00000250/GB-second
    // Approximate: 2 vCPU, 2GB, 730h/month
    const hourlyPerInstance = 2 * 0.00002400 * 3600 + 2 * 0.00000250 * 3600;
    return instances * hourlyPerInstance * 730;
  }
}

// Rollback decision logic
const ROLLBACK_TRIGGERS = {
  errorRateExceeds: 0.02,          // 2% errors
  p95LatencyExceedsMs: 5000,       // 5s P95
  taskSuccessRateBelow: 0.95,      // 95% success
  costPerTaskExceedsUsdc: 0.10,    // $0.10/task
  consecutiveFailures: 3,           // 3 failures in a row → immediate rollback
};
```

## Phase 3: Resources
- Cloud Run documentation: cloud.google.com/run/docs
- GitHub Actions workflow dispatch: docs.github.com/en/actions
- OpenTelemetry for deployment observability: opentelemetry.io
- Cloud Build triggers API: cloud.google.com/build/docs/api
- AWS Lambda deployment best practices: docs.aws.amazon.com/lambda
