---
name: "senior-devops"
description: Comprehensive DevOps skill for CI/CD, infrastructure automation, containerization, and cloud platforms (AWS, GCP, Azure). Includes pipeline setup, infrastructure as code, deployment automation, and monitoring. Use when setting up pipelines, deploying applications, managing infrastructure, implementing monitoring, or optimizing deployment processes.
---

# Senior Devops

Complete toolkit for senior devops with modern tools and best practices.

## Quick Start

### Main Capabilities

This skill provides three core capabilities through automated scripts:

```bash
# Script 1: Pipeline Generator — scaffolds CI/CD pipelines for GitHub Actions or CircleCI
python scripts/pipeline_generator.py ./app --platform=github --stages=build,test,deploy

# Script 2: Terraform Scaffolder — generates and validates IaC modules for AWS/GCP/Azure
python scripts/terraform_scaffolder.py ./infra --provider=aws --module=ecs-service --verbose

# Script 3: Deployment Manager — generates deployment manifests + runbooks with rollback support
python3 scripts/deployment_manager.py deploy --env=staging --image=app:1.2.3 --strategy=blue-green --verbose --json
```

## Core Capabilities

### 1. Pipeline Generator

Scaffolds CI/CD pipeline configurations for GitHub Actions or CircleCI, with stages for build, test, security scan, and deploy.

**Example — GitHub Actions workflow:**
```yaml
# .github/workflows/ci.yml
name: CI/CD Pipeline
on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]

jobs:
  build-and-test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Set up Node.js
        uses: actions/setup-node@v4
        with:
          node-version: '20'
          cache: 'npm'
      - run: npm ci
      - run: npm run lint
      - run: npm test -- --coverage
      - name: Upload coverage
        uses: codecov/codecov-action@v4

  build-docker:
    needs: build-and-test
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Build and push image
        uses: docker/build-push-action@v5
        with:
          push: ${{ github.ref == 'refs/heads/main' }}
          tags: ghcr.io/${{ github.repository }}:${{ github.sha }}

  deploy:
    needs: build-docker
    if: github.ref == 'refs/heads/main'
    runs-on: ubuntu-latest
    steps:
      - name: Deploy to ECS
        run: |
          aws ecs update-service \
            --cluster production \
            --service app-service \
            --force-new-deployment
```

**Usage:**
```bash
python scripts/pipeline_generator.py <project-path> --platform=github|circleci --stages=build,test,deploy
```

### 2. Terraform Scaffolder

Generates, validates, and plans Terraform modules. Enforces consistent module structure and runs `terraform validate` + `terraform plan` before any apply.

**Example — AWS ECS service module:**
```hcl
# modules/ecs-service/main.tf
resource "aws_ecs_task_definition" "app" {
  family                   = var.service_name
  requires_compatibilities = ["FARGATE"]
  network_mode             = "awsvpc"
  cpu                      = var.cpu
  memory                   = var.memory

  container_definitions = jsonencode([{
    name      = var.service_name
    image     = var.container_image
    essential = true
    portMappings = [{
      containerPort = var.container_port
      protocol      = "tcp"
    }]
    environment = [for k, v in var.env_vars : { name = k, value = v }]
    logConfiguration = {
      logDriver = "awslogs"
      options = {
        awslogs-group         = "/ecs/${var.service_name}"
        awslogs-region        = var.aws_region
        awslogs-stream-prefix = "ecs"
      }
    }
  }])
}

resource "aws_ecs_service" "app" {
  name            = var.service_name
  cluster         = var.cluster_id
  task_definition = aws_ecs_task_definition.app.arn
  desired_count   = var.desired_count
  launch_type     = "FARGATE"

  network_configuration {
    subnets          = var.private_subnet_ids
    security_groups  = [aws_security_group.app.id]
    assign_public_ip = false
  }

  load_balancer {
    target_group_arn = aws_lb_target_group.app.arn
    container_name   = var.service_name
    container_port   = var.container_port
  }
}
```

**Usage:**
```bash
python scripts/terraform_scaffolder.py <target-path> --provider=aws|gcp|azure --module=ecs-service|gke-deployment|aks-service [--verbose]
```

### 3. Deployment Manager

Generates Kubernetes deployment manifests and ordered kubectl runbooks for blue/green or rolling strategies, with health-check gates before traffic switches and rollback runbooks. The tool writes manifests and prints the commands — it never applies them to a cluster itself, so every change gets a human review.

**Example — Kubernetes blue/green deployment (blue-slot specific elements):**
```yaml
# k8s/deployment-blue.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: app-blue
  labels:
    app: myapp
    slot: blue      # slot label distinguishes blue from green
spec:
  replicas: 3
  selector:
    matchLabels:
      app: myapp
      slot: blue
  template:
    metadata:
      labels:
        app: myapp
        slot: blue
    spec:
      containers:
        - name: app
          image: ghcr.io/org/app:1.2.3
          readinessProbe:       # gate: pod must pass before traffic switches
            httpGet:
              path: /healthz
              port: 8080
            initialDelaySeconds: 10
            periodSeconds: 5
          resources:
            requests:
              cpu: "250m"
              memory: "256Mi"
            limits:
              cpu: "500m"
              memory: "512Mi"
```

**Usage:**
```bash
python scripts/deployment_manager.py deploy \
  --env=staging|production \
  --image=app:1.2.3 \
  --strategy=blue-green|rolling \
  --health-check-url=https://app.example.com/healthz

python scripts/deployment_manager.py rollback --env=production --to-version=1.2.2
python scripts/deployment_manager.py --analyze --env=production   # audit current state
```

## Resources

- Pattern Reference: `references/cicd_pipeline_guide.md` — detailed CI/CD patterns, best practices, anti-patterns
- Workflow Guide: `references/infrastructure_as_code.md` — IaC step-by-step processes, optimization, troubleshooting
- Technical Guide: `references/deployment_strategies.md` — deployment strategy configs, security considerations, scalability
- Tool Scripts: `scripts/` directory

## Development Workflow

### 1. Infrastructure Changes (Terraform)

```bash
# Scaffold or update module
python scripts/terraform_scaffolder.py ./infra --provider=aws --module=ecs-service --verbose

# Validate and plan — review diff before applying
terraform -chdir=infra init
terraform -chdir=infra validate
terraform -chdir=infra plan -out=tfplan

# Apply only after plan review
terraform -chdir=infra apply tfplan

# Verify resources are healthy
aws ecs describe-services --cluster production --services app-service \
  --query 'services[0].{Status:status,Running:runningCount,Desired:desiredCount}'
```

### 2. Application Deployment

```bash
# Generate or update pipeline config
python scripts/pipeline_generator.py . --platform=github --stages=build,test,security,deploy

# Build and tag image
docker build -t ghcr.io/org/app:$(git rev-parse --short HEAD) .
docker push ghcr.io/org/app:$(git rev-parse --short HEAD)

# Deploy with health-check gate
python scripts/deployment_manager.py deploy \
  --env=production \
  --image=app:$(git rev-parse --short HEAD) \
  --strategy=blue-green \
  --health-check-url=https://app.example.com/healthz

# Verify pods are running
kubectl get pods -n production -l app=myapp
kubectl rollout status deployment/app-blue -n production

# Switch traffic after verification
kubectl patch service app-svc -n production \
  -p '{"spec":{"selector":{"slot":"blue"}}}'
```

### 3. Rollback Procedure

```bash
# Immediate rollback via deployment manager
python scripts/deployment_manager.py rollback --env=production --to-version=1.2.2

# Or via kubectl
kubectl rollout undo deployment/app -n production
kubectl rollout status deployment/app -n production

# Verify rollback succeeded
kubectl get pods -n production -l app=myapp
curl -sf https://app.example.com/healthz || echo "ROLLBACK FAILED — escalate"
```

## Multi-Cloud Cross-References

Use these companion skills for cloud-specific deep dives:

| Skill | Cloud | Use When |
|-------|-------|----------|
| **aws-solution-architect** | AWS | ECS/EKS, Lambda, VPC design, cost optimization |
| **azure-cloud-architect** | Azure | AKS, App Service, Virtual Networks, Azure DevOps |
| **gcp-cloud-architect** | GCP | GKE, Cloud Run, VPC, Cloud Build *(coming soon)* |

**Multi-cloud vs single-cloud decision:**
- **Single-cloud** (default) — lower operational complexity, deeper managed-service integration, better cost leverage with committed-use discounts
- **Multi-cloud** — required when mandated by compliance/data residency, acquiring companies on different clouds, or needing best-of-breed services across providers (e.g., AWS for compute + GCP for ML)
- **Hybrid** — on-prem + cloud; use when regulated workloads must stay on-prem while burst/non-sensitive workloads run in the cloud

> Start single-cloud. Add a second cloud only when there is a concrete business or compliance driver — not for theoretical redundancy.

---

## Cloud-Agnostic IaC

### Terraform / OpenTofu (Default Choice)

Terraform (or its open-source fork OpenTofu) is the recommended IaC tool for most teams:
- Single language (HCL) across AWS, Azure, GCP, and 3,000+ providers
- State management with remote backends (S3, GCS, Azure Blob)
- Plan-before-apply workflow prevents drift surprises
- Cross-reference **terraform-patterns** for module structure, state isolation, and CI/CD integration

### Pulumi (Programming Language IaC)

Choose Pulumi when the team strongly prefers TypeScript, Python, Go, or C# over HCL:
- Full programming language — loops, conditionals, unit tests native
- Same cloud provider coverage as Terraform
- Easier onboarding for dev teams that resist learning HCL

### When to Use Cloud-Native IaC

| Tool | Use When |
|------|----------|
| **CloudFormation** | AWS-only shop; need native AWS support (StackSets, Service Catalog) |
| **Bicep** | Azure-only shop; simpler syntax than ARM templates |
| **Cloud Deployment Manager** | GCP-only; rare — most GCP teams prefer Terraform |

> **Rule of thumb:** Use Terraform/OpenTofu unless you are 100% committed to a single cloud AND the cloud-native tool offers a feature Terraform cannot replicate (e.g., AWS Service Catalog integration).

---

## Troubleshooting

Check the comprehensive troubleshooting section in `references/deployment_strategies.md`.
