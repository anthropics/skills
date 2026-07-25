---
name: "terraform-patterns"
description: "Terraform infrastructure-as-code agent skill and plugin for Claude Code, Codex, Gemini CLI, Cursor, OpenClaw. Covers module design patterns, state management strategies, provider configuration, security hardening, policy-as-code with Sentinel/OPA, and CI/CD plan/apply workflows. Use when: user wants to design Terraform modules, manage state backends, review Terraform security, implement multi-region deployments, or follow IaC best practices."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: engineering
  updated: 2026-03-15
---

# Terraform Patterns

> Predictable infrastructure. Secure state. Modules that compose. No drift.

Opinionated Terraform workflow that turns sprawling HCL into well-structured, secure, production-grade infrastructure code. Covers module design, state management, provider patterns, security hardening, and CI/CD integration.

Not a Terraform tutorial — a set of concrete decisions about how to write infrastructure code that doesn't break at 3 AM.

---

## Slash Commands

| Command | What it does |
|---------|-------------|
| `/terraform:review` | Analyze Terraform code for anti-patterns, security issues, and structure problems |
| `/terraform:module` | Design or refactor a Terraform module with proper inputs, outputs, and composition |
| `/terraform:security` | Audit Terraform code for security vulnerabilities, secrets exposure, and IAM misconfigurations |

---

## When This Skill Activates

Recognize these patterns from the user:

- "Review this Terraform code"
- "Design a Terraform module for..."
- "My Terraform state is..."
- "Set up remote state backend"
- "Multi-region Terraform deployment"
- "Terraform security review"
- "Module structure best practices"
- "Terraform CI/CD pipeline"
- Any request involving: `.tf` files, HCL, Terraform modules, state management, provider configuration, infrastructure-as-code

If the user has `.tf` files or wants to provision infrastructure with Terraform → this skill applies.

---

## Workflow

### `/terraform:review` — Terraform Code Review

1. **Analyze current state**
   - Read all `.tf` files in the target directory
   - Identify module structure (flat vs nested)
   - Count resources, data sources, variables, outputs
   - Check naming conventions

2. **Apply review checklist**

   ```
   MODULE STRUCTURE
   ├── Variables have descriptions and type constraints
   ├── Outputs expose only what consumers need
   ├── Resources use consistent naming: {provider}_{type}_{purpose}
   ├── Locals used for computed values and DRY expressions
   └── No hardcoded values — everything parameterized or in locals

   STATE & BACKEND
   ├── Remote backend configured (S3, GCS, Azure Blob, Terraform Cloud)
   ├── State locking enabled (DynamoDB for S3, native for others)
   ├── State encryption at rest enabled
   ├── No secrets stored in state (or state access is restricted)
   └── Workspaces or directory isolation for environments

   PROVIDERS
   ├── Version constraints use pessimistic operator: ~> 5.0
   ├── Required providers block in terraform {} block
   ├── Provider aliases for multi-region or multi-account
   └── No provider configuration in child modules

   SECURITY
   ├── No hardcoded secrets, keys, or passwords
   ├── IAM follows least-privilege principle
   ├── Encryption enabled for storage, databases, secrets
   ├── Security groups are not overly permissive (no 0.0.0.0/0 ingress on sensitive ports)
   └── Sensitive variables marked with sensitive = true
   ```

3. **Generate report**
   ```bash
   python3 scripts/tf_module_analyzer.py ./terraform
   ```

4. **Run security scan**
   ```bash
   python3 scripts/tf_security_scanner.py ./terraform
   ```

### `/terraform:module` — Module Design

1. **Identify module scope**
   - Single responsibility: one module = one logical grouping
   - Determine inputs (variables), outputs, and resource boundaries
   - Decide: flat module (single directory) vs nested (calling child modules)

2. **Apply module design checklist**

   ```
   STRUCTURE
   ├── main.tf        — Primary resources
   ├── variables.tf   — All input variables with descriptions and types
   ├── outputs.tf     — All outputs with descriptions
   ├── versions.tf    — terraform {} block with required_providers
   ├── locals.tf      — Computed values and naming conventions
   ├── data.tf        — Data sources (if any)
   └── README.md      — Usage examples and variable documentation

   VARIABLES
   ├── Every variable has: description, type, validation (where applicable)
   ├── Sensitive values marked: sensitive = true
   ├── Defaults provided for optional settings
   ├── Use object types for related settings: variable "config" { type = object({...}) }
   └── Validate with: validation { condition = ... }

   OUTPUTS
   ├── Output IDs, ARNs, endpoints — things consumers need
   ├── Include description on every output
   ├── Mark sensitive outputs: sensitive = true
   └── Don't output entire resources — only specific attributes

   COMPOSITION
   ├── Root module calls child modules
   ├── Child modules never call other child modules
   ├── Pass values explicitly — no hidden data source lookups in child modules
   ├── Provider configuration only in root module
   └── Use module "name" { source = "./modules/name" }
   ```

3. **Generate module scaffold**
   - Output file structure with boilerplate
   - Include variable validation blocks
   - Add lifecycle rules where appropriate

### `/terraform:security` — Security Audit

1. **Code-level audit**

   | Check | Severity | Fix |
   |-------|----------|-----|
   | Hardcoded secrets in `.tf` files | Critical | Use variables with sensitive = true or vault |
   | IAM policy with `*` actions | Critical | Scope to specific actions and resources |
   | Security group with 0.0.0.0/0 on port 22/3389 | Critical | Restrict to known CIDR blocks or use SSM/bastion |
   | S3 bucket without encryption | High | Add `server_side_encryption_configuration` block |
   | S3 bucket with public access | High | Add `aws_s3_bucket_public_access_block` |
   | RDS without encryption | High | Set `storage_encrypted = true` |
   | RDS publicly accessible | High | Set `publicly_accessible = false` |
   | CloudTrail not enabled | Medium | Add `aws_cloudtrail` resource |
   | Missing `prevent_destroy` on stateful resources | Medium | Add `lifecycle { prevent_destroy = true }` |
   | Variables without `sensitive = true` for secrets | Medium | Add `sensitive = true` to secret variables |

2. **State security audit**

   | Check | Severity | Fix |
   |-------|----------|-----|
   | Local state file | Critical | Migrate to remote backend with encryption |
   | Remote state without encryption | High | Enable encryption on backend (SSE-S3, KMS) |
   | No state locking | High | Enable DynamoDB for S3, native for TF Cloud |
   | State accessible to all team members | Medium | Restrict via IAM policies or TF Cloud teams |

3. **Generate security report**
   ```bash
   python3 scripts/tf_security_scanner.py ./terraform
   python3 scripts/tf_security_scanner.py ./terraform --output json
   ```

---

## Tooling

### `scripts/tf_module_analyzer.py`

CLI utility for analyzing Terraform directory structure and module quality.

**Features:**
- Resource and data source counting
- Variable and output analysis (missing descriptions, types, validation)
- Naming convention checks
- Module composition detection
- File structure validation
- JSON and text output

**Usage:**
```bash
# Analyze a Terraform directory
python3 scripts/tf_module_analyzer.py ./terraform

# JSON output
python3 scripts/tf_module_analyzer.py ./terraform --output json

# Analyze a specific module
python3 scripts/tf_module_analyzer.py ./modules/vpc
```

### `scripts/tf_security_scanner.py`

CLI utility for scanning `.tf` files for common security issues.

**Features:**
- Hardcoded secret detection (AWS keys, passwords, tokens)
- Overly permissive IAM policy detection
- Open security group detection (0.0.0.0/0 on sensitive ports)
- Missing encryption checks (S3, RDS, EBS)
- Public access detection (S3, RDS, EC2)
- Sensitive variable audit
- JSON and text output

**Usage:**
```bash
# Scan a Terraform directory
python3 scripts/tf_security_scanner.py ./terraform

# JSON output
python3 scripts/tf_security_scanner.py ./terraform --output json

# Strict mode (elevate warnings)
python3 scripts/tf_security_scanner.py ./terraform --strict
```

---

## Module Design Patterns

### Pattern 1: Flat Module (Small/Medium Projects)

```
infrastructure/
├── main.tf          # All resources
├── variables.tf     # All inputs
├── outputs.tf       # All outputs
├── versions.tf      # Provider requirements
├── terraform.tfvars # Environment values (not committed)
└── backend.tf       # Remote state configuration
```

Best for: Single application, < 20 resources, one team owns everything.

### Pattern 2: Nested Modules (Medium/Large Projects)

```
infrastructure/
├── environments/
│   ├── dev/
│   │   ├── main.tf          # Calls modules with dev params
│   │   ├── backend.tf       # Dev state backend
│   │   └── terraform.tfvars
│   ├── staging/
│   │   └── ...
│   └── prod/
│       └── ...
├── modules/
│   ├── networking/
│   │   ├── main.tf
│   │   ├── variables.tf
│   │   └── outputs.tf
│   ├── compute/
│   │   └── ...
│   └── database/
│       └── ...
└── versions.tf
```

Best for: Multiple environments, shared infrastructure patterns, team collaboration.

### Pattern 3: Mono-Repo with Terragrunt

```
infrastructure/
├── terragrunt.hcl           # Root config
├── modules/                  # Reusable modules
│   ├── vpc/
│   ├── eks/
│   └── rds/
├── dev/
│   ├── terragrunt.hcl       # Dev overrides
│   ├── vpc/
│   │   └── terragrunt.hcl   # Module invocation
│   └── eks/
│       └── terragrunt.hcl
└── prod/
    ├── terragrunt.hcl
    └── ...
```

Best for: Large-scale, many environments, DRY configuration, team-level isolation.

---

## Provider Configuration Patterns

### Version Pinning
```hcl
terraform {
  required_version = ">= 1.5.0"

  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"    # Allow 5.x, block 6.0
    }
    random = {
      source  = "hashicorp/random"
      version = "~> 3.5"
    }
  }
}
```

### Multi-Region with Aliases
```hcl
provider "aws" {
  region = "us-east-1"
}

provider "aws" {
  alias  = "west"
  region = "us-west-2"
}

resource "aws_s3_bucket" "primary" {
  bucket = "my-app-primary"
}

resource "aws_s3_bucket" "replica" {
  provider = aws.west
  bucket   = "my-app-replica"
}
```

### Multi-Account with Assume Role
```hcl
provider "aws" {
  alias  = "production"
  region = "us-east-1"

  assume_role {
    role_arn = "arn:aws:iam::PROD_ACCOUNT_ID:role/TerraformRole"
  }
}
```

---

## State Management Decision Tree

```
Single developer, small project?
├── Yes → Local state (but migrate to remote ASAP)
└── No
    ├── Using Terraform Cloud/Enterprise?
    │   └── Yes → TF Cloud native backend (built-in locking, encryption, RBAC)
    └── No
        ├── AWS?
        │   └── S3 + DynamoDB (encryption, locking, versioning)
        ├── GCP?
        │   └── GCS bucket (native locking, encryption)
        ├── Azure?
        │   └── Azure Blob Storage (native locking, encryption)
        └── Other?
            └── Consul or PostgreSQL backend

Environment isolation strategy:
├── Separate state files per environment (recommended)
│   ├── Option A: Separate directories (dev/, staging/, prod/)
│   └── Option B: Terraform workspaces (simpler but less isolation)
└── Single state file for all environments (never do this)
```

---

## CI/CD Integration Patterns

### GitHub Actions Plan/Apply

```yaml
# .github/workflows/terraform.yml
name: Terraform
on:
  pull_request:
    paths: ['terraform/**']
  push:
    branches: [main]
    paths: ['terraform/**']

jobs:
  plan:
    runs-on: ubuntu-latest
    if: github.event_name == 'pull_request'
    steps:
      - uses: actions/checkout@v4
      - uses: hashicorp/setup-terraform@v3
      - run: terraform init
      - run: terraform validate
      - run: terraform plan -out=tfplan
      - run: terraform show -json tfplan > plan.json
      # Post plan as PR comment

  apply:
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main' && github.event_name == 'push'
    environment: production
    steps:
      - uses: actions/checkout@v4
      - uses: hashicorp/setup-terraform@v3
      - run: terraform init
      - run: terraform apply -auto-approve
```

### Drift Detection

```yaml
# Run on schedule to detect drift
name: Drift Detection
on:
  schedule:
    - cron: '0 6 * * 1-5'  # Weekdays at 6 AM

jobs:
  detect:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: hashicorp/setup-terraform@v3
      - run: terraform init
      - run: |
          terraform plan -detailed-exitcode -out=drift.tfplan 2>&1 | tee drift.log
          EXIT_CODE=$?
          if [ $EXIT_CODE -eq 2 ]; then
            echo "DRIFT DETECTED — review drift.log"
            # Send alert (Slack, PagerDuty, etc.)
          fi
```

---

## Proactive Triggers

Flag these without being asked:

- **No remote backend configured** → Migrate to S3/GCS/Azure Blob with locking and encryption.
- **Provider without version constraint** → Add `version = "~> X.0"` to prevent breaking upgrades.
- **Hardcoded secrets in .tf files** → Use variables with `sensitive = true`, or integrate Vault/SSM.
- **IAM policy with `"Action": "*"`** → Scope to specific actions. No wildcard actions in production.
- **Security group open to 0.0.0.0/0 on SSH/RDP** → Restrict to bastion CIDR or use SSM Session Manager.
- **No state locking** → Enable DynamoDB table for S3 backend, or use TF Cloud.
- **Resources without tags** → Add default_tags in provider block. Tags are mandatory for cost tracking.
- **Missing `prevent_destroy` on databases/storage** → Add lifecycle block to prevent accidental deletion.

---

## Multi-Cloud Provider Configuration

When a single root module must provision across AWS, Azure, and GCP simultaneously.

### Provider Aliasing Pattern

```hcl
terraform {
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }
    azurerm = {
      source  = "hashicorp/azurerm"
      version = "~> 3.0"
    }
    google = {
      source  = "hashicorp/google"
      version = "~> 5.0"
    }
  }
}

provider "aws" {
  region = var.aws_region
}

provider "azurerm" {
  features {}
  subscription_id = var.azure_subscription_id
}

provider "google" {
  project = var.gcp_project_id
  region  = var.gcp_region
}
```

### Shared Variables Across Providers

```hcl
variable "environment" {
  description = "Environment name used across all providers"
  type        = string
  validation {
    condition     = contains(["dev", "staging", "prod"], var.environment)
    error_message = "Must be dev, staging, or prod."
  }
}

locals {
  common_tags = {
    environment = var.environment
    managed_by  = "terraform"
    project     = var.project_name
  }
}
```

### When to Use Multi-Cloud

- **Yes**: Regulatory requirements mandate data residency across providers, or the org has existing workloads on multiple clouds.
- **No**: "Avoiding vendor lock-in" alone is not sufficient justification. Multi-cloud doubles operational complexity. Prefer single-cloud unless there is a concrete business requirement.

---

## OpenTofu Compatibility

OpenTofu is an open-source fork of Terraform maintained by the Linux Foundation under the MPL 2.0 license.

### Migration from Terraform to OpenTofu

```bash
# 1. Install OpenTofu
brew install opentofu        # macOS
snap install --classic tofu  # Linux

# 2. Replace the binary — state files are compatible
tofu init                    # Re-initializes with OpenTofu
tofu plan                    # Identical plan output
tofu apply                   # Same apply workflow
```

### License Considerations

| | Terraform (1.6+) | OpenTofu |
|---|---|---|
| **License** | BSL 1.1 (source-available) | MPL 2.0 (open-source) |
| **Commercial use** | Restricted for competing products | Unrestricted |
| **Community governance** | HashiCorp | Linux Foundation |

### Feature Parity

OpenTofu tracks Terraform 1.6.x features. Key additions unique to OpenTofu:
- Client-side state encryption (`tofu init -encryption`)
- Early variable/locals evaluation
- Provider-defined functions

### When to Choose OpenTofu

- You need a fully open-source license for your supply chain.
- You want client-side state encryption without Terraform Cloud.
- Otherwise, either tool works — the HCL syntax and provider ecosystem are identical.

---

## Infracost Integration

Infracost estimates cloud costs from Terraform code before resources are provisioned.

### PR Workflow

```bash
# Show cost breakdown for current code
infracost breakdown --path .

# Compare cost difference between current branch and main
infracost diff --path . --compare-to infracost-base.json
```

### GitHub Actions Cost Comment

```yaml
# .github/workflows/infracost.yml
name: Infracost
on: [pull_request]

jobs:
  cost:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: infracost/actions/setup@v3
        with:
          api-key: ${{ secrets.INFRACOST_API_KEY }}
      - run: infracost breakdown --path ./terraform --format json --out-file /tmp/infracost.json
      - run: infracost comment github --path /tmp/infracost.json --repo $GITHUB_REPOSITORY --pull-request ${{ github.event.pull_request.number }} --github-token ${{ secrets.GITHUB_TOKEN }} --behavior update
```

### Budget Thresholds and Cost Policy

```yaml
# infracost.yml — policy file
version: 2.9.0
policies:
  - path: "*"
    max_monthly_cost: "5000"    # Fail PR if estimated cost exceeds $5,000/month
    max_cost_increase: "500"    # Fail PR if cost increase exceeds $500/month
```

---

## Import Existing Infrastructure

Bring manually-created resources under Terraform management.

### terraform import Workflow

```bash
# 1. Write the resource block first (empty body is fine)
# main.tf:
# resource "aws_s3_bucket" "legacy" {}

# 2. Import the resource into state
terraform import aws_s3_bucket.legacy my-existing-bucket-name

# 3. Run plan to see attribute diff
terraform plan

# 4. Fill in the resource block until plan shows no changes
```

### Bulk Import with Config Generation (Terraform 1.5+)

```bash
# Generate HCL for imported resources
terraform plan -generate-config-out=generated.tf

# Review generated.tf, then move resources into proper files
```

### Common Pitfalls

- **Resource drift after import**: The imported resource may have attributes Terraform does not manage. Run `terraform plan` immediately and resolve every diff.
- **State manipulation**: Use `terraform state mv` to rename or reorganize. Use `terraform state rm` to remove without destroying. Always back up state before manipulation: `terraform state pull > backup.tfstate`.
- **Sensitive defaults**: Imported resources may expose secrets in state. Restrict state access and enable encryption.

---

## Terragrunt Patterns

Terragrunt is a thin wrapper around Terraform that provides DRY configuration for multi-environment setups.

### Root terragrunt.hcl (Shared Config)

```hcl
# terragrunt.hcl (root)
remote_state {
  backend = "s3"
  generate = {
    path      = "backend.tf"
    if_exists = "overwrite_terragrunt"
  }
  config = {
    bucket         = "my-org-terraform-state"
    key            = "${path_relative_to_include()}/terraform.tfstate"
    region         = "us-east-1"
    encrypt        = true
    dynamodb_table = "terraform-locks"
  }
}
```

### Child terragrunt.hcl (Environment Override)

```hcl
# prod/vpc/terragrunt.hcl
include "root" {
  path = find_in_parent_folders()
}

terraform {
  source = "../../modules/vpc"
}

inputs = {
  environment = "prod"
  cidr_block  = "10.0.0.0/16"
}
```

### Dependencies Between Modules

```hcl
# prod/eks/terragrunt.hcl
dependency "vpc" {
  config_path = "../vpc"
}

inputs = {
  vpc_id     = dependency.vpc.outputs.vpc_id
  subnet_ids = dependency.vpc.outputs.private_subnet_ids
}
```

### When Terragrunt Adds Value

- **Yes**: 3+ environments with identical module structure, shared backend config, or cross-module dependencies.
- **No**: Single environment, small team, or simple directory-based isolation already works. Terragrunt adds a learning curve and another binary to manage.

---

## Installation

### One-liner (any tool)
```bash
git clone https://github.com/alirezarezvani/claude-skills.git
cp -r claude-skills/engineering/terraform-patterns ~/.claude/skills/
```

### Multi-tool install
```bash
./scripts/convert.sh --skill terraform-patterns --tool codex|gemini|cursor|windsurf|openclaw
```

### OpenClaw
```bash
clawhub install terraform-patterns
```

---

## Related Skills

- **senior-devops** — Broader DevOps scope (CI/CD, monitoring, containerization). Complementary — use terraform-patterns for IaC-specific work, senior-devops for pipeline and infrastructure operations.
- **aws-solution-architect** — AWS architecture design. Complementary — terraform-patterns implements the infrastructure, aws-solution-architect designs it.
- **senior-security** — Application security. Complementary — terraform-patterns covers infrastructure security posture, senior-security covers application-level threats.
- **ci-cd-pipeline-builder** — Pipeline construction. Complementary — terraform-patterns defines infrastructure, ci-cd-pipeline-builder automates deployment.
