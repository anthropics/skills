# Terraform State Management Reference

## Backend Configuration Patterns

### AWS: S3 + DynamoDB (Recommended)

```hcl
terraform {
  backend "s3" {
    bucket         = "mycompany-terraform-state"
    key            = "project/env/terraform.tfstate"
    region         = "us-east-1"
    encrypt        = true
    dynamodb_table = "terraform-locks"
    # Optional: KMS key for encryption
    # kms_key_id   = "arn:aws:kms:us-east-1:ACCOUNT:key/KEY_ID"
  }
}
```

**Prerequisites:**
```hcl
# Bootstrap these resources manually or with a separate Terraform config
resource "aws_s3_bucket" "state" {
  bucket = "mycompany-terraform-state"

  lifecycle {
    prevent_destroy = true
  }
}

resource "aws_s3_bucket_versioning" "state" {
  bucket = aws_s3_bucket.state.id
  versioning_configuration {
    status = "Enabled"
  }
}

resource "aws_s3_bucket_server_side_encryption_configuration" "state" {
  bucket = aws_s3_bucket.state.id
  rule {
    apply_server_side_encryption_by_default {
      sse_algorithm = "aws:kms"
    }
  }
}

resource "aws_s3_bucket_public_access_block" "state" {
  bucket                  = aws_s3_bucket.state.id
  block_public_acls       = true
  block_public_policy     = true
  ignore_public_acls      = true
  restrict_public_buckets = true
}

resource "aws_dynamodb_table" "locks" {
  name         = "terraform-locks"
  billing_mode = "PAY_PER_REQUEST"
  hash_key     = "LockID"

  attribute {
    name = "LockID"
    type = "S"
  }
}
```

---

### GCP: Google Cloud Storage

```hcl
terraform {
  backend "gcs" {
    bucket = "mycompany-terraform-state"
    prefix = "project/env"
  }
}
```

**Key features:**
- Native locking (no separate lock table needed)
- Object versioning for state history
- IAM-based access control
- Encryption at rest by default

---

### Azure: Blob Storage

```hcl
terraform {
  backend "azurerm" {
    resource_group_name  = "terraform-state-rg"
    storage_account_name = "mycompanytfstate"
    container_name       = "tfstate"
    key                  = "project/env/terraform.tfstate"
  }
}
```

**Key features:**
- Native blob locking
- Encryption at rest with Microsoft-managed or customer-managed keys
- RBAC-based access control

---

### Terraform Cloud / Enterprise

```hcl
terraform {
  cloud {
    organization = "mycompany"
    workspaces {
      name = "project-dev"
    }
  }
}
```

**Key features:**
- Built-in state locking, encryption, and versioning
- RBAC and team-based access control
- Remote execution (plan/apply run in TF Cloud)
- Sentinel policy-as-code integration
- Cost estimation on plans

---

## Environment Isolation Strategies

### Strategy 1: Separate Directories (Recommended)

```
infrastructure/
├── environments/
│   ├── dev/
│   │   ├── main.tf
│   │   ├── backend.tf      # key = "project/dev/terraform.tfstate"
│   │   └── terraform.tfvars
│   ├── staging/
│   │   ├── main.tf
│   │   ├── backend.tf      # key = "project/staging/terraform.tfstate"
│   │   └── terraform.tfvars
│   └── prod/
│       ├── main.tf
│       ├── backend.tf      # key = "project/prod/terraform.tfstate"
│       └── terraform.tfvars
└── modules/
    └── ...
```

**Pros:**
- Complete isolation — a mistake in dev can't affect prod
- Different provider versions per environment
- Different module versions per environment (pin prod, iterate in dev)
- Clear audit trail — who changed what, where

**Cons:**
- Some duplication across environment directories
- Must update modules in each environment separately

### Strategy 2: Terraform Workspaces

```hcl
# Single directory, multiple workspaces
terraform {
  backend "s3" {
    bucket         = "mycompany-terraform-state"
    key            = "project/terraform.tfstate"
    region         = "us-east-1"
    dynamodb_table = "terraform-locks"
    encrypt        = true
  }
}

# State files stored at:
# env:/dev/project/terraform.tfstate
# env:/staging/project/terraform.tfstate
# env:/prod/project/terraform.tfstate
```

```bash
terraform workspace new dev
terraform workspace select dev
terraform plan -var-file="env/dev.tfvars"
```

**Pros:**
- Less duplication — single set of .tf files
- Quick to switch between environments
- Built-in workspace support in backends

**Cons:**
- Shared code means a bug affects all environments simultaneously
- Can't have different provider versions per workspace
- Easy to accidentally apply to wrong workspace
- Less isolation than separate directories

### Strategy 3: Terragrunt (DRY Configuration)

```
infrastructure/
├── terragrunt.hcl          # Root — defines remote state pattern
├── modules/
│   └── vpc/
│       ├── main.tf
│       ├── variables.tf
│       └── outputs.tf
├── dev/
│   ├── terragrunt.hcl      # env = "dev"
│   └── vpc/
│       └── terragrunt.hcl  # inputs for dev VPC
├── staging/
│   └── ...
└── prod/
    └── ...
```

```hcl
# Root terragrunt.hcl
remote_state {
  backend = "s3"
  generate = {
    path      = "backend.tf"
    if_exists = "overwrite_terragrunt"
  }
  config = {
    bucket         = "mycompany-terraform-state"
    key            = "${path_relative_to_include()}/terraform.tfstate"
    region         = "us-east-1"
    encrypt        = true
    dynamodb_table = "terraform-locks"
  }
}

# dev/vpc/terragrunt.hcl
terraform {
  source = "../../modules/vpc"
}

inputs = {
  environment = "dev"
  vpc_cidr    = "10.0.0.0/16"
}
```

**Pros:**
- Maximum DRY — define module once, parameterize per environment
- Automatic state key generation from directory structure
- Dependency management between modules (`dependency` blocks)
- `run-all` for applying multiple modules at once

**Cons:**
- Additional tool dependency (Terragrunt)
- Learning curve
- Debugging can be harder (generated files)

---

## State Migration Patterns

### Local to Remote (S3)

```bash
# 1. Add backend configuration to backend.tf
# 2. Run init with migration flag
terraform init -migrate-state

# Terraform will prompt:
# "Do you want to copy existing state to the new backend?"
# Answer: yes
```

### Between Remote Backends

```bash
# 1. Pull current state
terraform state pull > terraform.tfstate.backup

# 2. Update backend configuration in backend.tf

# 3. Reinitialize with migration
terraform init -migrate-state

# 4. Verify
terraform plan  # Should show no changes
```

### State Import (Existing Resources)

```bash
# Import a single resource
terraform import aws_instance.web i-1234567890abcdef0

# Import with for_each key
terraform import 'aws_subnet.public["us-east-1a"]' subnet-0123456789abcdef0

# Bulk import (Terraform 1.5+ import blocks)
import {
  to = aws_instance.web
  id = "i-1234567890abcdef0"
}
```

### State Move (Refactoring)

```bash
# Rename a resource (avoids destroy/recreate)
terraform state mv aws_instance.old_name aws_instance.new_name

# Move into a module
terraform state mv aws_instance.web module.compute.aws_instance.web

# Move between state files
terraform state mv -state-out=other.tfstate aws_instance.web aws_instance.web
```

---

## State Locking

### Why Locking Matters
Without locking, two concurrent `terraform apply` runs can corrupt state. The second apply reads stale state and may create duplicate resources or lose track of existing ones.

### Lock Behavior by Backend

| Backend | Lock Mechanism | Auto-Lock | Force Unlock |
|---------|---------------|-----------|--------------|
| S3 | DynamoDB table | Yes (if table configured) | `terraform force-unlock LOCK_ID` |
| GCS | Native blob locking | Yes | `terraform force-unlock LOCK_ID` |
| Azure Blob | Native blob lease | Yes | `terraform force-unlock LOCK_ID` |
| TF Cloud | Built-in | Always | Via UI or API |
| Consul | Key-value lock | Yes | `terraform force-unlock LOCK_ID` |
| Local | `.terraform.lock.hcl` | Yes (single user) | Delete lock file |

### Force Unlock (Emergency Only)

```bash
# Only use when you're certain no other process is running
terraform force-unlock LOCK_ID

# The LOCK_ID is shown in the error message when lock fails:
# Error: Error locking state: Error acquiring the state lock
# Lock Info:
#   ID:        12345678-abcd-1234-abcd-1234567890ab
```

---

## State Security Best Practices

### 1. Encrypt at Rest
```hcl
# S3 — server-side encryption
backend "s3" {
  encrypt    = true
  kms_key_id = "arn:aws:kms:us-east-1:ACCOUNT:key/KEY_ID"
}
```

### 2. Restrict Access
```json
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Effect": "Allow",
      "Action": [
        "s3:GetObject",
        "s3:PutObject",
        "s3:DeleteObject"
      ],
      "Resource": "arn:aws:s3:::mycompany-terraform-state/project/*",
      "Condition": {
        "StringEquals": {
          "aws:PrincipalTag/Team": "platform"
        }
      }
    },
    {
      "Effect": "Allow",
      "Action": [
        "dynamodb:GetItem",
        "dynamodb:PutItem",
        "dynamodb:DeleteItem"
      ],
      "Resource": "arn:aws:dynamodb:us-east-1:ACCOUNT:table/terraform-locks"
    }
  ]
}
```

### 3. Enable Versioning (State History)
```hcl
resource "aws_s3_bucket_versioning" "state" {
  bucket = aws_s3_bucket.state.id
  versioning_configuration {
    status = "Enabled"
  }
}
```

Versioning lets you recover from state corruption by restoring a previous version.

### 4. Audit Access
- Enable S3 access logging or CloudTrail data events
- Monitor for unexpected state reads (potential secret extraction)
- State files contain sensitive values — treat them like credentials

### 5. Sensitive Values in State
Terraform stores all resource attributes in state, including passwords, private keys, and tokens. This is unavoidable. Mitigate by:
- Encrypting state at rest (KMS)
- Restricting state file access (IAM)
- Using `sensitive = true` on variables and outputs (prevents display, not storage)
- Rotating secrets regularly (state contains the value at apply time)

---

## Drift Detection and Reconciliation

### Detect Drift
```bash
# Plan with detailed exit code
terraform plan -detailed-exitcode
# Exit 0 = no changes
# Exit 1 = error
# Exit 2 = changes detected (drift)
```

### Common Drift Sources
| Source | Example | Prevention |
|--------|---------|------------|
| Console changes | Someone edits SG rules in AWS Console | SCPs to restrict console access, or accept and reconcile |
| Auto-scaling | ASG launches instances not in state | Don't manage individual instances; manage ASG |
| External tools | Ansible modifies EC2 tags | Agree on ownership boundaries |
| Dependent resource changes | AMI deregistered | Use data sources to detect, lifecycle ignore_changes |

### Reconciliation Options
```hcl
# Option 1: Apply to restore desired state
terraform apply

# Option 2: Refresh state to match reality
terraform apply -refresh-only

# Option 3: Ignore specific attribute drift
resource "aws_instance" "web" {
  lifecycle {
    ignore_changes = [tags["LastModifiedBy"], ami]
  }
}

# Option 4: Import the manually-created resource
terraform import aws_security_group_rule.new sg-12345_ingress_tcp_443_443_0.0.0.0/0
```

---

## Troubleshooting Checklist

| Symptom | Likely Cause | Fix |
|---------|-------------|-----|
| "Error acquiring state lock" | Concurrent run or crashed process | Wait for other run to finish, or `force-unlock` |
| "Backend configuration changed" | Backend config modified | Run `terraform init -reconfigure` or `-migrate-state` |
| "Resource already exists" | Resource created outside Terraform | `terraform import` the resource |
| "No matching resource found" | Resource deleted outside Terraform | `terraform state rm` the resource |
| State file growing very large | Too many resources in one state | Split into smaller state files using modules |
| Slow plan/apply | Large state file, many resources | Split state, use `-target` for urgent changes |
| "Provider produced inconsistent result" | Provider bug or API race condition | Retry, or pin provider version |
| Workspace confusion | Applied to wrong workspace | Always check `terraform workspace show` before apply |
