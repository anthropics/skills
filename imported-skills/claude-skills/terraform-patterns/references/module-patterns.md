# Terraform Module Design Patterns Reference

## Pattern 1: Flat Module (Single Directory)

Best for: Small projects, < 20 resources, single team ownership.

```
project/
├── main.tf
├── variables.tf
├── outputs.tf
├── versions.tf
├── locals.tf
├── backend.tf
└── terraform.tfvars
```

### Example: Simple VPC + EC2

```hcl
# versions.tf
terraform {
  required_version = ">= 1.5.0"

  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }
  }
}

# locals.tf
locals {
  name_prefix = "${var.project}-${var.environment}"
  common_tags = {
    Project     = var.project
    Environment = var.environment
    ManagedBy   = "terraform"
  }
}

# main.tf
resource "aws_vpc" "main" {
  cidr_block           = var.vpc_cidr
  enable_dns_hostnames = true
  enable_dns_support   = true

  tags = merge(local.common_tags, {
    Name = "${local.name_prefix}-vpc"
  })
}

resource "aws_subnet" "public" {
  count             = length(var.public_subnet_cidrs)
  vpc_id            = aws_vpc.main.id
  cidr_block        = var.public_subnet_cidrs[count.index]
  availability_zone = var.availability_zones[count.index]

  tags = merge(local.common_tags, {
    Name = "${local.name_prefix}-public-${count.index + 1}"
    Tier = "public"
  })
}

# variables.tf
variable "project" {
  description = "Project name used for resource naming"
  type        = string
}

variable "environment" {
  description = "Deployment environment"
  type        = string
  validation {
    condition     = contains(["dev", "staging", "prod"], var.environment)
    error_message = "Environment must be dev, staging, or prod."
  }
}

variable "vpc_cidr" {
  description = "CIDR block for the VPC"
  type        = string
  default     = "10.0.0.0/16"
  validation {
    condition     = can(cidrhost(var.vpc_cidr, 0))
    error_message = "Must be a valid CIDR block."
  }
}

variable "public_subnet_cidrs" {
  description = "CIDR blocks for public subnets"
  type        = list(string)
  default     = ["10.0.1.0/24", "10.0.2.0/24"]
}

variable "availability_zones" {
  description = "AZs for subnet placement"
  type        = list(string)
  default     = ["us-east-1a", "us-east-1b"]
}

# outputs.tf
output "vpc_id" {
  description = "ID of the created VPC"
  value       = aws_vpc.main.id
}

output "public_subnet_ids" {
  description = "IDs of public subnets"
  value       = aws_subnet.public[*].id
}
```

---

## Pattern 2: Nested Modules (Composition)

Best for: Multiple environments, shared patterns, team collaboration.

```
infrastructure/
├── environments/
│   ├── dev/
│   │   ├── main.tf
│   │   ├── backend.tf
│   │   └── terraform.tfvars
│   ├── staging/
│   │   └── ...
│   └── prod/
│       └── ...
└── modules/
    ├── networking/
    │   ├── main.tf
    │   ├── variables.tf
    │   └── outputs.tf
    ├── compute/
    │   └── ...
    └── database/
        └── ...
```

### Root Module (environments/dev/main.tf)

```hcl
module "networking" {
  source = "../../modules/networking"

  project              = var.project
  environment          = "dev"
  vpc_cidr             = "10.0.0.0/16"
  public_subnet_cidrs  = ["10.0.1.0/24", "10.0.2.0/24"]
  private_subnet_cidrs = ["10.0.10.0/24", "10.0.11.0/24"]
}

module "compute" {
  source = "../../modules/compute"

  project        = var.project
  environment    = "dev"
  vpc_id         = module.networking.vpc_id
  subnet_ids     = module.networking.private_subnet_ids
  instance_type  = "t3.micro"
  instance_count = 1
}

module "database" {
  source = "../../modules/database"

  project            = var.project
  environment        = "dev"
  vpc_id             = module.networking.vpc_id
  subnet_ids         = module.networking.private_subnet_ids
  instance_class     = "db.t3.micro"
  allocated_storage  = 20
  db_password        = var.db_password
}
```

### Key Rules
- Child modules never call other child modules
- Pass values explicitly — no hidden data source lookups in children
- Provider configuration only in root module
- Each module has its own variables.tf, outputs.tf, main.tf

---

## Pattern 3: Registry Module Pattern

Best for: Reusable modules shared across teams or organizations.

```
terraform-aws-vpc/
├── main.tf
├── variables.tf
├── outputs.tf
├── versions.tf
├── README.md
├── examples/
│   ├── simple/
│   │   └── main.tf
│   └── complete/
│       └── main.tf
└── modules/
    ├── subnet/
    │   ├── main.tf
    │   ├── variables.tf
    │   └── outputs.tf
    └── nat-gateway/
        └── ...
```

### Publishing Conventions

```hcl
# Consumer usage
module "vpc" {
  source  = "terraform-aws-modules/vpc/aws"
  version = "~> 5.0"

  name = "my-vpc"
  cidr = "10.0.0.0/16"

  azs             = ["us-east-1a", "us-east-1b"]
  private_subnets = ["10.0.1.0/24", "10.0.2.0/24"]
  public_subnets  = ["10.0.101.0/24", "10.0.102.0/24"]

  enable_nat_gateway = true
  single_nat_gateway = true
}
```

### Registry Module Requirements
- Repository named `terraform-<PROVIDER>-<NAME>`
- README.md with usage examples
- Semantic versioning via git tags
- examples/ directory with working configurations
- No provider configuration in the module itself

---

## Pattern 4: Mono-Repo with Workspaces

Best for: Teams that prefer single-repo with workspace-based isolation.

```hcl
# backend.tf
terraform {
  backend "s3" {
    bucket         = "my-terraform-state"
    key            = "project/terraform.tfstate"
    region         = "us-east-1"
    dynamodb_table = "terraform-locks"
    encrypt        = true
  }
}

# main.tf
locals {
  env_config = {
    dev = {
      instance_type = "t3.micro"
      instance_count = 1
      db_class = "db.t3.micro"
    }
    staging = {
      instance_type = "t3.small"
      instance_count = 2
      db_class = "db.t3.small"
    }
    prod = {
      instance_type = "t3.large"
      instance_count = 3
      db_class = "db.r5.large"
    }
  }
  config = local.env_config[terraform.workspace]
}
```

### Usage
```bash
terraform workspace new dev
terraform workspace new staging
terraform workspace new prod

terraform workspace select dev
terraform apply

terraform workspace select prod
terraform apply
```

### Workspace Caveats
- All environments share the same backend — less isolation than separate directories
- A mistake in the code affects all environments
- Can't have different provider versions per workspace
- Recommended only for simple setups; prefer separate directories for production

---

## Pattern 5: for_each vs count

### Use `count` for identical resources
```hcl
resource "aws_subnet" "public" {
  count             = 3
  vpc_id            = aws_vpc.main.id
  cidr_block        = cidrsubnet(var.vpc_cidr, 8, count.index)
  availability_zone = data.aws_availability_zones.available.names[count.index]
}
```

### Use `for_each` for distinct resources
```hcl
variable "buckets" {
  type = map(object({
    versioning = bool
    lifecycle_days = number
  }))
  default = {
    logs    = { versioning = false, lifecycle_days = 30 }
    backups = { versioning = true,  lifecycle_days = 90 }
    assets  = { versioning = true,  lifecycle_days = 0 }
  }
}

resource "aws_s3_bucket" "this" {
  for_each = var.buckets
  bucket   = "${var.project}-${each.key}"
}

resource "aws_s3_bucket_versioning" "this" {
  for_each = { for k, v in var.buckets : k => v if v.versioning }
  bucket   = aws_s3_bucket.this[each.key].id

  versioning_configuration {
    status = "Enabled"
  }
}
```

### Why `for_each` > `count`
- `count` uses index — removing item 0 shifts all others, causing destroy/recreate
- `for_each` uses keys — removing a key only affects that resource
- Use `count` only for identical resources where order doesn't matter

---

## Variable Design Patterns

### Object Variables for Related Settings
```hcl
variable "database" {
  description = "Database configuration"
  type = object({
    engine         = string
    instance_class = string
    storage_gb     = number
    multi_az       = bool
    backup_days    = number
  })
  default = {
    engine         = "postgres"
    instance_class = "db.t3.micro"
    storage_gb     = 20
    multi_az       = false
    backup_days    = 7
  }
}
```

### Validation Blocks
```hcl
variable "instance_type" {
  description = "EC2 instance type"
  type        = string

  validation {
    condition     = can(regex("^t[23]\\.", var.instance_type))
    error_message = "Only t2 or t3 instance types are allowed."
  }
}

variable "cidr_block" {
  description = "VPC CIDR block"
  type        = string

  validation {
    condition     = can(cidrhost(var.cidr_block, 0))
    error_message = "Must be a valid IPv4 CIDR block."
  }
}
```

---

## Anti-Patterns to Avoid

| Anti-Pattern | Problem | Solution |
|-------------|---------|----------|
| God module (100+ resources) | Impossible to reason about, slow plan/apply | Split into focused child modules |
| Circular module dependencies | Terraform can't resolve dependency graph | Flatten or restructure module boundaries |
| Data sources in child modules | Hidden dependencies, hard to test | Pass values as variables from root module |
| Provider config in child modules | Can't reuse module across accounts/regions | Configure providers in root only |
| Hardcoded values | Not reusable across environments | Use variables with defaults and validation |
| No outputs | Consumer modules can't reference resources | Output IDs, ARNs, endpoints |
| No variable descriptions | Users don't know what to provide | Every variable gets a description |
| `terraform.tfvars` committed | Secrets leak to version control | Use `.gitignore`, env vars, or Vault |
