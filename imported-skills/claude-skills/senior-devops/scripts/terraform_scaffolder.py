#!/usr/bin/env python3
"""
Terraform Scaffolder
Generates provider-specific Terraform module skeletons (main.tf, variables.tf,
outputs.tf, versions.tf) and optionally runs `terraform fmt`/`validate` when the
terraform binary is available.
"""

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict

# module -> required provider
MODULE_PROVIDERS = {
    "ecs-service": "aws",
    "gke-deployment": "gcp",
    "aks-service": "azure",
}

ECS_MAIN = '''resource "aws_ecs_task_definition" "app" {
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
    security_groups  = var.security_group_ids
    assign_public_ip = false
  }
}
'''

ECS_VARIABLES = '''variable "service_name" {
  description = "Name of the ECS service"
  type        = string
}

variable "cluster_id" {
  description = "ECS cluster ID"
  type        = string
}

variable "container_image" {
  description = "Container image (repo:tag)"
  type        = string
}

variable "container_port" {
  description = "Container port"
  type        = number
  default     = 8080
}

variable "cpu" {
  description = "Fargate task CPU units"
  type        = number
  default     = 256
}

variable "memory" {
  description = "Fargate task memory (MiB)"
  type        = number
  default     = 512
}

variable "desired_count" {
  description = "Desired task count"
  type        = number
  default     = 2
}

variable "aws_region" {
  description = "AWS region"
  type        = string
}

variable "private_subnet_ids" {
  description = "Private subnet IDs for the service"
  type        = list(string)
}

variable "security_group_ids" {
  description = "Security group IDs for the service"
  type        = list(string)
}

variable "env_vars" {
  description = "Environment variables for the container"
  type        = map(string)
  default     = {}
}
'''

ECS_OUTPUTS = '''output "service_name" {
  description = "Name of the ECS service"
  value       = aws_ecs_service.app.name
}

output "task_definition_arn" {
  description = "ARN of the task definition"
  value       = aws_ecs_task_definition.app.arn
}
'''

GKE_MAIN = '''resource "kubernetes_deployment" "app" {
  metadata {
    name      = var.app_name
    namespace = var.namespace
    labels    = { app = var.app_name }
  }

  spec {
    replicas = var.replicas

    selector {
      match_labels = { app = var.app_name }
    }

    template {
      metadata {
        labels = { app = var.app_name }
      }

      spec {
        container {
          name  = var.app_name
          image = var.container_image

          port {
            container_port = var.container_port
          }

          readiness_probe {
            http_get {
              path = var.health_check_path
              port = var.container_port
            }
            initial_delay_seconds = 10
            period_seconds        = 5
          }

          resources {
            requests = {
              cpu    = var.cpu_request
              memory = var.memory_request
            }
            limits = {
              cpu    = var.cpu_limit
              memory = var.memory_limit
            }
          }
        }
      }
    }
  }
}

resource "kubernetes_service" "app" {
  metadata {
    name      = var.app_name
    namespace = var.namespace
  }

  spec {
    selector = { app = var.app_name }

    port {
      port        = 80
      target_port = var.container_port
    }

    type = "ClusterIP"
  }
}
'''

GKE_VARIABLES = '''variable "app_name" {
  description = "Application name"
  type        = string
}

variable "namespace" {
  description = "Kubernetes namespace"
  type        = string
  default     = "default"
}

variable "container_image" {
  description = "Container image (repo:tag)"
  type        = string
}

variable "container_port" {
  description = "Container port"
  type        = number
  default     = 8080
}

variable "replicas" {
  description = "Number of replicas"
  type        = number
  default     = 3
}

variable "health_check_path" {
  description = "Readiness probe path"
  type        = string
  default     = "/healthz"
}

variable "cpu_request" {
  description = "CPU request"
  type        = string
  default     = "250m"
}

variable "memory_request" {
  description = "Memory request"
  type        = string
  default     = "256Mi"
}

variable "cpu_limit" {
  description = "CPU limit"
  type        = string
  default     = "500m"
}

variable "memory_limit" {
  description = "Memory limit"
  type        = string
  default     = "512Mi"
}
'''

GKE_OUTPUTS = '''output "deployment_name" {
  description = "Name of the deployment"
  value       = kubernetes_deployment.app.metadata[0].name
}

output "service_name" {
  description = "Name of the service"
  value       = kubernetes_service.app.metadata[0].name
}
'''

AKS_MAIN = '''resource "azurerm_kubernetes_cluster" "this" {
  name                = var.cluster_name
  location            = var.location
  resource_group_name = var.resource_group_name
  dns_prefix          = var.cluster_name

  default_node_pool {
    name       = "default"
    node_count = var.node_count
    vm_size    = var.vm_size
  }

  identity {
    type = "SystemAssigned"
  }

  tags = var.tags
}
'''

AKS_VARIABLES = '''variable "cluster_name" {
  description = "AKS cluster name"
  type        = string
}

variable "location" {
  description = "Azure region"
  type        = string
}

variable "resource_group_name" {
  description = "Resource group name"
  type        = string
}

variable "node_count" {
  description = "Default node pool size"
  type        = number
  default     = 3
}

variable "vm_size" {
  description = "Node VM size"
  type        = string
  default     = "Standard_D2s_v5"
}

variable "tags" {
  description = "Resource tags"
  type        = map(string)
  default     = {}
}
'''

AKS_OUTPUTS = '''output "cluster_name" {
  description = "AKS cluster name"
  value       = azurerm_kubernetes_cluster.this.name
}

output "kube_config" {
  description = "Raw kube config for the cluster"
  value       = azurerm_kubernetes_cluster.this.kube_config_raw
  sensitive   = true
}
'''

VERSIONS = {
    "aws": '''terraform {
  required_version = ">= 1.5"
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = ">= 5.0"
    }
  }
}
''',
    "gcp": '''terraform {
  required_version = ">= 1.5"
  required_providers {
    kubernetes = {
      source  = "hashicorp/kubernetes"
      version = ">= 2.0"
    }
  }
}
''',
    "azure": '''terraform {
  required_version = ">= 1.5"
  required_providers {
    azurerm = {
      source  = "hashicorp/azurerm"
      version = ">= 3.0"
    }
  }
}
''',
}

MODULE_FILES: Dict[str, Dict[str, str]] = {
    "ecs-service": {"main.tf": ECS_MAIN, "variables.tf": ECS_VARIABLES, "outputs.tf": ECS_OUTPUTS},
    "gke-deployment": {"main.tf": GKE_MAIN, "variables.tf": GKE_VARIABLES, "outputs.tf": GKE_OUTPUTS},
    "aks-service": {"main.tf": AKS_MAIN, "variables.tf": AKS_VARIABLES, "outputs.tf": AKS_OUTPUTS},
}


def run_terraform_checks(module_dir: Path, verbose: bool) -> Dict:
    """Run terraform fmt/validate when the binary exists; otherwise skip."""
    checks = {"terraform_available": False, "fmt": "skipped", "validate": "skipped"}
    if not shutil.which("terraform"):
        if verbose:
            print("ℹ️  terraform binary not found — skipping fmt/validate")
        return checks

    checks["terraform_available"] = True
    fmt = subprocess.run(
        ["terraform", "fmt", "-recursive", str(module_dir)],
        capture_output=True, text=True,
    )
    checks["fmt"] = "passed" if fmt.returncode == 0 else f"failed: {fmt.stderr.strip()}"

    init = subprocess.run(
        ["terraform", f"-chdir={module_dir}", "init", "-backend=false", "-input=false"],
        capture_output=True, text=True,
    )
    if init.returncode == 0:
        validate = subprocess.run(
            ["terraform", f"-chdir={module_dir}", "validate"],
            capture_output=True, text=True,
        )
        checks["validate"] = "passed" if validate.returncode == 0 else f"failed: {validate.stderr.strip()}"
    else:
        checks["validate"] = f"init failed: {init.stderr.strip()}"
    return checks


def scaffold(target: Path, provider: str, module: str, force: bool, verbose: bool) -> Dict:
    expected_provider = MODULE_PROVIDERS[module]
    if provider != expected_provider:
        raise ValueError(
            f"Module '{module}' targets provider '{expected_provider}', not '{provider}'. "
            f"Valid pairs: " + ", ".join(f"{m} → {p}" for m, p in MODULE_PROVIDERS.items())
        )

    module_dir = target / "modules" / module
    module_dir.mkdir(parents=True, exist_ok=True)

    files = dict(MODULE_FILES[module])
    files["versions.tf"] = VERSIONS[provider]

    written, skipped = [], []
    for name, content in sorted(files.items()):
        path = module_dir / name
        if path.exists() and not force:
            skipped.append(str(path))
            if verbose:
                print(f"⏭️  Exists, skipping (use --force to overwrite): {path}")
            continue
        path.write_text(content, encoding="utf-8")
        written.append(str(path))
        if verbose:
            print(f"✓ Wrote {path}")

    return {
        "status": "success",
        "provider": provider,
        "module": module,
        "module_dir": str(module_dir),
        "files_written": written,
        "files_skipped": skipped,
        "checks": run_terraform_checks(module_dir, verbose),
    }


def main():
    parser = argparse.ArgumentParser(
        description="Generate a Terraform module skeleton for AWS/GCP/Azure."
    )
    parser.add_argument("target", help="Target infrastructure directory (e.g. ./infra)")
    parser.add_argument("--provider", required=True, choices=["aws", "gcp", "azure"],
                        help="Cloud provider")
    parser.add_argument("--module", required=True, choices=sorted(MODULE_PROVIDERS),
                        help="Module template to scaffold")
    parser.add_argument("--force", action="store_true",
                        help="Overwrite existing files")
    parser.add_argument("--verbose", "-v", action="store_true", help="Enable verbose output")
    parser.add_argument("--json", action="store_true", help="Output results as JSON")
    parser.add_argument("--output", "-o", help="Write JSON results to this file")
    args = parser.parse_args()

    print(f"🚀 Scaffolding {args.provider}/{args.module} module under {args.target} ...")
    try:
        results = scaffold(Path(args.target), args.provider, args.module, args.force, args.verbose)
    except ValueError as exc:
        print(f"❌ Error: {exc}", file=sys.stderr)
        sys.exit(1)

    print(f"✅ Module ready: {results['module_dir']} "
          f"({len(results['files_written'])} written, {len(results['files_skipped'])} skipped)")

    if args.json or args.output:
        output = json.dumps(results, indent=2)
        if args.output:
            Path(args.output).write_text(output, encoding="utf-8")
            print(f"Results written to {args.output}")
        else:
            print(output)


if __name__ == "__main__":
    main()
