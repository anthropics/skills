# Deploy to Terraform

This guide covers deploying Strands agents using Terraform infrastructure as code. Terraform enables consistent, repeatable deployments across AWS, Google Cloud, Azure, and other cloud providers.

Terraform supports multiple deployment targets. This deploy example illustates four deploy options from different Cloud Service Providers:

- **[AWS App Runner](#option-a-aws-app-runner-containerized)** - Simple containerized deployment with automatic scaling
- **[AWS Lambda](#option-b-aws-lambda-serverless)** - Serverless functions for event-driven workloads
- **[Google Cloud Run](#option-c-google-cloud-run)** - Fully managed serverless containers
- **[Azure Container Instances](#option-d-azure-container-instances)** - Simple container deployment

## Prerequisites

- **Docker deployment guide completed** - You must have a working containerized agent before proceeding:
    - [Python Docker guide](../deploy_to_docker/python) 
    - [TypeScript Docker guide](../deploy_to_docker/typescript)
- [Terraform](https://www.terraform.io/downloads.html) installed
- Cloud provider CLI configured:
    - AWS: [AWS CLI credentials](https://docs.aws.amazon.com/cli/latest/userguide/cli-chap-getting-started.html)
    - GCP: [gcloud CLI](https://cloud.google.com/sdk/docs/install)
    - Azure: [Azure CLI](https://docs.microsoft.com/en-us/cli/azure/install-azure-cli)


## Step 1: Container Registry Deployment

Cloud deployment requires your containerized agent to be available in a container registry. The following assumes you have completed the [Docker deployment guide](../deploy_to_docker) and pushed your image to the appropriate registry:

**Docker Tutorial Project Structure:**

Project Structure (Python):
```
my-python-app/
├── agent.py                # FastAPI application (from Docker tutorial)
├── Dockerfile              # Container configuration (from Docker tutorial)
├── pyproject.toml          # Created by uv init
├── uv.lock                 # Created automatically by uv
```

Project Structure (TypeScript):
```
my-typescript-app/
├── index.ts                # Express application (from Docker tutorial)
├── Dockerfile              # Container configuration (from Docker tutorial)
├── package.json            # Created by npm init
├── tsconfig.json           # TypeScript configuration
├── package-lock.json       # Created automatically by npm
```

**Deploy-specific Docker configurations**

=== "AWS App Runner"

    **Image Requirements:**

    - Standard Docker images supported

    **Container Registry Requirements:**

    - Amazon Elastic Container Registry ([See documentation to push Docker image to ECR](https://docs.aws.amazon.com/AmazonECR/latest/userguide/docker-push-ecr-image.html))

    **Docker Deployment Guide Modifications:**

    - No special base image required (standard Docker images work)
    - Ensure your app listens on port 8080 (or configure port in terraform)
    - Build with: `docker build --platform linux/amd64 -t my-agent .`

=== "AWS Lambda"

    **Image Requirements:**

    - Must use Lambda-compatible base images:
      - Python: `public.ecr.aws/lambda/python:3.11`
      - TypeScript/Node.js: `public.ecr.aws/lambda/nodejs:20`

    **Container Registry Requirements:**

    - Amazon Elastic Container Registry ([See documentation to push Docker image to ECR](https://docs.aws.amazon.com/AmazonECR/latest/userguide/docker-push-ecr-image.html))

    **Docker Deployment Guide Modifications:**

    - Update Dockerfile base image to Lambda-compatible version
    - Change CMD to Lambda handler format: `CMD ["index.handler"]` or `CMD ["app.lambda_handler"]`
    - Build with Lambda flags: `docker build --platform linux/amd64 --provenance=false --sbom=false -t my-agent .`
    - Add Lambda handler to your code:
        - **Python FastAPI (Recommended):** Use [Mangum](https://mangum.io/): `lambda_handler = Mangum(app)`
        - **Manual handlers:** Accept `(event, context)` parameters and return Lambda-compatible responses

    **Lambda Handler Examples:**

    Python with Mangum:
    ```python
    from mangum import Mangum
    from your_app import app  # Your existing FastAPI app

    lambda_handler = Mangum(app)
    ```

    TypeScript:
    ```typescript
    export const handler = async (event: any, context: any) => {
        // Your existing agent logic here
        return {
            statusCode: 200,
            body: JSON.stringify({ message: "Agent response" })
        };
    };
    ```

    Python:
    ```python
    def lambda_handler(event, context):
        # Your existing agent logic here
        return {
            'statusCode': 200,
            'body': json.dumps({'message': 'Agent response'})
        }
    ```

=== "Google Cloud Run"

    **Image Requirements:**

    - Standard Docker images supported

    **Container Registry Requirements:**

    - Google Artifact Registry ([See documentation to push Docker image to GAR](https://cloud.google.com/container-registry/docs/pushing-and-pulling))

    **Docker Deployment Guide Modifications:**

    - No special base image required (standard Docker images work)
    - Ensure your app listens on the port specified by `PORT` environment variable
    - Build with: `docker build --platform linux/amd64 -t my-agent .`

=== "Azure Container Instances"

    **Image Requirements:**

    - Standard Docker images supported

    **Container Registry Requirements:**

    - Azure Container Registry ([See documentation to push Docker image to ACR](https://docs.microsoft.com/en-us/azure/container-registry/container-registry-get-started-docker-cli))

    **Docker Deployment Guide Modifications:**

    - No special base image required (standard Docker images work)
    - Ensure your app exposes the correct port (typically 8080)
    - Build with: `docker build --platform linux/amd64 -t my-agent .`

## Step 2: Cloud Deployment Setup

=== "AWS App Runner"

    <details>
      <summary>
        <strong>Optional: Open AWS App Runner Setup All-in-One Bash Command</strong><br>
        <sub>Copy and paste this bash script to create all necessary terraform files and skip remaining "Cloud Deployment Setup" steps below:</sub>
      </summary>

    ```bash
    generate_aws_apprunner_terraform() {
        mkdir -p terraform
        
        # Generate main.tf
        cat > terraform/main.tf << 'EOF'
    terraform {
      required_providers {
        aws = {
          source  = "hashicorp/aws"
          version = "~> 5.0"
        }
      }
    }

    provider "aws" {
      region = var.aws_region
    }

    resource "aws_iam_role" "apprunner_ecr_access_role" {
      name = "apprunner-ecr-access-role"

      assume_role_policy = jsonencode({
        Version = "2012-10-17"
        Statement = [
          {
            Action = "sts:AssumeRole"
            Effect = "Allow"
            Principal = {
              Service = "build.apprunner.amazonaws.com"
            }
          }
        ]
      })
    }

    resource "aws_iam_role_policy_attachment" "apprunner_ecr_access_policy" {
      role       = aws_iam_role.apprunner_ecr_access_role.name
      policy_arn = "arn:aws:iam::aws:policy/service-role/AWSAppRunnerServicePolicyForECRAccess"
    }

    resource "aws_apprunner_service" "agent" {
      service_name = "strands-agent-v4"

      source_configuration {
        image_repository {
          image_identifier      = var.agent_image
          image_configuration {
            port = "8080"
            runtime_environment_variables = {
              OPENAI_API_KEY = var.openai_api_key
            }
          }
          image_repository_type = "ECR"
        }
        auto_deployments_enabled = false
        authentication_configuration {
          access_role_arn = aws_iam_role.apprunner_ecr_access_role.arn
        }
      }

      instance_configuration {
        cpu    = "0.25 vCPU"
        memory = "0.5 GB"
      }
    }
    EOF

        # Generate variables.tf
        cat > terraform/variables.tf << 'EOF'
    variable "aws_region" {
      description = "AWS region"
      type        = string
      default     = "us-east-1"
    }

    variable "agent_image" {
      description = "Container image for Strands agent"
      type        = string
    }

    variable "openai_api_key" {
      description = "OpenAI API key"
      type        = string
      sensitive   = true
    }
    EOF

        # Generate outputs.tf
        cat > terraform/outputs.tf << 'EOF'
    output "agent_url" {
      description = "AWS App Runner service URL"
      value       = aws_apprunner_service.agent.service_url
    }
    EOF

        # Generate terraform.tfvars template
        cat > terraform/terraform.tfvars << 'EOF'
    agent_image = "your-account.dkr.ecr.us-east-1.amazonaws.com/my-image:latest"
    openai_api_key = "<your-openai-api-key>"
    EOF

        echo "✅ AWS App Runner Terraform files generated in terraform/ directory"
    }

    generate_aws_apprunner_terraform
    ```

    </details>

    **Step by Step Guide**

    Create terraform directory

    ```bash
    mkdir terraform
    cd terraform
    ```

    Create `main.tf`

    ```hcl
    terraform {
      required_providers {
        aws = {
          source  = "hashicorp/aws"
          version = "~> 5.0"
        }
      }
    }

    provider "aws" {
      region = var.aws_region
    }

    resource "aws_iam_role" "apprunner_ecr_access_role" {
      name = "apprunner-ecr-access-role"

      assume_role_policy = jsonencode({
        Version = "2012-10-17"
        Statement = [
          {
            Action = "sts:AssumeRole"
            Effect = "Allow"
            Principal = {
              Service = "build.apprunner.amazonaws.com"
            }
          }
        ]
      })
    }

    resource "aws_iam_role_policy_attachment" "apprunner_ecr_access_policy" {
      role       = aws_iam_role.apprunner_ecr_access_role.name
      policy_arn = "arn:aws:iam::aws:policy/service-role/AWSAppRunnerServicePolicyForECRAccess"
    }

    resource "aws_apprunner_service" "agent" {
      service_name = "strands-agent-v4"

      source_configuration {
        image_repository {
          image_identifier      = var.agent_image
          image_configuration {
            port = "8080"
            runtime_environment_variables = {
              OPENAI_API_KEY = var.openai_api_key
            }
          }
          image_repository_type = "ECR"
        }
        auto_deployments_enabled = false
        authentication_configuration {
          access_role_arn = aws_iam_role.apprunner_ecr_access_role.arn
        }
      }

      instance_configuration {
        cpu    = "0.25 vCPU"
        memory = "0.5 GB"
      }
    }
    ```

    Create `variables.tf`

    ```hcl
    variable "aws_region" {
      description = "AWS region"
      type        = string
      default     = "us-east-1"
    }

    variable "agent_image" {
      description = "Container image for Strands agent"
      type        = string
    }

    variable "openai_api_key" {
      description = "OpenAI API key"
      type        = string
      sensitive   = true
    }
    ```

    Create `outputs.tf`

    ```hcl
    output "agent_url" {
      description = "AWS App Runner service URL"
      value       = aws_apprunner_service.agent.service_url
    }
    ```

=== "AWS Lambda"

    <details>
      <summary>
        <strong>Optional: Open AWS Lambda Setup All-in-One Bash Command</strong><br>
        <sub>Copy and paste this bash script to create all necessary terraform files and skip remaining "Cloud Deployment Setup" steps below:</sub>
      </summary>

    ```bash
    generate_aws_lambda_terraform() {
        mkdir -p terraform
        
        # Generate main.tf
        cat > terraform/main.tf << 'EOF'
    terraform {
      required_providers {
        aws = {
          source  = "hashicorp/aws"
          version = "~> 5.0"
        }
      }
    }

    provider "aws" {
      region = var.aws_region
    }

    resource "aws_lambda_function" "agent" {
      function_name = "strands-agent"
      role          = aws_iam_role.lambda.arn
      image_uri     = var.agent_image
      package_type  = "Image"
      architectures = ["x86_64"]
      timeout       = 30
      memory_size   = 512

      environment {
        variables = {
          OPENAI_API_KEY = var.openai_api_key
        }
      }
    }

    resource "aws_lambda_function_url" "agent" {
      function_name      = aws_lambda_function.agent.function_name
      authorization_type = "NONE"
    }

    resource "aws_iam_role" "lambda" {
      name = "strands-agent-lambda-role"
      assume_role_policy = jsonencode({
        Version = "2012-10-17"
        Statement = [{
          Action = "sts:AssumeRole"
          Effect = "Allow"
          Principal = {
            Service = "lambda.amazonaws.com"
          }
        }]
      })
    }

    resource "aws_iam_role_policy_attachment" "lambda" {
      role       = aws_iam_role.lambda.name
      policy_arn = "arn:aws:iam::aws:policy/service-role/AWSLambdaBasicExecutionRole"
    }
    EOF

        # Generate variables.tf
        cat > terraform/variables.tf << 'EOF'
    variable "aws_region" {
      description = "AWS region"
      type        = string
      default     = "us-east-1"
    }

    variable "agent_image" {
      description = "Container image for Strands agent"
      type        = string
    }

    variable "openai_api_key" {
      description = "OpenAI API key"
      type        = string
      sensitive   = true
    }
    EOF

        # Generate outputs.tf
        cat > terraform/outputs.tf << 'EOF'
    output "agent_url" {
      description = "AWS Lambda function URL"
      value       = aws_lambda_function_url.agent.function_url
    }
    EOF

        # Generate terraform.tfvars template
        cat > terraform/terraform.tfvars << 'EOF'
    agent_image = "your-account.dkr.ecr.us-east-1.amazonaws.com/my-image:latest"
    openai_api_key = "<your-openai-api-key>"
    EOF

        echo "✅ AWS Lambda Terraform files generated in terraform/ directory"
    }

    generate_aws_lambda_terraform
    ```
    </details>

    **Step by Step Guide**

    Create terraform directory

    ```bash
    mkdir terraform
    cd terraform
    ```

    Create `main.tf`

    ```hcl
    terraform {
      required_providers {
        aws = {
          source  = "hashicorp/aws"
          version = "~> 5.0"
        }
      }
    }

    provider "aws" {
      region = var.aws_region
    }

    resource "aws_lambda_function" "agent" {
      function_name = "strands-agent"
      role          = aws_iam_role.lambda.arn
      image_uri     = var.agent_image
      package_type  = "Image"
      architectures = ["x86_64"]
      timeout       = 30
      memory_size   = 512

      environment {
        variables = {
          OPENAI_API_KEY = var.openai_api_key
        }
      }
    }

    resource "aws_lambda_function_url" "agent" {
      function_name      = aws_lambda_function.agent.function_name
      authorization_type = "NONE"
    }

    resource "aws_iam_role" "lambda" {
      name = "strands-agent-lambda-role"
      assume_role_policy = jsonencode({
        Version = "2012-10-17"
        Statement = [{
          Action = "sts:AssumeRole"
          Effect = "Allow"
          Principal = {
            Service = "lambda.amazonaws.com"
          }
        }]
      })
    }

    resource "aws_iam_role_policy_attachment" "lambda" {
      role       = aws_iam_role.lambda.name
      policy_arn = "arn:aws:iam::aws:policy/service-role/AWSLambdaBasicExecutionRole"
    }
    ```

    Create `variables.tf`

    ```hcl
    variable "aws_region" {
      description = "AWS region"
      type        = string
      default     = "us-east-1"
    }

    variable "agent_image" {
      description = "Container image for Strands agent"
      type        = string
    }

    variable "openai_api_key" {
      description = "OpenAI API key"
      type        = string
      sensitive   = true
    }
    ```

    Create `outputs.tf`

    ```hcl
    output "agent_url" {
      description = "AWS Lambda function URL"
      value       = aws_lambda_function_url.agent.function_url
    }
    ```

=== "Google Cloud Run"

    <details>
      <summary>
        <strong>Optional: Open Google Cloud Run Setup All-in-One Bash Command</strong><br>
        <sub>Copy and paste this bash script to create all necessary terraform files and skip remaining "Cloud Deployment Setup" steps below:</sub>
      </summary>

    ```bash
    generate_google_cloud_run_terraform() {
        mkdir -p terraform
        
        # Generate main.tf
        cat > terraform/main.tf << 'EOF'
    terraform {
      required_providers {
        google = {
          source  = "hashicorp/google"
          version = "~> 4.0"
        }
      }
    }

    provider "google" {
      project = var.gcp_project
      region  = var.gcp_region
    }

    resource "google_cloud_run_service" "agent" {
      name     = "strands-agent"
      location = var.gcp_region

      template {
        spec {
          containers {
            image = var.agent_image
            env {
              name  = "OPENAI_API_KEY"
              value = var.openai_api_key
            }
          }
        }
      }
    }

    resource "google_cloud_run_service_iam_member" "public" {
      service  = google_cloud_run_service.agent.name
      location = google_cloud_run_service.agent.location
      role     = "roles/run.invoker"
      member   = "allUsers"
    }
    EOF

        # Generate variables.tf
        cat > terraform/variables.tf << 'EOF'
    variable "gcp_project" {
      description = "GCP project ID"
      type        = string
    }

    variable "gcp_region" {
      description = "GCP region"
      type        = string
      default     = "us-central1"
    }

    variable "agent_image" {
      description = "Container image for Strands agent"
      type        = string
    }

    variable "openai_api_key" {
      description = "OpenAI API key"
      type        = string
      sensitive   = true
    }
    EOF

        # Generate outputs.tf
        cat > terraform/outputs.tf << 'EOF'
    output "agent_url" {
      description = "Google Cloud Run service URL"
      value       = google_cloud_run_service.agent.status[0].url
    }
    EOF

        # Generate terraform.tfvars template
        cat > terraform/terraform.tfvars << 'EOF'
    gcp_project = "<your-project-id>"
    agent_image = "gcr.io/your-project/my-image:latest"
    openai_api_key = "<your-openai-api-key>"
    EOF

        echo "✅ Google Cloud Run Terraform files generated in terraform/ directory"
    }

    generate_google_cloud_run_terraform
    ```

    </details>

    **Step by Step Guide**

    Create terraform directory

    ```bash
    mkdir terraform
    cd terraform
    ```

    Create `main.tf`

    ```hcl
    terraform {
      required_providers {
        google = {
          source  = "hashicorp/google"
          version = "~> 4.0"
        }
      }
    }

    provider "google" {
      project = var.gcp_project
      region  = var.gcp_region
    }

    resource "google_cloud_run_service" "agent" {
      name     = "strands-agent"
      location = var.gcp_region

      template {
        spec {
          containers {
            image = var.agent_image
            env {
              name  = "OPENAI_API_KEY"
              value = var.openai_api_key
            }
            env {
              name  = "GOOGLE_GENAI_USE_VERTEXAI"
              value = "false"
            }
            env {
              name  = "GOOGLE_API_KEY"
              value = var.google_api_key
            }
          }
        }
      }
    }

    resource "google_cloud_run_service_iam_member" "public" {
      service  = google_cloud_run_service.agent.name
      location = google_cloud_run_service.agent.location
      role     = "roles/run.invoker"
      member   = "allUsers"
    }
    ```
    
    Create `variables.tf`

    ```hcl
    variable "gcp_project" {
      description = "GCP project ID"
      type        = string
    }

    variable "gcp_region" {
      description = "GCP region"
      type        = string
      default     = "us-central1"
    }

    variable "agent_image" {
      description = "Container image for Strands agent"
      type        = string
    }

    variable "openai_api_key" {
      description = "OpenAI API key"
      type        = string
      sensitive   = true
    }

    variable "google_api_key" {
      description = "Google API key"
      type        = string
      sensitive   = true
    }
    ```

    Create `outputs.tf`

    ```hcl
    output "agent_url" {
      description = "Google Cloud Run service URL"
      value       = google_cloud_run_service.agent.status[0].url
    }
    ```
  
=== "Azure Container Instances"

    <details>
      <summary>
        <strong>Optional: Open Azure Container Instances Setup All-in-One Bash Command</strong><br>
        <sub>Copy and paste this bash script to create all necessary terraform files and skip remaining "Cloud Deployment Setup" steps below:</sub>
      </summary>

    ```bash
    generate_azure_container_instance_terraform() {
        mkdir -p terraform
        
        # Generate main.tf
        cat > terraform/main.tf << 'EOF'
    terraform {
      required_providers {
        azurerm = {
          source  = "hashicorp/azurerm"
          version = "~> 3.0"
        }
      }
    }

    provider "azurerm" {
      features {}
    }

    data "azurerm_container_registry" "acr" {
      name                = var.acr_name
      resource_group_name = var.acr_resource_group
    }

    resource "azurerm_resource_group" "main" {
      name     = "strands-agent"
      location = var.azure_location
    }

    resource "azurerm_container_group" "agent" {
      name                = "strands-agent"
      location            = azurerm_resource_group.main.location
      resource_group_name = azurerm_resource_group.main.name
      ip_address_type     = "Public"
      os_type             = "Linux"

      image_registry_credential {
        server   = "${var.acr_name}.azurecr.io"
        username = var.acr_name
        password = data.azurerm_container_registry.acr.admin_password
      }

      container {
        name   = "agent"
        image  = var.agent_image
        cpu    = "0.5"
        memory = "1.5"

        ports {
          port = 8080
        }

        environment_variables = {
          OPENAI_API_KEY = var.openai_api_key
        }
      }
    }
    EOF

        # Generate variables.tf
        cat > terraform/variables.tf << 'EOF'
    variable "azure_location" {
      description = "Azure location"
      type        = string
      default     = "East US"
    }

    variable "agent_image" {
      description = "Container image for Strands agent"
      type        = string
    }

    variable "openai_api_key" {
      description = "OpenAI API key"
      type        = string
      sensitive   = true
    }

    variable "acr_name" {
      description = "Azure Container Registry name"
      type        = string
    }

    variable "acr_resource_group" {
      description = "Azure Container Registry resource group"
      type        = string
    }
    EOF

        # Generate outputs.tf
        cat > terraform/outputs.tf << 'EOF'
    output "agent_url" {
      description = "Azure Container Instance URL"
      value       = "http://${azurerm_container_group.agent.ip_address}:8080"
    }
    EOF

        # Generate terraform.tfvars template
        cat > terraform/terraform.tfvars << 'EOF'
    agent_image = "your-registry.azurecr.io/my-image:latest"
    openai_api_key = "<your-openai-api-key>"
    acr_name = "<your-acr-name>"
    acr_resource_group = "<your-resource-group>"
    EOF

        echo "✅ Azure Container Instance Terraform files generated in terraform/ directory"
    }

    generate_azure_container_instance_terraform
    ```
    
    </details>

    **Step by Step Guide**

    Create terraform directory

    ```bash
    mkdir terraform
    cd terraform
    ```

    Create `main.tf`

    ```hcl
    terraform {
      required_providers {
        azurerm = {
          source  = "hashicorp/azurerm"
          version = "~> 3.0"
        }
      }
    }

    provider "azurerm" {
      features {}
    }

    data "azurerm_container_registry" "acr" {
      name                = var.acr_name
      resource_group_name = var.acr_resource_group
    }

    resource "azurerm_resource_group" "main" {
      name     = "strands-agent"
      location = var.azure_location
    }

    resource "azurerm_container_group" "agent" {
      name                = "strands-agent"
      location            = azurerm_resource_group.main.location
      resource_group_name = azurerm_resource_group.main.name
      ip_address_type     = "Public"
      os_type             = "Linux"

      image_registry_credential {
        server   = "${var.acr_name}.azurecr.io"
        username = var.acr_name
        password = data.azurerm_container_registry.acr.admin_password
      }

      container {
        name   = "agent"
        image  = var.agent_image
        cpu    = "0.5"
        memory = "1.5"

        ports {
          port = 8080
        }

        environment_variables = {
          OPENAI_API_KEY = var.openai_api_key
        }
      }
    }
    ```

    Create `variables.tf`

    ```hcl
    variable "azure_location" {
      description = "Azure location"
      type        = string
      default     = "East US"
    }

    variable "agent_image" {
      description = "Container image for Strands agent"
      type        = string
    }

    variable "openai_api_key" {
      description = "OpenAI API key"
      type        = string
      sensitive   = true
    }

    variable "acr_name" {
      description = "Azure Container Registry name"
      type        = string
    }

    variable "acr_resource_group" {
      description = "Azure Container Registry resource group"
      type        = string
    }
    ```

    Create `output.tf`

    ```hcl
    output "agent_url" {
      description = "Azure Container Instance URL"
      value       = "http://${azurerm_container_group.agent.ip_address}:8080"
    }
    ```

## Step 3: Configure Variables

Update `terraform/terraform.tfvars` based on your chosen provider:

=== "AWS App Runner"

    ```hcl
    agent_image = "your-account.dkr.ecr.us-east-1.amazonaws.com/my-image:latest"
    openai_api_key = "<your-openai-api-key>"
    ```

    This example uses OpenAI, but any supported model provider can be configured. See the [Strands documentation](https://strandsagents.com/latest/documentation/docs/user-guide/concepts/model-providers) for all supported model providers. 


    **Note:** Bedrock model provider credentials are automatically passed using App Runner's IAM role and do not need to be specified in Terraform.

=== "AWS Lambda"

    ```hcl
    agent_image = "your-account.dkr.ecr.us-east-1.amazonaws.com/my-image:latest"
    openai_api_key = "<your-openai-api-key>"
    ```

    This example uses OpenAI, but any supported model provider can be configured. See the [Strands documentation](https://strandsagents.com/latest/documentation/docs/user-guide/concepts/model-providers) for all supported model providers.

    
    **Note:** Bedrock model provider credentials are automatically passed using Lambda's IAM role and do not need to be specified in Terraform.

=== "Google Cloud Run"

    ```hcl
    gcp_project = "your-project-id"
    agent_image = "gcr.io/your-project/my-image:latest"
    openai_api_key = "<your-openai-api-key>"
    ```

    This example uses OpenAI, but any supported model provider can be configured. See the [Strands documentation](https://strandsagents.com/latest/documentation/docs/user-guide/concepts/model-providers) for all supported model providers. For instance, to use Bedrock model provider credentials:

    ```hcl
    aws_access_key_id = "<your-aws-access-key-id>"
    aws_secret_access_key = "<your-aws-secret-key>"
    ```

=== "Azure Container Instances"

    ```hcl
    agent_image = "your-registry.azurecr.io/my-image:latest"
    openai_api_key = "<your-openai-api-key>"
    acr_name = "<your-registry>"
    acr_resource_group = "<your-resource-group>"
    ```

    This example uses OpenAI, but any supported model provider can be configured. See the [Strands documentation](https://strandsagents.com/latest/documentation/docs/user-guide/concepts/model-providers) for all supported model providers. For instance, to use Bedrock model provider credentials:

    ```hcl
    aws_access_key_id = "<your-aws-access-key-id>"
    aws_secret_access_key = "<your-aws-secret-key>"
    ```

## Step 4: Deploy Infrastructure

```bash

# Initialize Terraform
terraform init

# Review the deployment plan
terraform plan

# Deploy the infrastructure
terraform apply

# Get the endpoints
terraform output
```

## Step 5: Test Your Deployment

Test the endpoints using the output URLs:

```bash
# Health check
curl http://<your-service-url>/ping

# Test agent invocation
curl -X POST http://<your-service-url>/invocations \
  -H "Content-Type: application/json" \
  -d '{"input": {"prompt": "What is artificial intelligence?"}}'
```

## Step 6: Making Changes

When you modify your code, redeploy with:

```bash
# Rebuild and push image
docker build -t <your-registry>/my-image:latest .
docker push <your-registry>/my-image:latest

# Update infrastructure
terraform apply
```

## Cleanup

Remove the infrastructure when done:

```bash
terraform destroy
```

## Additional Resources

- [Strands Docker Deploy Documentation](../deploy_to_docker)
- [Terraform Documentation](https://www.terraform.io/docs/)
- [Terraform AWS Provider](https://registry.terraform.io/providers/hashicorp/aws/latest/docs)
- [Terraform Google Provider](https://registry.terraform.io/providers/hashicorp/google/latest/docs)
- [Terraform Azure Provider](https://registry.terraform.io/providers/hashicorp/azurerm/latest/docs)
