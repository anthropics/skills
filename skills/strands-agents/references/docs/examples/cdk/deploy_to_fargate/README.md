# AWS CDK Fargate Deployment Example

## Introduction

This is a TypeScript-based CDK (Cloud Development Kit) example that demonstrates how to deploy a Python application to AWS Fargate. The example deploys a weather forecaster application that runs as a containerized service in AWS Fargate with an Application Load Balancer. The application is built with FastAPI and provides two weather endpoints:

1. `/weather` - A standard endpoint that returns weather information based on the provided prompt
2. `/weather-streaming` - A streaming endpoint that delivers weather information in real-time as it's being generated

## Prerequisites

- [AWS CLI](https://aws.amazon.com/cli/) installed and configured
- [Node.js](https://nodejs.org/) (v18.x or later)
- Python 3.12 or later
- Either:
  - [Podman](https://podman.io/) installed and running
  - (or) [Docker](https://www.docker.com/) installed and running
## Project Structure

- `lib/` - Contains the CDK stack definition in TypeScript
- `bin/` - Contains the CDK app entry point and deployment scripts:
  - `cdk-app.ts` - Main CDK application entry point
- `docker/` - Contains the Dockerfile and application code for the container:
  - `Dockerfile` - Docker image definition
  - `app/` - Application code
  - `requirements.txt` - Python dependencies for the container & local development

## Setup and Deployment

1. Install dependencies:

```bash
# Install Node.js dependencies including CDK and TypeScript locally
npm install

# Create a Python virtual environment (optional but recommended)
python -m venv .venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate

# Install Python dependencies for the local development
pip install -r ./docker/requirements.txt
```

2. Bootstrap your AWS environment (if not already done):

```bash
npx cdk bootstrap
```

3. Ensure podman is started (one time):

```bash
podman machine init
podman machine start
```

4. Package & deploy via CDK:

```bash
CDK_DOCKER=podman npx cdk deploy
```

## Usage

After deployment, you can access the weather service using the Application Load Balancer URL that is output after deployment:

```bash
# Get the service URL from the CDK output
SERVICE_URL=$(aws cloudformation describe-stacks --stack-name AgentFargateStack --query "Stacks[0].Outputs[?ExportName=='AgentServiceEndpoint'].OutputValue" --output text)
```

The service exposes a REST API endpoint that you can call using curl or any HTTP client:

```bash


# Call the weather service
curl -X POST \
  http://$SERVICE_URL/weather \
  -H 'Content-Type: application/json' \
  -d '{"prompt": "What is the weather in New York?"}'
  
 # Call the streaming endpoint
 curl -X POST \
  http://$SERVICE_URL/weather-streaming \
  -H 'Content-Type: application/json' \
  -d '{"prompt": "What is the weather in New York in Celsius?"}'
```

## Local testing (python)

You can run the python app directly for local testing via:

```bash
python ./docker/app/app.py
```

Then, set the SERVICE_URL to point to your local server

```bash
SERVICE_URL=127.0.0.1:8000
```

and you can use the curl commands above to test locally.

## Local testing (container)

Build & run the container:

```bash
podman build ./docker/ -t agent_container
podman run -p 127.0.0.1:8000:8000 -t agent_container
```

Then, set the SERVICE_URL to point to your local server

```bash
SERVICE_URL=127.0.0.1:8000
```

and you can use the curl commands above to test locally.

## Cleanup

To remove all resources created by this example:

```bash
npx cdk destroy
```

## Additional Resources

- [AWS CDK TypeScript Documentation](https://docs.aws.amazon.com/cdk/latest/guide/work-with-cdk-typescript.html)
- [AWS Fargate Documentation](https://docs.aws.amazon.com/AmazonECS/latest/developerguide/AWS_Fargate.html)
- [Docker Documentation](https://docs.docker.com/)
- [TypeScript Documentation](https://www.typescriptlang.org/docs/)
