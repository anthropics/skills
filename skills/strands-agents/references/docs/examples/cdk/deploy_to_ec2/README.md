# AWS CDK EC2 Deployment Example

## Introduction

This is a TypeScript-based CDK (Cloud Development Kit) example that demonstrates how to deploy a Python application to AWS EC2. The example deploys a weather forecaster application that runs as a service on an EC2 instance. The application provides two weather endpoints:

1. `/weather` - A standard endpoint that returns weather information based on the provided prompt
2. `/weather-streaming` - A streaming endpoint that delivers weather information in real-time as it's being generated

## Prerequisites

- [AWS CLI](https://aws.amazon.com/cli/) installed and configured
- [Node.js](https://nodejs.org/) (v18.x or later)
- Python 3.12 or later

## Project Structure

- `lib/` - Contains the CDK stack definition in TypeScript
- `bin/` - Contains the CDK app entry point and deployment scripts:
  - `cdk-app.ts` - Main CDK application entry point
- `app/` - Contains the application code:
  - `app.py` - FastAPI application code
- `requirements.txt` - Python dependencies for the application

## Setup and Deployment

1. Install dependencies:

```bash
# Install Node.js dependencies including CDK and TypeScript locally
npm install

# Create a Python virtual environment (optional but recommended)
python -m venv .venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate

# Install Python dependencies for the local development
pip install -r ./requirements.txt

# Install Python dependencies for the app distribution
pip install -r requirements.txt --python-version 3.12 --platform manylinux2014_aarch64 --target ./packaging/_dependencies --only-binary=:all:
```

2. Bootstrap your AWS environment (if not already done):

```bash
npx cdk bootstrap
```

3. Deploy the stack:

```bash
npx cdk deploy
```

## How It Works

This deployment:

1. Creates an EC2 instance in a public subnet with a public IP
2. Uploads the application code to S3 as CDK assets
3. Uses a user data script to:
   - Install Python and other dependencies
   - Download the application code from S3
   - Set up the application as a systemd service using uvicorn

## Usage

After deployment, you can access the weather service using the Application Load Balancer URL that is output after deployment:

```bash
# Get the service URL from the CDK output
SERVICE_URL=$(aws cloudformation describe-stacks --stack-name AgentEC2Stack --region us-east-1 --query "Stacks[0].Outputs[?ExportName=='Ec2ServiceEndpoint'].OutputValue" --output text)
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

## Local testing

You can run the python app directly for local testing via:

```bash
python app/app.py
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

## Callouts and considerations

Note that this example demonstrates a simple deployment approach with some important limitations:

- The application code is deployed only during the initial instance creation via user data script
- Updating the application requires implementing a custom update mechanism
- The example exposes the application directly on port 8000 without a load balancer
- For production workloads, consider using ECS/Fargate/App Runner which provides built-in support for application updates, scaling, and high availability


## Additional Resources

- [AWS CDK TypeScript Documentation](https://docs.aws.amazon.com/cdk/latest/guide/work-with-cdk-typescript.html)
- [Amazon EC2 Documentation](https://docs.aws.amazon.com/ec2/)
- [FastAPI Documentation](https://fastapi.tiangolo.com/)
- [TypeScript Documentation](https://www.typescriptlang.org/docs/)
