# Python Deployment to Docker

This guide covers deploying Python-based Strands agents using Docker for for local and cloud development.

## Prerequisites

- Python 3.10+
- [Docker](https://www.docker.com/) installed and running
- Model provider credentials

---

## Quick Start Setup

Install uv:
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

Configure Model Provider Credentials:
```bash
export OPENAI_API_KEY='<your-api-key>'
```

**Note**: This example uses OpenAI, but any supported model provider can be configured. See the [Strands documentation](https://strandsagents.com/latest/documentation/docs/user-guide/concepts/model-providers) for all supported model providers.

For instance, to configure AWS credentials:
```bash
  export AWS_ACCESS_KEY_ID=<'your-access-key-id'>
  export AWS_SECRET_ACCESS_KEY='<your-secret-access-key'>
```

### Project Setup

<details>
  <summary>
    <strong>Open Quick Setup All-in-One Bash Command</strong><br>
    <sub>Optional: Copy and paste this bash command to create your project with all necessary files and skip remaining "Project Setup" steps below:</sub>
  </summary>

```bash
setup_agent() {
mkdir my-python-agent && cd my-python-agent
uv init --python 3.11
uv add fastapi "uvicorn[standard]" pydantic strands-agents "strands-agents[openai]"

# Remove the auto-generated main.py
rm -f main.py

cat > agent.py << 'EOF'
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
from typing import Dict, Any
from datetime import datetime, timezone
from strands import Agent
from strands.models.openai import OpenAIModel

app = FastAPI(title="Strands Agent Server", version="1.0.0")

# Note: Any supported model provider can be configured
# Automatically uses process.env.OPENAI_API_KEY
model = OpenAIModel(model_id="gpt-4o")

strands_agent = Agent(model=model)

class InvocationRequest(BaseModel):
    input: Dict[str, Any]

class InvocationResponse(BaseModel):
    output: Dict[str, Any]

@app.post("/invocations", response_model=InvocationResponse)
async def invoke_agent(request: InvocationRequest):
    try:
        user_message = request.input.get("prompt", "")
        if not user_message:
            raise HTTPException(
                status_code=400,
                detail="No prompt found in input. Please provide a 'prompt' key in the input."
            )

        result = strands_agent(user_message)
        response = {
            "message": result.message,
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "model": "strands-agent",
        }

        return InvocationResponse(output=response)

    except Exception as e:
        raise HTTPException(status_code=500, detail=f"Agent processing failed: {str(e)}")

@app.get("/ping")
async def ping():
    return {"status": "healthy"}

def main():
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8080)

if __name__ == "__main__":
    main()
EOF

cat > Dockerfile << 'EOF'
# Use uv's Python base image
FROM ghcr.io/astral-sh/uv:python3.11-bookworm-slim

WORKDIR /app

# Copy uv files
COPY pyproject.toml uv.lock ./

# Install dependencies
RUN uv sync --frozen --no-cache

# Copy agent file
COPY agent.py ./

# Expose port
EXPOSE 8080

# Run application
CMD ["uv", "run", "python", "agent.py"]
EOF

echo "Setup complete! Project created in my-python-agent/"
}

setup_agent

```

</details>

Step 1: Create project directory and initialize
```bash
mkdir my-python-agent && cd my-python-agent
uv init --python 3.11
```

Step 2: Add dependencies
```bash
uv add fastapi "uvicorn[standard]" pydantic strands-agents "strands-agents[openai]"
```

Step 3: Create agent.py
```python
--8<-- "user-guide/deploy/deploy_to_docker/imports.py:imports"
--8<-- "user-guide/deploy/deploy_to_docker/agent.py:agent"
```

Step 4: Create Dockerfile
```dockerfile
# Use uv's Python base image
FROM ghcr.io/astral-sh/uv:python3.11-bookworm-slim

WORKDIR /app

# Copy uv files
COPY pyproject.toml uv.lock ./

# Install dependencies
RUN uv sync --frozen --no-cache

# Copy agent file
COPY agent.py ./

# Expose port
EXPOSE 8080

# Run application
CMD ["uv", "run", "python", "agent.py"]
```


Your project structure will now look like:
```
my-python-agent/
├── agent.py                # FastAPI application
├── Dockerfile              # Container configuration
├── pyproject.toml          # Created by uv init
└── uv.lock                 # Created automatically by uv
```

### Test Locally

Before deploying with Docker, test your application locally:

```bash
# Run the application
uv run python agent.py

# Test /ping endpoint
curl http://localhost:8080/ping

# Test /invocations endpoint
curl -X POST http://localhost:8080/invocations \
  -H "Content-Type: application/json" \
  -d '{ 
    "input": {"prompt": "What is artificial intelligence?"}
  }'
```

## Deploy to Docker

### Step 1: Build Docker Image

Build your Docker image:
```bash
docker build -t my-agent-image:latest .
```

### Step 2: Run Docker Container

Run the container with model provider credentials:
```bash
docker run -p 8080:8080 \
  -e OPENAI_API_KEY=$OPENAI_API_KEY \
  my-agent-image:latest
```

This example uses OpenAI credentials by default, but any model provider credentials can be passed as environment variables when running the image. For instance, to pass AWS credentials:
```bash
docker run -p 8080:8080 \
  -e AWS_ACCESS_KEY_ID=$AWS_ACCESS_KEY_ID \
  -e AWS_SECRET_ACCESS_KEY=$AWS_SECRET_ACCESS_KEY \
  -e AWS_REGION=us-east-1 \
  my-agent-image:latest
```

### Step 3: Test Your Deployment

Test the endpoints:
```bash
# Health check
curl http://localhost:8080/ping

# Test agent invocation
curl -X POST http://localhost:8080/invocations \
  -H "Content-Type: application/json" \
  -d '{"input": {"prompt": "What is artificial intelligence?"}}'
```

### Step 4: Making Changes

When you modify your code, rebuild and run:

```bash
# Rebuild image
docker build -t my-agent-image:latest .

# Stop existing container (if running)
docker stop $(docker ps -q --filter ancestor=my-agent-image:latest)

# Run new container
docker run -p 8080:8080 \
  -e OPENAI_API_KEY=$OPENAI_API_KEY \
  my-agent-image:latest
```

## Troubleshooting

- **Container not starting**: Check logs with `docker logs $(docker ps -q --filter ancestor=my-agent-image:latest)`
- **Connection refused**: Verify app is listening on 0.0.0.0:8080
- **Image build fails**: Check `pyproject.toml` and dependencies
- **Port already in use**: Use different port mapping `-p 8081:8080`


## Docker Compose for Local Development

**Optional**: Docker Compose is only recommended for local development. Most cloud service providers only support raw Docker commands, not Docker Compose.

For local development and testing, Docker Compose provides a more convenient way to manage your container:

```yaml
# Example for OpenAI
version: '3.8'
services:
  my-python-agent:
    build: .
    ports:
      - "8080:8080"
    environment:
      - OPENAI_API_KEY=<your-api-key>
```

Run with Docker Compose:
```bash
# Start services
docker-compose up --build

# Run in background
docker-compose up -d --build

# Stop services
docker-compose down
```

## Optional: Deploy to Cloud Container Service

Once your application works locally with Docker, you can deploy it to any cloud-hosted container service. The Docker container you've created is the foundation for deploying to the cloud platform of your choice (AWS, GCP, Azure, etc).

Our other deployment guides build on this Docker foundation to show you how to deploy to specific cloud services:

- [Amazon Bedrock AgentCore](../deploy_to_bedrock_agentcore/python.md) - Deploy to AWS with Bedrock integration
- [AWS Fargate](../deploy_to_aws_fargate.md) - Deploy to AWS's managed container service
- [Amazon EKS](../deploy_to_amazon_eks.md) - Deploy to Kubernetes on AWS
- [Amazon EC2](../deploy_to_amazon_ec2.md) - Deploy directly to EC2 instances


## Additional Resources

- [Strands Documentation](https://strandsagents.com/latest/)
- [Docker Documentation](https://docs.docker.com/)
- [uv Documentation](https://docs.astral.sh/uv/)
- [FastAPI Documentation](https://fastapi.tiangolo.com/)
- [Python Docker Guide](https://docs.docker.com/guides/python/)