# Python Deployment to Amazon Bedrock AgentCore Runtime

This guide covers deploying Python-based Strands agents to [Amazon Bedrock AgentCore Runtime](index.md).

## Prerequisites

- Python 3.10+
- AWS account with appropriate [permissions](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/runtime-permissions.html)
- Optional: A container engine (Docker, Finch, or Podman) - only required for local testing and advanced deployment scenarios

---

## Choose Your Deployment Approach

> ⚠️ **Important**: Choose the approach that best fits your use case. You only need to follow ONE of the two approaches below.

### 🚀 SDK Integration

**[Option A: SDK Integration](#option-a-sdk-integration)**

- **Use when**: You want to quickly deploy existing agent functions
- **Best for**: Simple agents, prototyping, minimal setup
- **Benefits**: Automatic HTTP server setup, built-in deployment tools
- **Trade-offs**: Less control over server configuration

### 🔧 Custom Implementation

**[Option B: Custom Agent](#option-b-custom-agent)**

- **Use when**: You need full control over your agent's HTTP interface
- **Best for**: Complex agents, custom middleware, production systems
- **Benefits**: Complete FastAPI control, custom routing, advanced features
- **Trade-offs**: More setup required, manual server configuration

---

## Option A: SDK Integration

The AgentCore Runtime Python SDK provides a lightweight wrapper that helps you deploy your agent functions as HTTP services.

### Step 1: Install the SDK

```bash
pip install bedrock-agentcore
```

### Step 2: Prepare Your Agent Code

Basic Setup (3 simple steps)

Import the runtime

```python
from bedrock_agentcore.runtime import BedrockAgentCoreApp
```

Initialize the app

```python
app = BedrockAgentCoreApp()
```

Decorate your function

```python
@app.entrypoint
def invoke(payload):
    # Your existing code remains unchanged
    return payload

if __name__ == "__main__":
    app.run()
```

Complete Examples

- Basic Example

```python
from bedrock_agentcore.runtime import BedrockAgentCoreApp
from strands import Agent

app = BedrockAgentCoreApp()
agent = Agent()

@app.entrypoint
def invoke(payload):
    """Process user input and return a response"""
    user_message = payload.get("prompt", "Hello")
    result = agent(user_message)
    return {"result": result.message}

if __name__ == "__main__":
    app.run()
```

- Streaming Example

```python
from strands import Agent
from bedrock_agentcore import BedrockAgentCoreApp

app = BedrockAgentCoreApp()
agent = Agent()

@app.entrypoint
async def agent_invocation(payload):
    """Handler for agent invocation"""
    user_message = payload.get(
        "prompt", "No prompt found in input, please guide customer to create a json payload with prompt key"
    )
    stream = agent.stream_async(user_message)
    async for event in stream:
        print(event)
        yield (event)

if __name__ == "__main__":
    app.run()
```

### Step 3: Test Locally

```bash
python my_agent.py

# Test with curl:
curl -X POST http://localhost:8080/invocations \
-H "Content-Type: application/json" \
-d '{"prompt": "Hello world!"}'
```

### Step 4: Choose Your Deployment Method

> **Choose ONE of the following deployment methods:**

#### Method A: Starter Toolkit (For quick prototyping)

For quick prototyping with automated deployment:

```bash
pip install bedrock-agentcore-starter-toolkit
```

Project Structure

```
your_project_directory/
├── agent_example.py # Your main agent code
├── requirements.txt # Dependencies for your agent
└── __init__.py # Makes the directory a Python package
```

Example: agent_example.py

```python
from strands import Agent
from bedrock_agentcore.runtime import BedrockAgentCoreApp

agent = Agent()
app = BedrockAgentCoreApp()

@app.entrypoint
def invoke(payload):
    """Process user input and return a response"""
    user_message = payload.get("prompt", "Hello")
    response = agent(user_message)
    return str(response) # response should be json serializable

if __name__ == "__main__":
    app.run()
```

Example: requirements.txt

```
strands-agents
bedrock-agentcore
```

Deploy with Starter Toolkit

```bash
# Configure your agent
agentcore configure --entrypoint agent_example.py

# Optional: Local testing (requires Docker, Finch, or Podman)
agentcore launch --local

# Deploy to AWS
agentcore launch

# Test your agent with CLI
agentcore invoke '{"prompt": "Hello"}'
```

> **Note**: The `agentcore launch --local` command requires a container engine (Docker, Finch, or Podman) for local deployment testing. This step is optional - you can skip directly to `agentcore launch` for AWS deployment if you don't need local testing.

#### Method B: Manual Deployment with boto3

For more control over the deployment process:

1. Package your code as a container image and push it to ECR
2. Create your agent using CreateAgentRuntime:

```python
import boto3

# Create the client
client = boto3.client('bedrock-agentcore-control', region_name="us-east-1")

# Call the CreateAgentRuntime operation
response = client.create_agent_runtime(
    agentRuntimeName='hello-strands',
    agentRuntimeArtifact={
        'containerConfiguration': {
            # Your ECR image Uri
            'containerUri': '123456789012.dkr.ecr.us-east-1.amazonaws.com/my-agent:latest'
        }
    },
    networkConfiguration={"networkMode":"PUBLIC"},
    # Your AgentCore Runtime role arn
    roleArn='arn:aws:iam::123456789012:role/AgentRuntimeRole'
)
```

Invoke Your Agent

```python
import boto3
import json

# Initialize the AgentCore Runtime client
agent_core_client = boto3.client('bedrock-agentcore')

# Prepare the payload
payload = json.dumps({"prompt": prompt}).encode()

# Invoke the agent
response = agent_core_client.invoke_agent_runtime(
    agentRuntimeArn=agent_arn, # you will get this from deployment
    runtimeSessionId=session_id, # you will get this from deployment
    payload=payload
)
```

>📊 Next Steps: Set Up Observability (Optional)
> 
> **⚠️ IMPORTANT**: Your agent is deployed, you could also set up [Observability](#observability-enablement)


---

## Option B: Custom Agent

> **This section is complete** - follow all steps below if you choose the custom agent approach.

This approach demonstrates how to deploy a custom agent using FastAPI and Docker, following AgentCore Runtime requirements.

**Requirements**

- **FastAPI Server**: Web server framework for handling requests
- **`/invocations` Endpoint**: POST endpoint for agent interactions (REQUIRED)
- **`/ping` Endpoint**: GET endpoint for health checks (REQUIRED)
- **Container Engine**: Docker, Finch, or Podman (required for this example)
- **Docker Container**: ARM64 containerized deployment package

### Step 1: Quick Start Setup

Install uv

```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

Create Project

```bash
mkdir my-custom-agent && cd my-custom-agent
uv init --python 3.11
uv add fastapi 'uvicorn[standard]' pydantic httpx strands-agents
```

Project Structure example

```
my-custom-agent/
├── agent.py                 # FastAPI application
├── Dockerfile               # ARM64 container configuration
├── pyproject.toml          # Created by uv init
└── uv.lock                 # Created automatically by uv
```

### Step 2: Prepare your agent code

Example: agent.py

```python
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
from typing import Dict, Any
from datetime import datetime,timezone
from strands import Agent

app = FastAPI(title="Strands Agent Server", version="1.0.0")

# Initialize Strands agent
strands_agent = Agent()

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

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8080)
```

### Step 3: Test Locally

```bash
# Run the application
uv run uvicorn agent:app --host 0.0.0.0 --port 8080

# Test /ping endpoint
curl http://localhost:8080/ping

# Test /invocations endpoint
curl -X POST http://localhost:8080/invocations \
  -H "Content-Type: application/json" \
  -d '{
    "input": {"prompt": "What is artificial intelligence?"}
  }'
```

### Step 4: Prepare your docker image

Create docker file

```dockerfile
# Use uv's ARM64 Python base image
FROM --platform=linux/arm64 ghcr.io/astral-sh/uv:python3.11-bookworm-slim

WORKDIR /app

# Copy uv files
COPY pyproject.toml uv.lock ./

# Install dependencies (including strands-agents)
RUN uv sync --frozen --no-cache

# Copy agent file
COPY agent.py ./

# Expose port
EXPOSE 8080

# Run application
CMD ["uv", "run", "uvicorn", "agent:app", "--host", "0.0.0.0", "--port", "8080"]
```

Setup Docker buildx

```bash
docker buildx create --use
```

Build and Test Locally

```bash
# Build the image
docker buildx build --platform linux/arm64 -t my-agent:arm64 --load .

# Test locally with credentials
docker run --platform linux/arm64 -p 8080:8080 \
  -e AWS_ACCESS_KEY_ID="$AWS_ACCESS_KEY_ID" \
  -e AWS_SECRET_ACCESS_KEY="$AWS_SECRET_ACCESS_KEY" \
  -e AWS_SESSION_TOKEN="$AWS_SESSION_TOKEN" \
  -e AWS_REGION="$AWS_REGION" \
  my-agent:arm64
```

Deploy to ECR

```bash
# Create ECR repository
aws ecr create-repository --repository-name my-strands-agent --region us-west-2

# Login to ECR
aws ecr get-login-password --region us-west-2 | docker login --username AWS --password-stdin <account-id>.dkr.ecr.us-west-2.amazonaws.com

# Build and push to ECR
docker buildx build --platform linux/arm64 -t <account-id>.dkr.ecr.us-west-2.amazonaws.com/my-strands-agent:latest --push .

# Verify the image
aws ecr describe-images --repository-name my-strands-agent --region us-west-2
```

### Step 5: Deploy Agent Runtime

Example: deploy_agent.py

```python
import boto3

client = boto3.client('bedrock-agentcore-control')

response = client.create_agent_runtime(
    agentRuntimeName='strands_agent',
    agentRuntimeArtifact={
        'containerConfiguration': {
            'containerUri': '<account-id>.dkr.ecr.us-west-2.amazonaws.com/my-strands-agent:latest'
        }
    },
    networkConfiguration={"networkMode": "PUBLIC"},
    roleArn='arn:aws:iam::<account-id>:role/AgentRuntimeRole'
)

print(f"Agent Runtime created successfully!")
print(f"Agent Runtime ARN: {response['agentRuntimeArn']}")
print(f"Status: {response['status']}")
```

Execute python file

```bash
uv run deploy_agent.py
```

### Step 6: Invoke Your Agent

Example: invoke_agent.py

```python
import boto3
import json

agent_core_client = boto3.client('bedrock-agentcore', region_name='us-west-2')
payload = json.dumps({
    "input": {"prompt": "Explain machine learning in simple terms"}
})

response = agent_core_client.invoke_agent_runtime(
    agentRuntimeArn='arn:aws:bedrock-agentcore:us-west-2:<account-id>:runtime/myStrandsAgent-suffix',
    runtimeSessionId='dfmeoagmreaklgmrkleafremoigrmtesogmtrskhmtkrlshmt',  # Must be 33+ chars
    payload=payload,
    qualifier="DEFAULT"
)

response_body = response['response'].read()
response_data = json.loads(response_body)
print("Agent Response:", response_data)
```

Execute python file

```bash
uv run invoke_agent.py
```

Expected Response Format

```json
{
  "output": {
    "message": {
      "role": "assistant",
      "content": [
        {
          "text": "# Artificial Intelligence in Simple Terms\n\nArtificial Intelligence (AI) is technology that allows computers to do tasks that normally need human intelligence. Think of it as teaching machines to:\n\n- Learn from information (like how you learn from experience)\n- Make decisions based on what they've learned\n- Recognize patterns (like identifying faces in photos)\n- Understand language (like when I respond to your questions)\n\nInstead of following specific step-by-step instructions for every situation, AI systems can adapt to new information and improve over time.\n\nExamples you might use every day include voice assistants like Siri, recommendation systems on streaming services, and email spam filters that learn which messages are unwanted."
        }
      ]
    },
    "timestamp": "2025-07-13T01:48:06.740668",
    "model": "strands-agent"
  }
}
```

---

## Shared Information

> **This section applies to both deployment approaches** - reference as needed regardless of which option you chose.

### AgentCore Runtime Requirements Summary

- **Platform**: Must be linux/arm64
- **Endpoints**: `/invocations` POST and `/ping` GET are mandatory
- **ECR**: Images must be deployed to ECR
- **Port**: Application runs on port 8080
- **Strands Integration**: Uses Strands Agent for AI processing
- **Credentials**: Require AWS credentials for operation

### Best Practices

**Development**

- Test locally before deployment
- Use version control
- Keep dependencies updated

**Configuration**

- Use appropriate IAM roles
- Implement proper error handling
- Monitor agent performance

**Security**

- Follow the least privilege principle
- Secure sensitive information
- Regular security updates

### Troubleshooting

**Deployment Failures**

- Verify AWS credentials are configured correctly
- Check IAM role permissions
- Ensure container engine is running (for local testing with `agentcore launch --local` or Option B custom deployments)

**Runtime Errors**

- Check CloudWatch logs
- Verify environment variables
- Test agent locally first

**Container Issues**

- Verify container engine installation (Docker, Finch, or Podman)
- Check port configurations
- Review Dockerfile if customized

---

## Observability Enablement

Amazon Bedrock AgentCore provides built-in metrics to monitor your Strands agents. This section explains how to enable observability for your agents to view metrics, spans, and traces in CloudWatch.
> With AgentCore, you can also view metrics for agents that aren't running in the AgentCore runtime. Additional setup steps are required to configure telemetry outputs for non-AgentCore agents. See the instructions in [Configure Observability for agents hosted outside of the AgentCore runtime](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/observability-configure.html#observability-configure-3p) to learn more.

### Step 1: Enable CloudWatch Transaction Search

Before you can view metrics and traces, complete this one-time setup:

**Via AgentCore Console**

Look for the **"Enable Observability"** button when creating a memory resource

>If you don't see this button while configuring your agent (for example, if you don't create a memory resource in the console), you must enable observability manually by using the CloudWatch console to enable Transaction Search as described in the following procedure.

**Via CloudWatch Console**

1. Open the CloudWatch console
2. Navigate to Application Signals (APM) > Transaction search
3. Choose "Enable Transaction Search"
4. Select the checkbox to ingest spans as structured logs
5. Optionally adjust the X-Ray trace indexing percentage (default is 1%)
6. Choose Save

### Step 2: Add ADOT to Your Strands Agent

Add to your `requirements.txt`:
```text
aws-opentelemetry-distro>=0.10.1
boto3
```

Or install directly:
```bash
pip install aws-opentelemetry-distro>=0.10.1 boto3
```

Run With Auto-Instrumentation

- For SDK Integration (Option A):
```bash
opentelemetry-instrument python my_agent.py
```

- For Docker Deployment:
```dockerfile
CMD ["opentelemetry-instrument", "python", "main.py"]
```

- For Custom Agent (Option B):
```dockerfile
CMD ["opentelemetry-instrument", "uvicorn", "agent:app", "--host", "0.0.0.0", "--port", "8080"]
```

### Step 3: Viewing Your Agent's Observability Data

1. Open the CloudWatch console
2. Navigate to the GenAI Observability page
3. Find your agent service
4. View traces, metrics, and logs

### Session ID support

To propagate session ID, you need to invoke using session identifier in the OTEL baggage:
````python
from opentelemetry import baggage,context

ctx = baggage.set_baggage("session.id", session_id) # Set the session.id in baggage
context.attach(ctx)
````

### Enhanced AgentCore observability with custom headers (Optional)

You can invoke your agent with additional HTTP headers to provide enhanced observability options. The following example shows invocations including optional additional header requests for agents hosted in the AgentCore runtime.

```python
import boto3

def invoke_agent(agent_id, payload, session_id=None):
    client = boto3.client("bedrock-agentcore", region_name="us-west-2")
    response = client.invoke_agent_runtime(
        agentRuntimeArn=f"arn:aws:bedrock-agentcore:us-west-2:123456789012:runtime/{agent_id}",
        runtimeSessionId="12345678-1234-5678-9abc-123456789012",
        payload=payload
    )
    return response
```

Common Tracing Headers Examples:

| Header | Description | Sample Value |
|--------|-------------|-------------|
| `X-Amzn-Trace-Id` | X-Ray format trace ID | `Root=1-5759e988-bd862e3fe1be46a994272793;Parent=53995c3f42cd8ad8;Sampled=1` |
| `traceparent` | W3C standard tracing header | `00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01` |
| `X-Amzn-Bedrock-AgentCore-Runtime-Session-Id` | Session identifier | `aea8996f-dcf5-4227-b5ea-f9e9c1843729` |
| `baggage` | User-defined properties | `userId=alice,serverRegion=us-east-1` |

For more supported headers details, please check [Bedrock AgentCore Runtime Observability Configuration](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/observability-configure.html)

### Best Practices

- Use consistent session IDs across related requests
- Set appropriate sampling rates (1% is default)
- Monitor key metrics like latency, error rates, and token usage
- Set up CloudWatch alarms for critical thresholds

---

## Notes

- Keep your AgentCore Runtime and Strands packages updated for latest features and security fixes

## Additional Resources

- [Amazon Bedrock AgentCore Runtime Documentation](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/what-is-bedrock-agentcore.html)
- [Strands Documentation](https://strandsagents.com/latest/)
- [AWS IAM Documentation](https://docs.aws.amazon.com/IAM/latest/UserGuide/introduction.html)
- [Docker Documentation](https://docs.docker.com/)
- [Amazon Bedrock AgentCore Observability](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/observability.html)
