# Deploying Strands Agents SDK Agents to AWS App Runner

AWS App Runner is the easiest way to deploy web applications on AWS, including API services, backend web services, and websites. App Runner eliminates the need for infrastructure management or container orchestration by providing a fully managed platform with automatic integration and delivery pipelines, high performance, scalability, and security.

AWS App Runner automatically deploys containerized applications with secure HTTPS endpoints while handling infrastructure provisioning, auto-scaling, and TLS certificate management. This makes App Runner an excellent choice for deploying Strands Agents SDK agents as highly available and scalable containerized applications.

If you're not familiar with the AWS CDK, check out the [official documentation](https://docs.aws.amazon.com/cdk/v2/guide/home.html).

This guide discusses AWS App Runner integration at a high level - for a complete example project deploying to App Runner, check out the [`deploy_to_apprunner` sample project on GitHub][project_code].

## Creating Your Agent in Python

The core of your App Runner deployment is a containerized FastAPI application that hosts your Strands Agents SDK agent. This Python application initializes your agent and processes incoming HTTP requests.

The FastAPI application follows these steps:

1. Define endpoints for agent interactions
2. Create a Strands Agents SDK agent with the specified system prompt and tools
3. Process incoming requests through the agent
4. Return the response back to the client

Here's an example of a weather forecasting agent application ([`app.py`][app_py]):

```python
app = FastAPI(title="Weather API")

# Define a weather-focused system prompt
WEATHER_SYSTEM_PROMPT = """You are a weather assistant with HTTP capabilities. You can:

1. Make HTTP requests to the National Weather Service API
2. Process and display weather forecast data
3. Provide weather information for locations in the United States

When retrieving weather information:
1. First get the coordinates or grid information using https://api.weather.gov/points/{latitude},{longitude} or https://api.weather.gov/points/{zipcode}
2. Then use the returned forecast URL to get the actual forecast

When displaying responses:
- Format weather data in a human-readable way
- Highlight important information like temperature, precipitation, and alerts
- Handle errors appropriately
- Don't ask follow-up questions

Always explain the weather conditions clearly and provide context for the forecast.

At the point where tools are done being invoked and a summary can be presented to the user, invoke the ready_to_summarize
tool and then continue with the summary.
"""

class PromptRequest(BaseModel):
    prompt: str

@app.post('/weather')
async def get_weather(request: PromptRequest):
    """Endpoint to get weather information."""
    prompt = request.prompt
    
    if not prompt:
        raise HTTPException(status_code=400, detail="No prompt provided")

    try:
        weather_agent = Agent(
            system_prompt=WEATHER_SYSTEM_PROMPT,
            tools=[http_request],
        )
        response = weather_agent(prompt)
        content = str(response)
        return PlainTextResponse(content=content)
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
```

### Streaming responses

Streaming responses can significantly improve the user experience by providing real-time responses back to the customer. This is especially valuable for longer responses.

Python web-servers commonly implement streaming through the use of iterators, and the Strands Agents SDK facilitates response streaming via the `stream_async(prompt)` function:

```python
async def run_weather_agent_and_stream_response(prompt: str):
    """
    A helper function to yield summary text chunks one by one as they come in, allowing the web server to emit
    them to caller live
    """
    is_summarizing = False

    @tool
    def ready_to_summarize():
        """
        A tool that is intended to be called by the agent right before summarize the response.
        """
        nonlocal is_summarizing
        is_summarizing = True
        return "Ok - continue providing the summary!"

    weather_agent = Agent(
        system_prompt=WEATHER_SYSTEM_PROMPT,
        tools=[http_request, ready_to_summarize],
        callback_handler=None
    )

    async for item in weather_agent.stream_async(prompt):
        if not is_summarizing:
            continue
        if "data" in item:
            yield item['data']

@app.post('/weather-streaming')
async def get_weather_streaming(request: PromptRequest):
    """Endpoint to stream the weather summary as it comes it, not all at once at the end."""
    try:
        prompt = request.prompt

        if not prompt:
            raise HTTPException(status_code=400, detail="No prompt provided")

        return StreamingResponse(
            run_weather_agent_and_stream_response(prompt),
            media_type="text/plain"
        )
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
```

The implementation above employs a [custom tool](../concepts/tools/custom-tools.md) to mark the boundary between information gathering and summary generation phases. This approach ensures that only the final, user-facing content is streamed to the client, maintaining consistency with the non-streaming endpoint while providing the benefits of incremental response delivery.

## Containerization

To deploy your agent to App Runner, you need to containerize it using Podman or Docker. The Dockerfile defines how your application is packaged and run.  Below is an example Docker file that installs all needed dependencies, the application, and configures the FastAPI server to run via Uvicorn ([Dockerfile][dockerfile]):

```dockerfile
FROM public.ecr.aws/docker/library/python:3.12-slim

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    git \
    && rm -rf /var/lib/apt/lists/*

# Install Python dependencies
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy application code
COPY app/ .

# Create a non-root user to run the application
RUN useradd -m appuser
USER appuser

# Expose the port the app runs on
EXPOSE 8000

# Command to run the application with Uvicorn
# - port: 8000
CMD ["uvicorn", "app:app", "--host", "0.0.0.0", "--port", "8000", "--workers", "2"]
```

## Infrastructure

To deploy the containerized agent to App Runner using the TypeScript CDK, you need to define the infrastructure stack ([agent-apprunner-stack.ts][agent_apprunner_stack]). Much of the configuration follows standard App Runner deployment patterns, but the following code snippet highlights the key components specific to deploying Strands Agents SDK agents:

```typescript
// Create IAM role for App Runner instance
const instanceRole = new iam.Role(this, "AppRunnerInstanceRole", {
  assumedBy: new iam.ServicePrincipal("tasks.apprunner.amazonaws.com"),
});

// Add Bedrock permissions
instanceRole.addToPolicy(
  new iam.PolicyStatement({
    actions: ["bedrock:InvokeModel", "bedrock:InvokeModelWithResponseStream"],
    resources: ["*"],
  })
);

// Create IAM role for App Runner to access ECR
const accessRole = new iam.Role(this, "AppRunnerAccessRole", {
  assumedBy: new iam.ServicePrincipal("build.apprunner.amazonaws.com"),
  managedPolicies: [
    iam.ManagedPolicy.fromAwsManagedPolicyName(
      "service-role/AWSAppRunnerServicePolicyForECRAccess"
    ),
  ],
});

// Build Docker image for x86_64 (App Runner requirement)
const dockerAsset = new ecr_assets.DockerImageAsset(this, "AppRunnerImage", {
  directory: path.join(__dirname, "../docker"),
  platform: ecr_assets.Platform.LINUX_AMD64, // App Runner requires x86_64
});

// Grant App Runner access to pull the image
dockerAsset.repository.grantPull(accessRole);

// Create App Runner service
const service = new apprunner.CfnService(this, "AgentAppRunnerService", {
  serviceName: "agent-service",
  sourceConfiguration: {
    authenticationConfiguration: {
      accessRoleArn: accessRole.roleArn,
    },
    imageRepository: {
      imageIdentifier: dockerAsset.imageUri,
      imageRepositoryType: "ECR",
      imageConfiguration: {
        port: "8000",
        runtimeEnvironmentVariables: [
          {
            name: "LOG_LEVEL",
            value: "INFO",
          },
        ],
      },
    },
  },
  instanceConfiguration: {
    cpu: "1 vCPU",
    memory: "2 GB",
    instanceRoleArn: instanceRole.roleArn,
  },
  healthCheckConfiguration: {
    protocol: "HTTP",
    path: "/health",
    interval: 10,
    timeout: 5,
    healthyThreshold: 1,
    unhealthyThreshold: 5,
  },
});

// Output the service URL
this.exportValue(service.attrServiceUrl, {
  name: "AppRunnerServiceUrl",
  description: "The URL of the App Runner service",
});
```

The full example ([agent-apprunner-stack.ts][agent_apprunner_stack]):

1. Creates an instance role with permissions to invoke Bedrock APIs
2. Creates an access role for App Runner to pull images from ECR
3. Builds a Docker image for x86_64 architecture (App Runner requirement)
4. Configures the App Runner service with container settings (port 8000, environment variables)
5. Sets up instance configuration with 1 vCPU and 2 GB memory
6. Configures health checks to monitor service availability
7. Outputs the secure HTTPS service URL for accessing your application

## Deploying Your Agent & Testing

Assuming that Python & Node dependencies are already installed, run the CDK and deploy which will also run the Docker file for deployment:

```bash
# Bootstrap your AWS environment (if not already done)
npx cdk bootstrap

# Ensure Docker or Podman is running
podman machine start 

# Deploy the stack
CDK_DOCKER=podman npx cdk deploy  
```

Once deployed, you can test your agent using the Application Load Balancer URL:

```bash
# Get the service URL from the CDK output
SERVICE_URL=$(aws cloudformation describe-stacks --stack-name AgentAppRunnerStack --query "Stacks[0].Outputs[?ExportName=='AppRunnerServiceUrl'].OutputValue" --output text)

# Call the weather service
curl -X POST \
  https://$SERVICE_URL/weather \
  -H 'Content-Type: application/json' \
  -d '{"prompt": "What is the weather in New York?"}'
  
# Call the streaming endpoint
curl -X POST \
  https://$SERVICE_URL/weather-streaming \
  -H 'Content-Type: application/json' \
  -d '{"prompt": "What is the weather in New York in Celsius?"}'
```
## Summary

The above steps covered:

- Creating a FastAPI application that hosts your Strands Agents SDK agent
- Containerizing your application with Podman
- Creating the CDK infrastructure to deploy to App Runner
- Deploying the agent and infrastructure to an AWS account
- Manually testing the deployed service

## Complete Example

For the complete example code, including all files and configurations, see the [`deploy_to_apprunner` sample project on GitHub][project_code].

## Related Resources

- [AWS App Runner Documentation](https://docs.aws.amazon.com/apprunner/latest/dg/what-is-apprunner.html)
- [AWS CDK Documentation](https://docs.aws.amazon.com/cdk/v2/guide/home.html)
- [Podman Documentation](https://docs.podman.io/en/latest/)
- [FastAPI Documentation](https://fastapi.tiangolo.com/)

[project_code]: {{ docs_repo }}/docs/examples/cdk/deploy_to_apprunner
[app_py]: {{ docs_repo }}/docs/examples/cdk/deploy_to_apprunner/docker/app/app.py
[dockerfile]: {{ docs_repo }}/docs/examples/cdk/deploy_to_apprunner/docker/Dockerfile
[agent_apprunner_stack]: {{ docs_repo }}/docs/examples/cdk/deploy_to_apprunner/lib/agent-apprunner-stack.ts

