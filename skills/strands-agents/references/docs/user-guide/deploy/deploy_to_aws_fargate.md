# Deploying Strands Agents SDK Agents to AWS Fargate

AWS Fargate is a serverless compute engine for containers that works with Amazon ECS and EKS. It allows you to run containers without having to manage servers or clusters. This makes it an excellent choice for deploying Strands Agents SDK agents as containerized applications with high availability and scalability.

If you're not familiar with the AWS CDK, check out the [official documentation](https://docs.aws.amazon.com/cdk/v2/guide/home.html).

This guide discusses Fargate integration at a high level - for a complete example project deploying to Fargate, check out the [`deploy_to_fargate` sample project on GitHub][project_code].

## Creating Your Agent in Python

The core of your Fargate deployment is a containerized FastAPI application that hosts your Strands Agents SDK agent. This Python application initializes your agent and processes incoming HTTP requests.

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
    is_summarizing = False

    @tool
    def ready_to_summarize():
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

@app.route('/weather-streaming', methods=['POST'])
async def get_weather_streaming(request: PromptRequest):
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

The implementation above employs a [custom tool](../concepts/tools/custom-tools.md#creating-custom-tools) to mark the boundary between information gathering and summary generation phases. This approach ensures that only the final, user-facing content is streamed to the client, maintaining consistency with the non-streaming endpoint while providing the benefits of incremental response delivery.

## Containerization

To deploy your agent to Fargate, you need to containerize it using Podman or Docker. The Dockerfile defines how your application is packaged and run.  Below is an example Docker file that installs all needed dependencies, the application, and configures the FastAPI server to run via unicorn ([Dockerfile][dockerfile]):

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

To deploy the containerized agent to Fargate using the TypeScript CDK, you need to define the infrastructure stack ([agent-fargate-stack.ts][agent_fargate_stack]). Much of the configuration
follows standard Fargate deployment patterns, but the following code snippet highlights the key components specific to deploying Strands Agents SDK agents:

```typescript
// ... vpc, cluster, logGroup, executionRole, and taskRole omitted for brevity ...

// Add permissions for the task to invoke Bedrock APIs
taskRole.addToPolicy(
  new iam.PolicyStatement({
    actions: ["bedrock:InvokeModel", "bedrock:InvokeModelWithResponseStream"],
    resources: ["*"],
  }),
);

// Create a task definition
const taskDefinition = new ecs.FargateTaskDefinition(this, "AgentTaskDefinition", {
  memoryLimitMiB: 512,
  cpu: 256,
  executionRole,
  taskRole,
  runtimePlatform: {
    cpuArchitecture: ecs.CpuArchitecture.ARM64,
    operatingSystemFamily: ecs.OperatingSystemFamily.LINUX,
  },
});

// This will use the Dockerfile in the docker directory
const dockerAsset = new ecrAssets.DockerImageAsset(this, "AgentImage", {
  directory: path.join(__dirname, "../docker"),
  file: "./Dockerfile",
  platform: ecrAssets.Platform.LINUX_ARM64,
});

// Add container to the task definition
taskDefinition.addContainer("AgentContainer", {
  image: ecs.ContainerImage.fromDockerImageAsset(dockerAsset),
  logging: ecs.LogDrivers.awsLogs({
    streamPrefix: "agent-service",
    logGroup,
  }),
  environment: {
    // Add any environment variables needed by your application
    LOG_LEVEL: "INFO",
  },
  portMappings: [
    {
      containerPort: 8000, // The port your application listens on
      protocol: ecs.Protocol.TCP,
    },
  ],
});

// Create a Fargate service
const service = new ecs.FargateService(this, "AgentService", {
  cluster,
  taskDefinition,
  desiredCount: 2, // Run 2 instances for high availability
  assignPublicIp: false, // Use private subnets with NAT gateway
  vpcSubnets: { subnetType: ec2.SubnetType.PRIVATE_WITH_EGRESS },
  circuitBreaker: {
    rollback: true,
  },
  securityGroups: [
    new ec2.SecurityGroup(this, "AgentServiceSG", {
      vpc,
      description: "Security group for Agent Fargate Service",
      allowAllOutbound: true,
    }),
  ],
  minHealthyPercent: 100,
  maxHealthyPercent: 200,
  healthCheckGracePeriod: Duration.seconds(60),
});

// ... load balancer omitted for brevity ...
```

The full example ([agent-fargate-stack.ts][agent_fargate_stack]):

1. Creates a VPC with public and private subnets
2. Sets up an ECS cluster
3. Defines a task role with permissions to invoke Bedrock APIs
4. Creates a Fargate task definition
5. Builds a Docker image from your Dockerfile
6. Configures a Fargate service with multiple instances for high availability
7. Sets up an Application Load Balancer with health checks
8. Outputs the load balancer DNS name for accessing your service

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
SERVICE_URL=$(aws cloudformation describe-stacks --stack-name AgentFargateStack --query "Stacks[0].Outputs[?ExportName=='AgentServiceEndpoint'].OutputValue" --output text)

# Call the weather service
curl -X POST \
  http://$SERVICE_URL/weather \
  -H 'Content-Type: application/json' \
  -d '{"prompt": "What is the weather in Seattle?"}'

# Call the streaming endpoint
curl -X POST \
  http://$SERVICE_URL/weather-streaming \
  -H 'Content-Type: application/json' \
  -d '{"prompt": "What is the weather in New York in Celsius?"}'
```
## Summary

The above steps covered:

- Creating a FastAPI application that hosts your Strands Agents SDK agent
- Containerizing your application with Podman
- Creating the CDK infrastructure to deploy to Fargate
- Deploying the agent and infrastructure to an AWS account
- Manually testing the deployed service

Possible follow-up tasks would be to:

- Set up auto-scaling based on CPU/memory usage or request count
- Implement API authentication for secure access
- Add custom domain name and HTTPS support
- Set up monitoring and alerting
- Implement CI/CD pipeline for automated deployments

## Complete Example

For the complete example code, including all files and configurations, see the [`deploy_to_fargate` sample project on GitHub][project_code].

## Related Resources

- [AWS Fargate Documentation](https://docs.aws.amazon.com/AmazonECS/latest/developerguide/AWS_Fargate.html)
- [AWS CDK Documentation](https://docs.aws.amazon.com/cdk/v2/guide/home.html)
- [Podman Documentation](https://docs.podman.io/en/latest/)
- [FastAPI Documentation](https://fastapi.tiangolo.com/)

[project_code]: {{ docs_repo }}/docs/examples/cdk/deploy_to_fargate
[app_py]: {{ docs_repo }}/docs/examples/cdk/deploy_to_fargate/docker/app/app.py
[dockerfile]: {{ docs_repo }}/docs/examples/cdk/deploy_to_fargate/docker/Dockerfile
[agent_fargate_stack]: {{ docs_repo }}/docs/examples/cdk/deploy_to_fargate/lib/agent-fargate-stack.ts

