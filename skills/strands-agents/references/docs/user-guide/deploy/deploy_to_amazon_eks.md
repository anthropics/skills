# Deploying Strands Agents SDK Agents to Amazon EKS

Amazon Elastic Kubernetes Service (EKS) is a managed container orchestration service that makes it easy to deploy, manage, and scale containerized applications using Kubernetes, while AWS manages the Kubernetes control plane.

In this tutorial we are using [Amazon EKS Auto Mode](https://aws.amazon.com/eks/auto-mode), EKS Auto Mode extends AWS management of Kubernetes clusters beyond the cluster itself, to allow AWS to also set up and manage the infrastructure that enables the smooth operation of your workloads. This makes it an excellent choice for deploying Strands Agents SDK agents as containerized applications with high availability and scalability.

This guide discuss EKS integration at a high level - for a complete example project deploying to EKS, check out the [`deploy_to_eks` sample project on GitHub][project_code].

## Creating Your Agent in Python

The core of your EKS deployment is a containerized Flask application that hosts your Strands Agents SDK agent. This Python application initializes your agent and processes incoming HTTP requests.

The FastAPI application follows these steps:

1. Define endpoints for agent interactions
2. Create a Strands agent with the specified system prompt and tools
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

To deploy your agent to EKS, you need to containerize it using Podman or Docker. The Dockerfile defines how your application is packaged and run.  Below is an example Docker file that installs all needed dependencies, the application, and configures the FastAPI server to run via unicorn ([Dockerfile][dockerfile]):

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

To deploy our containerized agent to EKS, we will first need to provision an EKS Auto Mode cluster, define IAM role and policies, associate them with a Kubernetes Service Account and package & deploy our Agent using Helm.   
Helm packages and deploys application to Kubernetes and EKS, Helm enables deployment to different environments, define version control, updates, and consistent deployments across EKS clusters.

Follow the full example [`deploy_to_eks` sample project on GitHub][project_code]:

1. Using eksctl creates an EKS Auto Mode cluster and a VPC
2. Builds and pushes the Docker image from your Dockerfile to Amazon Elastic Container Registry (ECR). 
3. Configure agent access to AWS services such as Amazon Bedrock by using Amazon EKS Pod Identity.
4. Deploy the `strands-agents-weather` agent helm package to EKS
5. Sets up an Application Load Balancer using Kubernetes Ingress and EKS Auto Mode network capabilities.
6. Outputs the load balancer DNS name for accessing your service

## Deploying Your agent & Testing

Assuming your EKS Auto Mode cluster is already provisioned, deploy the Helm chart.

```bash
helm install strands-agents-weather docs/examples/deploy_to_eks/chart
```

Once deployed, you can test your agent using kubectl port-forward:

```bash
kubectl port-forward service/strands-agents-weather 8080:80 &
```

Call the weather service
```bash
curl -X POST \
  http://localhost:8080/weather \
  -H 'Content-Type: application/json' \
  -d '{"prompt": "What is the weather in Seattle?"}'
```

Call the weather streaming endpoint
```bash
curl -X POST \
  http://localhost:8080/weather-streaming \
  -H 'Content-Type: application/json' \
  -d '{"prompt": "What is the weather in New York in Celsius?"}'
```

## Summary

The above steps covered:

- Creating a FastAPI application that hosts your Strands Agents SDK agent
- Containerizing your application with Podman or Docker
- Creating the infrastructure to deploy to EKS Auto Mode
- Deploying the agent and infrastructure to EKS Auto Mode
- Manually testing the deployed service

Possible follow-up tasks would be to:

- Set up auto-scaling based on CPU/memory usage or request count using HPA
- Configure Pod Disruption Budgets for high availability and resiliency
- Implement API authentication for secure access
- Add custom domain name and HTTPS support
- Set up monitoring and alerting
- Implement CI/CD pipeline for automated deployments

## Complete Example

For the complete example code, including all files and configurations, see the  [`deploy_to_eks` sample project on GitHub][project_code]

## Related Resources

- [Amazon EKS Auto Mode Documentation](https://docs.aws.amazon.com/eks/latest/userguide/automode.html)
- [eksctl Documentation](https://eksctl.io/usage/creating-and-managing-clusters/)
- [FastAPI Documentation](https://fastapi.tiangolo.com/)

[project_code]: {{ docs_repo }}/docs/examples/deploy_to_eks
[app_py]: {{ docs_repo }}/docs/examples/deploy_to_eks/docker/app/app.py
[dockerfile]: {{ docs_repo }}/docs/examples/deploy_to_eks/docker/Dockerfile
[values_yaml]: {{ docs_repo }}/docs/examples/deploy_to_eks/chart/values.yaml