# Deploying Strands Agents SDK Agents to Amazon EC2

Amazon EC2 (Elastic Compute Cloud) provides resizable compute capacity in the cloud, making it a flexible option for deploying Strands Agents SDK agents. This deployment approach gives you full control over the underlying infrastructure while maintaining the ability to scale as needed.

If you're not familiar with the AWS CDK, check out the [official documentation](https://docs.aws.amazon.com/cdk/v2/guide/home.html).

This guide discusses EC2 integration at a high level - for a complete example project deploying to EC2, check out the [`deploy_to_ec2` sample project on GitHub][project_code].

## Creating Your Agent in Python

The core of your EC2 deployment is a FastAPI application that hosts your Strands Agents SDK agent. This Python application initializes your agent and processes incoming HTTP requests.

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

@app.route('/weather', methods=['POST'])
def get_weather():
    """Endpoint to get weather information."""
    data = request.json
    prompt = data.get('prompt')
    
    if not prompt:
        return jsonify({"error": "No prompt provided"}), 400

    try:
        weather_agent = Agent(
            system_prompt=WEATHER_SYSTEM_PROMPT,
            tools=[http_request],
        )
        response = weather_agent(prompt)
        content = str(response)
        return content, {"Content-Type": "plain/text"}
    except Exception as e:
        return jsonify({"error": str(e)}), 500
```

### Streaming responses

Streaming responses can significantly improve the user experience by providing real-time responses back to the customer. This is especially valuable for longer responses.

The EC2 deployment implements streaming through a custom approach that adapts the agent's output to an iterator that can be consumed by FastAPI. Here's how it's implemented:

```python
def run_weather_agent_and_stream_response(prompt: str):
    is_summarizing = False

    @tool
    def ready_to_summarize():
        nonlocal is_summarizing

        is_summarizing = True
        return "Ok - continue providing the summary!"

    def thread_run(callback_handler):
        weather_agent = Agent(
            system_prompt=WEATHER_SYSTEM_PROMPT,
            tools=[http_request, ready_to_summarize],
            callback_handler=callback_handler
        )
        weather_agent(prompt)

    iterator = adapt_to_iterator(thread_run)

    for item in iterator:
        if not is_summarizing:
            continue
        if "data" in item:
            yield item['data']

@app.route('/weather-streaming', methods=['POST'])
def get_weather_streaming():
    try:
        data = request.json
        prompt = data.get('prompt')

        if not prompt:
            return jsonify({"error": "No prompt provided"}), 400

        return run_weather_agent_and_stream_response(prompt), {"Content-Type": "plain/text"}
    except Exception as e:
        return jsonify({"error": str(e)}), 500
```

The implementation above employs a [custom tool](../concepts/tools/custom-tools.md#creating-custom-tools) to mark the boundary between information gathering and summary generation phases. This approach ensures that only the final, user-facing content is streamed to the client, maintaining consistency with the non-streaming endpoint while providing the benefits of incremental response delivery.

## Infrastructure

To deploy the agent to EC2 using the TypeScript CDK, you need to define the infrastructure stack ([agent-ec2-stack.ts][agent_ec2_stack]). The following code snippet highlights the key components specific to deploying Strands Agents SDK agents to EC2:

```typescript
// ... instance role & security-group omitted for brevity ...

// Upload the application code to S3
 const appAsset = new Asset(this, "AgentAppAsset", {
   path: path.join(__dirname, "../app"),
 });

 // Upload dependencies to S3
 // This could also be replaced by a pip install if all dependencies are public
 const dependenciesAsset = new Asset(this, "AgentDependenciesAsset", {
   path: path.join(__dirname, "../packaging/_dependencies"),
 });
 
 instanceRole.addToPolicy(
   new iam.PolicyStatement({
     actions: ["bedrock:InvokeModel", "bedrock:InvokeModelWithResponseStream"],
     resources: ["*"],
   }),
 );

 // Create an EC2 instance in a public subnet with a public IP
 const instance = new ec2.Instance(this, "AgentInstance", {
   vpc,
   vpcSubnets: { subnetType: ec2.SubnetType.PUBLIC }, // Use public subnet
   instanceType: ec2.InstanceType.of(ec2.InstanceClass.T4G, ec2.InstanceSize.MEDIUM), // ARM-based instance
   machineImage: ec2.MachineImage.latestAmazonLinux2023({
     cpuType: ec2.AmazonLinuxCpuType.ARM_64,
   }),
   securityGroup: instanceSG,
   role: instanceRole,
   associatePublicIpAddress: true, // Assign a public IP address
 });

```

For EC2 deployment, the application code and dependencies are packaged separately and uploaded to S3 as assets. During instance initialization, both packages are downloaded and extracted to the appropriate locations and then configured to run as a Linux service:

```typescript
 // Create user data script to set up the application
 const userData = ec2.UserData.forLinux();
 userData.addCommands(
   "#!/bin/bash",
   "set -o verbose",
   "yum update -y",
   "yum install -y python3.12 python3.12-pip git unzip ec2-instance-connect",

   // Create app directory
   "mkdir -p /opt/agent-app",

   // Download application files from S3
   `aws s3 cp ${appAsset.s3ObjectUrl} /tmp/app.zip`,
   `aws s3 cp ${dependenciesAsset.s3ObjectUrl} /tmp/dependencies.zip`,

   // Extract application files
   "unzip /tmp/app.zip -d /opt/agent-app",
   "unzip /tmp/dependencies.zip -d /opt/agent-app/_dependencies",

   // Create a systemd service file
   "cat > /etc/systemd/system/agent-app.service << 'EOL'",
   "[Unit]",
   "Description=Weather Agent Application",
   "After=network.target",
   "",
   "[Service]",
   "User=ec2-user",
   "WorkingDirectory=/opt/agent-app",
   "ExecStart=/usr/bin/python3.12 -m uvicorn app:app --host=0.0.0.0 --port=8000 --workers=2",
   "Restart=always",
   "Environment=PYTHONPATH=/opt/agent-app:/opt/agent-app/_dependencies",
   "Environment=LOG_LEVEL=INFO",
   "",
   "[Install]",
   "WantedBy=multi-user.target",
   "EOL",

   // Enable and start the service
   "systemctl enable agent-app.service",
   "systemctl start agent-app.service",
 );
```

The full example ([agent-ec2-stack.ts][agent_ec2_stack]):

1. Creates a VPC with public subnets
2. Sets up an EC2 instance with the appropriate IAM role
3. Defines permissions to invoke Bedrock APIs
4. Uploads application code and dependencies to S3
5. Creates a user data script to:
   - Install Python and other dependencies
   - Download and extract the application code and dependencies
   - Set up the application as a systemd service
6. Outputs the instance ID, public IP, and service endpoint for easy access

## Deploying Your Agent & Testing

To deploy your agent to EC2:

```bash
# Bootstrap your AWS environment (if not already done)
npx cdk bootstrap

# Package Python dependencies for the target architecture
pip install -r requirements.txt --target ./packaging/_dependencies --python-version 3.12 --platform manylinux2014_aarch64 --only-binary=:all:

# Deploy the stack
npx cdk deploy
```

Once deployed, you can test your agent using the public IP address and port:

```bash
# Get the service URL from the CDK output
SERVICE_URL=$(aws cloudformation describe-stacks --stack-name AgentEC2Stack --region us-east-1 --query "Stacks[0].Outputs[?ExportName=='Ec2ServiceEndpoint'].OutputValue" --output text)

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
- Packaging your application and dependencies for EC2 deployment
- Creating the CDK infrastructure to deploy to EC2
- Setting up the application as a systemd service
- Deploying the agent and infrastructure to an AWS account
- Manually testing the deployed service

Possible follow-up tasks would be to:

- Implement an update mechanism for the application
- Add a load balancer for improved availability and scaling
- Set up auto-scaling with multiple instances
- Implement API authentication for secure access
- Add custom domain name and HTTPS support
- Set up monitoring and alerting
- Implement CI/CD pipeline for automated deployments

## Complete Example

For the complete example code, including all files and configurations, see the [`deploy_to_ec2` sample project on GitHub][project_code].

## Related Resources

- [Amazon EC2 Documentation](https://docs.aws.amazon.com/ec2/)
- [AWS CDK Documentation](https://docs.aws.amazon.com/cdk/v2/guide/home.html)
- [FastAPI Documentation](https://fastapi.tiangolo.com/)

[project_code]: {{ docs_repo }}/docs/examples/cdk/deploy_to_ec2
[app_py]: {{ docs_repo }}/docs/examples/cdk/deploy_to_ec2/app/app.py
[agent_ec2_stack]: {{ docs_repo }}/docs/examples/cdk/deploy_to_ec2/lib/agent-ec2-stack.ts
