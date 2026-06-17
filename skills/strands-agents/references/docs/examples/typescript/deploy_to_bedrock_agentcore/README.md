# TypeScript Agent Deployment to Amazon Bedrock AgentCore Runtime

This example demonstrates deploying a TypeScript-based Strands agent to Amazon Bedrock AgentCore Runtime using Express and Docker.

## What's Included

This example includes a complete, ready-to-deploy agent service with:

- **Express-based HTTP server** with required AgentCore endpoints (`/ping` and `/invocations`)
- **Calculator tool** demonstrating custom tool implementation
- **Amazon Bedrock integration** for LLM inference
- **Docker configuration** for containerized deployment via AgentCore
- **IAM role automation scripts** for AWS permissions setup
- **Test script** for invoking the deployed agent

## Prerequisites

Before you begin, ensure you have:

- Node.js 20+
- Docker installed and running
- AWS CLI configured with valid credentials
- AWS account with [appropriate permissions](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/runtime-permissions.html)
- ECR repository access

## Project Structure

```
.
├── index.ts               # Main agent service implementation
├── invoke.ts              # Test script for deployed agent
├── package.json           # Node.js dependencies and scripts
├── tsconfig.json          # TypeScript configuration
├── Dockerfile             # Container configuration
├── create-iam-role.sh     # IAM role automation script
└── README.md              # This file
```


## Quick Start

### 1. Install Dependencies

```bash
npm install
```

### 2. Test Locally

Build and start the server:

```bash
npm run build
npm start
```

In another terminal, test the health check:

```bash
curl http://localhost:8080/ping
```

Test the agent:

```bash
echo -n "What is 5 plus 3?" | curl -X POST http://localhost:8080/invocations \
  -H "Content-Type: application/octet-stream" \
  --data-binary @-
```

### 3. Test with Docker

Build the Docker image:

```bash
docker build -t my-agent-service .
```

Run the container:

```bash
docker run -p 8081:8080 my-agent-service
```

Test in another terminal:

```bash
curl http://localhost:8081/ping
```

## Deployment to AWS

### Step 1: Create IAM Role

**Option A: Automated Script (Recommended)**

Make the script executable and run it:

```bash
chmod +x create-iam-role.sh
./create-iam-role.sh
```

The script will output the Role ARN. Save this for deployment.

**Option B: Manual Setup**

Create the role manually using AWS CLI or Console following the steps outlined in the above script.

### Step 2: Set Environment Variables

```bash
# Get your AWS Account ID
export ACCOUNTID=$(aws sts get-caller-identity --query Account --output text)

# Set your preferred region
export AWS_REGION=ap-southeast-2

# Get the IAM Role ARN
export ROLE_ARN=$(aws iam get-role \
  --role-name BedrockAgentCoreRuntimeRole \
  --query 'Role.Arn' \
  --output text)

# Set ECR repository name
export ECR_REPO=my-agent-service
```

### Step 3: Create ECR Repository

```bash
aws ecr create-repository \
  --repository-name ${ECR_REPO} \
  --region ${AWS_REGION}
```

### Step 4: Build and Push Docker Image

Login to ECR:

```bash
aws ecr get-login-password --region ${AWS_REGION} | \
  docker login --username AWS --password-stdin \
  ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com
```

Build, Tag, and push:

```bash
docker build -t ${ECR_REPO} .

docker tag ${ECR_REPO}:latest \
  ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest

docker push ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest
```

### Step 5: Create AgentCore Runtime

```bash
aws bedrock-agentcore-control create-agent-runtime \
  --agent-runtime-name my_agent_service \
  --agent-runtime-artifact containerConfiguration={containerUri=${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest} \
  --role-arn ${ROLE_ARN} \
  --network-configuration networkMode=PUBLIC \
  --protocol-configuration serverProtocol=HTTP \
  --region ${AWS_REGION}
```

### Step 6: Verify Deployment

Wait about a minute, then check the status:

```bash
aws bedrock-agentcore-control get-agent-runtime \
  --agent-runtime-id my-agent-service-XXXXXXXXXX \
  --region ${AWS_REGION} \
  --query 'status' \
  --output text
```

Replace `XXXXXXXXXX` with your runtime ID from the create command output.

### Step 7: Test Your Deployment

1. Update `invoke.ts` with your AWS Account ID and runtime ID
2. Run the test:

```bash
npm run test:invoke
```

Expected output:
```
Response: {"response":{"type":"agentResult","stopReason":"endTurn",...}}
```


## Customization

### Adding More Tools

Add custom tools to the agent configuration in `index.ts`:

```typescript
const myCustomTool = strands.tool({
  name: 'my_tool',
  description: 'Description of what this tool does',
  inputSchema: z.object({
    // Define your input schema
  }),
  callback: (input) => {
    // Implement your tool logic
  },
})

const agent = new strands.Agent({
  model: new strands.BedrockModel({
    region: 'ap-southeast-2',
  }),
  tools: [calculatorTool, myCustomTool], // Add your tool here
})
```

## Updating Your Deployment

After making code changes:

1. Build and push new Docker image:
```bash
docker build -t ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest . --no-cache
docker push ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest
```

2. Update the runtime:
```bash
aws bedrock-agentcore-control update-agent-runtime \
  --agent-runtime-id "my-agent-service-XXXXXXXXXX" \
  --agent-runtime-artifact "{\"containerConfiguration\": {\"containerUri\": \"${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest\"}}" \
  --role-arn "${ROLE_ARN}" \
  --network-configuration "{\"networkMode\": \"PUBLIC\"}" \
  --protocol-configuration serverProtocol=HTTP \
  --region ${AWS_REGION}
```

3. Wait a minute and test with `npm run test:invoke`

## Troubleshooting

### TypeScript Compilation Errors

Clean and rebuild:
```bash
rm -rf dist node_modules
npm install
npm run build
```

### Docker Build Fails

Ensure Docker is running:
```bash
docker info
```

Build without cache:
```bash
docker build --no-cache -t my-agent-service .
```

### ECR Authentication Expired

Re-authenticate:
```bash
aws ecr get-login-password --region ${AWS_REGION} | \
  docker login --username AWS --password-stdin \
  ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com
```

### View CloudWatch Logs

```bash
aws logs tail /aws/bedrock-agentcore/runtimes/my-agent-service-XXXXXXXXXX-DEFAULT \
  --region ${AWS_REGION} \
  --since 1h \
  --follow
```

## Additional Resources

- [Full Documentation](../../../user-guide/deploy/deploy_to_bedrock_agentcore/typescript.md) - Complete deployment guide with detailed explanations
- [Amazon Bedrock AgentCore Documentation](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/what-is-bedrock-agentcore.html)
- [Strands TypeScript SDK](https://github.com/strands-agents/sdk-typescript)
- [Express.js Documentation](https://expressjs.com/)
- [Docker Documentation](https://docs.docker.com/)

## Support

For issues or questions:

- Check the [full documentation](../../../user-guide/deploy/deploy_to_bedrock_agentcore/typescript.md) for detailed troubleshooting
- Consult the [Strands documentation](https://strandsagents.com)
