# TypeScript Deployment to Amazon Bedrock AgentCore Runtime


This guide covers deploying TypeScript-based Strands agents to [Amazon Bedrock AgentCore Runtime](index.md) using Express and Docker.

## Prerequisites

- Node.js 20+
- Docker installed and running
- AWS CLI configured with valid credentials
- AWS account with appropriate [permissions](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/runtime-permissions.html)
- ECR repository access

---

## Step 1: Project Setup

### Create Project Structure

```bash
mkdir my-agent-service && cd my-agent-service
npm init -y
```

### Install Dependencies

Create or update your `package.json` with the following configuration and dependencies:

```json
{
  "name": "my-agent-service",
  "version": "1.0.0",
  "type": "module",
  "scripts": {
    "build": "tsc",
    "start": "node dist/index.js",
    "dev": "tsc && node dist/index.js"
  },
  "dependencies": {
    "@strands-agents/sdk": "latest",
    "@aws-sdk/client-bedrock-agentcore": "latest",
    "express": "^4.18.2",
    "zod": "^4.1.12"
  },
  "devDependencies": {
    "@types/express": "^4.17.21",
    "typescript": "^5.3.3"
  }
}
```

Then install all dependencies:

```bash
npm install
```

### Configure TypeScript

Create `tsconfig.json`:

```json
{
  "compilerOptions": {
    "target": "ES2022",
    "module": "ESNext",
    "moduleResolution": "bundler",
    "outDir": "./dist",
    "rootDir": "./",
    "strict": true,
    "esModuleInterop": true,
    "skipLibCheck": true,
    "forceConsistentCasingInFileNames": true
  },
  "include": ["*.ts"],
  "exclude": ["node_modules", "dist"]
}
```

---

## Step 2: Create Your Agent

Create `index.ts` with your agent implementation:

```typescript
import { z } from 'zod'
import * as strands from '@strands-agents/sdk'
import express, { type Request, type Response } from 'express'

const PORT = process.env.PORT || 8080

// Define a custom tool
const calculatorTool = strands.tool({
  name: 'calculator',
  description: 'Performs basic arithmetic operations',
  inputSchema: z.object({
    operation: z.enum(['add', 'subtract', 'multiply', 'divide']),
    a: z.number(),
    b: z.number(),
  }),
  callback: (input): number => {
    switch (input.operation) {
      case 'add':
        return input.a + input.b
      case 'subtract':
        return input.a - input.b
      case 'multiply':
        return input.a * input.b
      case 'divide':
        return input.a / input.b
    }
  },
})

// Configure the agent with Amazon Bedrock
const agent = new strands.Agent({
  model: new strands.BedrockModel({
    region: 'ap-southeast-2', // Change to your preferred region
  }),
  tools: [calculatorTool],
})

const app = express()

// Health check endpoint (REQUIRED)
app.get('/ping', (_, res) =>
  res.json({
    status: 'Healthy',
    time_of_last_update: Math.floor(Date.now() / 1000),
  })
)

// Agent invocation endpoint (REQUIRED)
// AWS sends binary payload, so we use express.raw middleware
app.post('/invocations', express.raw({ type: '*/*' }), async (req, res) => {
  try {
    // Decode binary payload from AWS SDK
    const prompt = new TextDecoder().decode(req.body)

    // Invoke the agent
    const response = await agent.invoke(prompt)

    // Return response
    return res.json({ response })
  } catch (err) {
    console.error('Error processing request:', err)
    return res.status(500).json({ error: 'Internal server error' })
  }
})

// Start server
app.listen(PORT, () => {
  console.log(`🚀 AgentCore Runtime server listening on port ${PORT}`)
  console.log(`📍 Endpoints:`)
  console.log(`   POST http://0.0.0.0:${PORT}/invocations`)
  console.log(`   GET  http://0.0.0.0:${PORT}/ping`)
})
```

**Understanding the Endpoints**

AgentCore Runtime requires your service to expose two HTTP endpoints, `/ping` and `/invocations`. See [HTTP protocol contract](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/runtime-http-protocol-contract.html) for more details.

---

## Step 3: Test Locally


**Compile & Start server**
```bash
npm run build

npm start
```

**Test health check**

```bash
curl http://localhost:8080/ping
```

**Test invocation**

```bash
echo -n "What is 5 plus 3?" | curl -X POST http://localhost:8080/invocations \
  -H "Content-Type: application/octet-stream" \
  --data-binary @-
```

---

## Step 4: Create Dockerfile

Create a `Dockerfile` for deployment:

```dockerfile
FROM --platform=linux/arm64 public.ecr.aws/docker/library/node:latest

WORKDIR /app

# Copy source code
COPY . ./

# Install dependencies
RUN npm install

# Build TypeScript
RUN npm run build

# Expose port
EXPOSE 8080

# Start the application
CMD ["npm", "start"]
```

### Test Docker Build Locally

**Build the image**

```bash
docker build -t my-agent-service .
```

**Run the container**

```bash
docker run -p 8081:8080 my-agent-service
```

**Test in another terminal**

```bash
curl http://localhost:8081/ping
```

---

## Step 5: Create IAM Role

The agent runtime needs an IAM role with permissions to access Bedrock and other AWS services.

### Option 1: Using a Script (Recommended)

The easiest way to create the IAM role is to use the provided script that automates the entire process.

Create a file `create-iam-role.sh`:

```bash
#!/bin/bash

# Script to create IAM role for AWS Bedrock AgentCore Runtime
# Based on the CloudFormation AgentCoreRuntimeExecutionRole

set -e

# Get AWS Account ID and Region
ACCOUNT_ID=$(aws sts get-caller-identity --query Account --output text)
REGION=${AWS_REGION:-ap-southeast-2}

echo "Creating IAM role for Bedrock AgentCore Runtime..."
echo "Account ID: ${ACCOUNT_ID}"
echo "Region: ${REGION}"

# Role name
ROLE_NAME="BedrockAgentCoreRuntimeRole"

# Create trust policy document
TRUST_POLICY=$(cat <<EOF
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Sid": "AssumeRolePolicy",
      "Effect": "Allow",
      "Principal": {
        "Service": "bedrock-agentcore.amazonaws.com"
      },
      "Action": "sts:AssumeRole",
      "Condition": {
        "StringEquals": {
          "aws:SourceAccount": "${ACCOUNT_ID}"
        },
        "ArnLike": {
          "aws:SourceArn": "arn:aws:bedrock-agentcore:${REGION}:${ACCOUNT_ID}:*"
        }
      }
    }
  ]
}
EOF
)

# Create permissions policy document
PERMISSIONS_POLICY=$(cat <<EOF
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Sid": "ECRImageAccess",
      "Effect": "Allow",
      "Action": [
        "ecr:BatchGetImage",
        "ecr:GetDownloadUrlForLayer"
      ],
      "Resource": "arn:aws:ecr:${REGION}:${ACCOUNT_ID}:repository/*"
    },
    {
      "Sid": "ECRTokenAccess",
      "Effect": "Allow",
      "Action": "ecr:GetAuthorizationToken",
      "Resource": "*"
    },
    {
      "Effect": "Allow",
      "Action": [
        "logs:DescribeLogStreams",
        "logs:CreateLogGroup"
      ],
      "Resource": "arn:aws:logs:${REGION}:${ACCOUNT_ID}:log-group:/aws/bedrock-agentcore/runtimes/*"
    },
    {
      "Effect": "Allow",
      "Action": "logs:DescribeLogGroups",
      "Resource": "arn:aws:logs:${REGION}:${ACCOUNT_ID}:log-group:*"
    },
    {
      "Effect": "Allow",
      "Action": [
        "logs:CreateLogStream",
        "logs:PutLogEvents"
      ],
      "Resource": "arn:aws:logs:${REGION}:${ACCOUNT_ID}:log-group:/aws/bedrock-agentcore/runtimes/*:log-stream:*"
    },
    {
      "Effect": "Allow",
      "Action": [
        "xray:PutTraceSegments",
        "xray:PutTelemetryRecords",
        "xray:GetSamplingRules",
        "xray:GetSamplingTargets"
      ],
      "Resource": "*"
    },
    {
      "Effect": "Allow",
      "Action": "cloudwatch:PutMetricData",
      "Resource": "*",
      "Condition": {
        "StringEquals": {
          "cloudwatch:namespace": "bedrock-agentcore"
        }
      }
    },
    {
      "Sid": "BedrockModelAccess",
      "Effect": "Allow",
      "Action": [
        "bedrock:InvokeModel",
        "bedrock:InvokeModelWithResponseStream"
      ],
      "Resource": [
        "arn:aws:bedrock:*::foundation-model/*",
        "arn:aws:bedrock:${REGION}:${ACCOUNT_ID}:*"
      ]
    }
  ]
}
EOF
)

# Check if role already exists
if aws iam get-role --role-name ${ROLE_NAME} 2>/dev/null; then
  echo "Role ${ROLE_NAME} already exists."
  echo "Role ARN: $(aws iam get-role --role-name ${ROLE_NAME} --query 'Role.Arn' --output text)"
  exit 0
fi

# Create the IAM role
echo "Creating IAM role: ${ROLE_NAME}"
aws iam create-role \
  --role-name ${ROLE_NAME} \
  --assume-role-policy-document "${TRUST_POLICY}" \
  --description "Service role for AWS Bedrock AgentCore Runtime" \
  --tags Key=ManagedBy,Value=Script Key=Purpose,Value=BedrockAgentCore

echo "Attaching permissions policy to role..."
aws iam put-role-policy \
  --role-name ${ROLE_NAME} \
  --policy-name AgentCoreRuntimeExecutionPolicy \
  --policy-document "${PERMISSIONS_POLICY}"

# Get the role ARN
ROLE_ARN=$(aws iam get-role --role-name ${ROLE_NAME} --query 'Role.Arn' --output text)

echo ""
echo "✅ IAM Role created successfully!"
echo ""
echo "Role Name: ${ROLE_NAME}"
echo "Role ARN:  ${ROLE_ARN}"
echo ""
echo "Use this ARN in your create-agent-runtime command:"
echo "  --role-arn ${ROLE_ARN}"
echo ""
echo "You can also set it as an environment variable:"
echo "  export ROLE_ARN=${ROLE_ARN}"
```

**Make the script executable**

```bash
chmod +x create-iam-role.sh
```

**Run the script**

```bash
./create-iam-role.sh
```

**Or specify a different region**

```bash
AWS_REGION=us-east-1 ./create-iam-role.sh
```

The script will output the role ARN. Save this for the deployment steps.


### Option 2: Using AWS Console

1. Go to IAM Console → Roles → Create Role
2. Select "Custom trust policy" and paste the trust policy above
3. Attach the required policies:
    - AmazonBedrockFullAccess
    - CloudWatchLogsFullAccess
    - AWSXRayDaemonWriteAccess

4. Name the role `BedrockAgentCoreRuntimeRole`

---

## Step 6: Deploy to AWS

**Set Environment Variables**

```bash
export ACCOUNTID=$(aws sts get-caller-identity --query Account --output text)

export AWS_REGION=ap-southeast-2

// Set the IAM Role ARN
export ROLE_ARN=$(aws iam get-role \
  --role-name BedrockAgentCoreRuntimeRole \
  --query 'Role.Arn' \
  --output text)

// New or Existing ECR repository name
export ECR_REPO=my-agent-service
```

**Create ECR Repository**

> Create a new ECR repo if it doesn't yet exist

```bash
aws ecr create-repository \
  --repository-name ${ECR_REPO} \
  --region ${AWS_REGION}
```

**Build and Push Docker Image:**

**Login to ECR**

```bash
aws ecr get-login-password --region ${AWS_REGION} | \
  docker login --username AWS --password-stdin \
  ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com
```

**Build, Tag, and Push**

```bash
docker build -t ${ECR_REPO} .

docker tag ${ECR_REPO}:latest \
  ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest
  
docker push ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest
```

**Create AgentCore Runtime**

```bash
aws bedrock-agentcore-control create-agent-runtime \
  --agent-runtime-name my_agent_service \
  --agent-runtime-artifact containerConfiguration={containerUri=${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest} \
  --role-arn ${ROLE_ARN} \
  --network-configuration networkMode=PUBLIC \
  --protocol-configuration serverProtocol=HTTP \
  --region ${AWS_REGION}
```

### Verify Deployment Status

Wait a minute for the runtime to reach "READY" status.

**Get runtime ID from the create command output, then check status**

```bash
aws bedrock-agentcore-control get-agent-runtime \
  --agent-runtime-id my-agent-service-XXXXXXXXXX \
  --region ${AWS_REGION} \
  --query 'status' \
  --output text
```

**You can list all runtimes if needed:**

```bash
aws bedrock-agentcore-control list-agent-runtimes --region ${AWS_REGION}
```



---

## Step 7: Test Your Deployment

### Create Test Script

Create `invoke.ts`:

> Update the `YOUR_ACCOUNT_ID` and the `agentRuntimeArn` to the variables we just saw

```typescript
import {
  BedrockAgentCoreClient,
  InvokeAgentRuntimeCommand,
} from '@aws-sdk/client-bedrock-agentcore'

const input_text = 'Calculate 5 plus 3 using the calculator tool'

const client = new BedrockAgentCoreClient({
  region: 'ap-southeast-2',
})

const input = {
  // Generate unique session ID
  runtimeSessionId: 'test-session-' + Date.now() + '-' + Math.random().toString(36).substring(7),
  // Replace with your actual runtime ARN
  agentRuntimeArn:
    'arn:aws:bedrock-agentcore:ap-southeast-2:YOUR_ACCOUNT_ID:runtime/my-agent-service-XXXXXXXXXX',
  qualifier: 'DEFAULT',
  payload: new TextEncoder().encode(input_text),
}

const command = new InvokeAgentRuntimeCommand(input)
const response = await client.send(command)
const textResponse = await response.response.transformToString()

console.log('Response:', textResponse)
```

### Run the Test

```bash
npx tsx invoke.ts
```

Expected output:
```
Response: {"response":{"type":"agentResult","stopReason":"endTurn","lastMessage":{"type":"message","role":"assistant","content":[{"type":"textBlock","text":"The result of 5 plus 3 is **8**."}]}}}
```

---

## Step 8: Update Your Deployment

After making code changes, use this workflow to update your deployed agent.

**Build TypeScript**

```bash
npm run build
```

**Set Environment Variables**

```bash
export ACCOUNTID=$(aws sts get-caller-identity --query Account --output text)

export AWS_REGION=ap-southeast-2

export ECR_REPO=my-agent-service
```

**Get the IAM Role ARN**

```bash
export ROLE_ARN=$(aws iam get-role --role-name BedrockAgentCoreRuntimeRole --query 'Role.Arn' --output text)
```

**Build new image**

```bash
docker build -t ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest . --no-cache
```

**Push to ECR**

```bash
docker push ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest
```

**Update runtime** 
> (replace XXXXXXXXXX with your runtime ID)

```bash
aws bedrock-agentcore-control update-agent-runtime \
  --agent-runtime-id "my-agent-service-XXXXXXXXXX" \
  --agent-runtime-artifact "{\"containerConfiguration\": {\"containerUri\": \"${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com/${ECR_REPO}:latest\"}}" \
  --role-arn "${ROLE_ARN}" \
  --network-configuration "{\"networkMode\": \"PUBLIC\"}" \
  --protocol-configuration serverProtocol=HTTP \
  --region ${AWS_REGION}
```

Wait a minute for the update to complete, then test with `npx tsx invoke.ts`.

---

## Best Practices

**Development**

- Test locally with Docker before deploying
- Use TypeScript strict mode for better type safety
- Include error handling in all endpoints
- Log important events for debugging

**Deployment**

- Keep IAM permissions minimal (least privilege)
- Monitor CloudWatch logs after deployment
- Test thoroughly after each update

---

## Troubleshooting

### Build Errors

**TypeScript compilation fails:**

Clean, install and build

```bash
rm -rf dist node_modules

npm install

npm run build
```

**Docker build fails:**

Ensure Docker is running

```bash
docker info
```

Try building without cache

```bash
docker build --no-cache -t my-agent-service .
```

### Deployment Errors

**"Access Denied" errors:**

- Verify IAM role trust policy includes your account ID
- Check role has required permissions
- Ensure you have permissions to create AgentCore runtimes


**ECR authentication expired:**

```bash
// Re-authenticate
aws ecr get-login-password --region ${AWS_REGION} | \
  docker login --username AWS --password-stdin \
  ${ACCOUNTID}.dkr.ecr.${AWS_REGION}.amazonaws.com
```


### Runtime Errors

**Check CloudWatch logs**

```bash
aws logs tail /aws/bedrock-agentcore/runtimes/my-agent-service-XXXXXXXXXX-DEFAULT \
  --region ${AWS_REGION} \
  --since 5m \
  --follow
```

---

## Observability

Amazon Bedrock AgentCore provides built-in observability through CloudWatch. 

### View Recent Logs

```bash
aws logs tail /aws/bedrock-agentcore/runtimes/my-agent-service-XXXXXXXXXX-DEFAULT \
  --region ${AWS_REGION} \
  --since 1h
```

---


## Additional Resources

- [Amazon Bedrock AgentCore Runtime Documentation](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/what-is-bedrock-agentcore.html)
- [Strands TypeScript SDK Repository](https://github.com/strands-agents/sdk-typescript)
- [Express.js Documentation](https://expressjs.com/)
- [Docker Documentation](https://docs.docker.com/)
- [AWS IAM Documentation](https://docs.aws.amazon.com/IAM/latest/UserGuide/introduction.html)
