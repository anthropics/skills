# TypeScript Deployment to Docker

This guide covers deploying TypeScript-based Strands agents using Docker for local and cloud development.

## Prerequisites

- Node.js 20+
- [Docker](https://www.docker.com/) installed and running
- Model provider credentials

---

## Quick Start Setup

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
setup_typescript_agent() {
# Create project directory and initialize with npm
mkdir my-typescript-agent && cd my-typescript-agent
npm init -y

# Install required dependencies
npm install @strands-agents/sdk express @types/express typescript ts-node
npm install -D @types/node

# Create TypeScript configuration
cat > tsconfig.json << 'EOF'
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
EOF

# Add npm scripts
npm pkg set scripts.build="tsc" scripts.start="node dist/index.js" scripts.dev="ts-node index.ts"

# Create the Express agent application
cat > index.ts << 'EOF'
import { Agent } from '@strands-agents/sdk'
import express, { type Request, type Response } from 'express'
import { OpenAIModel } from '@strands-agents/sdk/openai'

const PORT = Number(process.env.PORT) || 8080

// Note: Any supported model provider can be configured
// Automatically uses process.env.OPENAI_API_KEY
const model = new OpenAIModel()

const agent = new Agent({ model })

const app = express()

// Middleware to parse JSON
app.use(express.json())

// Health check endpoint
app.get('/ping', (_: Request, res: Response) =>
  res.json({
    status: 'healthy',
  })
)

// Agent invocation endpoint
app.post('/invocations', async (req: Request, res: Response) => {
  try {
    const { input } = req.body
    const prompt = input?.prompt || ''

    if (!prompt) {
      return res.status(400).json({
        detail: 'No prompt found in input. Please provide a "prompt" key in the input.'
      })
    }

    // Invoke the agent
    const result = await agent.invoke(prompt)

    const response = {
      message: result,
      timestamp: new Date().toISOString(),
      model: 'strands-agent',
    }

    return res.json({ output: response })
  } catch (err) {
    console.error('Error processing request:', err)
    return res.status(500).json({
      detail: `Agent processing failed: ${err instanceof Error ? err.message : 'Unknown error'}`
    })
  }
})

// Start server
app.listen(PORT, '0.0.0.0', () => {
  console.log(`🚀 Strands Agent Server listening on port ${PORT}`)
  console.log(`📍 Endpoints:`)
  console.log(`   POST http://0.0.0.0:${PORT}/invocations`)
  console.log(`   GET  http://0.0.0.0:${PORT}/ping`)
})
EOF

# Create Docker configuration
cat > Dockerfile << 'EOF'
# Use Node 20+
FROM node:20

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
EOF

echo "Setup complete! Project created in my-typescript-agent/"
}

# Run the setup
setup_typescript_agent
```

</details>

Step 1: Create project directory and initialize
```bash
mkdir my-typescript-agent && cd my-typescript-agent
npm init -y
```

Step 2: Add dependencies
```bash
npm install @strands-agents/sdk express @types/express typescript ts-node
npm install -D @types/node
```

Step 3: Create tsconfig.json
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

Step 4: Update package.json scripts
```json
{
  "scripts": {
    "build": "tsc",
    "start": "node dist/index.js",
    "dev": "ts-node index.ts"
  }
}
```

Step 5: Create index.ts
```typescript
--8<-- "user-guide/deploy/deploy_to_docker/imports.ts:imports"
--8<-- "user-guide/deploy/deploy_to_docker/index.ts:agent"
```

Step 6: Create Dockerfile
```dockerfile
# Use Node 20+
FROM node:20

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


Your project structure will now look like:
```
my-typescript-app/
├── index.ts                # Express application
├── Dockerfile              # Container configuration
├── package.json            # Created by npm init
├── tsconfig.json           # TypeScript configuration
└── package-lock.json       # Created automatically by npm
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

Run the container with OpenAI credentials:
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
- **Image build fails**: Check `package.json` and dependencies
- **TypeScript compilation errors**: Check `tsconfig.json` and run `npm run build` locally
- **"Unable to locate credentials"**: Verify model provider credentials environment variables are set
- **Port already in use**: Use different port mapping `-p 8081:8080`

## Docker Compose for Local Development

**Optional**: Docker Compose is only recommended for local development. Most cloud service providers only support raw Docker commands, not Docker Compose.

For local development and testing, Docker Compose provides a more convenient way to manage your container:

```yaml
# Example for OpenAI
version: '3.8'
services:
  my-typescript-agent:
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

- [Amazon Bedrock AgentCore](../deploy_to_bedrock_agentcore/typescript.md) - Deploy to AWS with Bedrock integration
- [AWS Fargate](../deploy_to_aws_fargate.md) - Deploy to AWS's managed container service
- [Amazon EKS](../deploy_to_amazon_eks.md) - Deploy to Kubernetes on AWS
- [Amazon EC2](../deploy_to_amazon_ec2.md) - Deploy directly to EC2 instances


## Additional Resources

- [Strands Documentation](https://strandsagents.com/latest/)
- [Docker Documentation](https://docs.docker.com/)
- [Express.js Documentation](https://expressjs.com/)
- [TypeScript Docker Guide](https://docs.docker.com/guides/nodejs/)