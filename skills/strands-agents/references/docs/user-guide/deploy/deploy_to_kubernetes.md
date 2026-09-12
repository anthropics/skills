# Deploy to Kubernetes

This guide covers deploying containerized Strands agents to Kubernetes using Kind (Kubernetes in Docker) for local and cloud development.

## Prerequisites

- **Docker deployment guide completed** - You must have a working containerized agent before proceeding:
    - [Python Docker guide](../deploy_to_docker/python) 
    - [TypeScript Docker guide](../deploy_to_docker/typescript)
- [Kind](https://kind.sigs.k8s.io/docs/user/quick-start/) installed
- [kubectl](https://kubernetes.io/docs/tasks/tools/) installed

## Step 1: Setup Kind Cluster

Create a Kind cluster:
```bash
kind create cluster --name my-cluster
```

Verify cluster is running:
```bash
kubectl get nodes
```

## Step 2: Create Kubernetes Manifests

The following assume you have completed the [Docker deployment guide](../deploy_to_docker) with the following file structure:


Project Structure (Python):
```
my-python-app/
├── agent.py                # FastAPI application (from Docker tutorial)
├── Dockerfile              # Container configuration (from Docker tutorial)
├── pyproject.toml          # Created by uv init
└── uv.lock                 # Created automatically by uv
```

Project Structure (TypeScript):
```
my-typescript-app/
├── index.ts                # Express application (from Docker tutorial)
├── Dockerfile              # Container configuration (from Docker tutorial)
├── package.json            # Created by npm init
├── tsconfig.json           # TypeScript configuration
└── package-lock.json       # Created automatically by npm
```

Add k8s-deployment.yaml to your project:
```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-app
spec:
  replicas: 1
  selector:
    matchLabels:
      app: my-app
  template:
    metadata:
      labels:
        app: my-app
    spec:
      containers:
      - name: my-app
        image: my-image:latest
        imagePullPolicy: Never
        ports:
        - containerPort: 8080
        env:
        - name: OPENAI_API_KEY
          value: "<your-api-key>"
---
apiVersion: v1
kind: Service
metadata:
  name: my-service
spec:
  selector:
    app: my-app
  ports:
  - port: 8080
    targetPort: 8080
  type: NodePort
```

This example k8s-deployment.yaml uses OpenAI, but any supported model provider can be configured. See the [Strands documentation](https://strandsagents.com/latest/documentation/docs/user-guide/concepts/model-providers) for all supported model providers. For instance, to include AWS credentials:

```yaml
env:
  - name: AWS_ACCESS_KEY_ID
    value: "<your-access-key-id>"
  - name: AWS_SECRET_ACCESS_KEY
    value: "<your-secret-access-id>"
  - name: AWS_REGION
    value: "us-east-1"
```

## Step 3: Deploy to Kubernetes

Build and load your Docker image:
```bash
docker build -t my-image:latest .
kind load docker-image my-image:latest --name my-cluster
```

Apply the Kubernetes manifests:
```bash
kubectl apply -f k8s-deployment.yaml
```

Verify deployment:
```bash
kubectl get pods
kubectl get services
```

## Step 4: Test Your Deployment

Port forward to access the service:
```bash
kubectl port-forward svc/my-service 8080:8080
```

Test the endpoints:
```bash
# Health check
curl http://localhost:8080/ping

# Test agent invocation
curl -X POST http://localhost:8080/invocations \
  -H "Content-Type: application/json" \
  -d '{"input": {"prompt": "What is artificial intelligence?"}}'
```

## Step 5: Making Changes

When you modify your code, redeploy with:

```bash
# Rebuild image
docker build -t my-image:latest .

# Load into cluster
kind load docker-image my-image:latest --name my-cluster

# Restart deployment
kubectl rollout restart deployment my-app
```

## Cleanup

Remove the Kind cluster when done:
```bash
kind delete cluster --name my-cluster
```

## Optional: Deploy to Cloud-Hosted Kubernetes

Once your application works locally with Kind, you can deploy it to any cloud-hosted Kubernetes cluster. 

See our documentation for [Deploying Strands Agents to Amazon EKS](https://strandsagents.com/latest/documentation/docs/user-guide/deploy/deploy_to_amazon_eks/) as an example.

### Step 1: Push Container to Repository

Push your image to a container registry:
```bash
# Tag and push to your registry (Docker Hub, ECR, GCR, etc.)
docker tag my-image:latest <registry-url>/my-image:latest
docker push <registry-url>/my-image:latest
```

### Step 2: Update Deployment Configuration

Update `k8s-deployment.yaml` for cloud deployment:

```yaml
# Change image pull policy from:
imagePullPolicy: Never
# To:
imagePullPolicy: Always

# Change image URL from:
image: my-image:latest
# To:
image: <registry-url>/my-image:latest

# Change service type from:
type: NodePort
# To:
type: LoadBalancer
```

### Step 3: Apply to Cloud Cluster

```bash
# Connect to your cloud cluster (varies by provider)
kubectl config use-context <cloud-context>

# Deploy your application
kubectl apply -f k8s-deployment.yaml
```


## Additional Resources

- [Docker Documentation](https://docs.docker.com/)
- [Strands Docker Deploy Documentation](../deploy_to_docker)
- [Kubernetes Documentation](https://kubernetes.io/docs/)
- [Kubectl Reference](https://kubernetes.io/docs/reference/kubectl/)
- [Kubernetes Deployment Guide](https://kubernetes.io/docs/concepts/workloads/controllers/deployment/)
