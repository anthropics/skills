# Amazon EKS Deployment Example

## Introduction

This is an example that demonstrates how to deploy a Python application to Amazon EKS.   
The example deploys a weather forecaster application that runs as a containerized service in Amazon EKS with an Application Load Balancer. The application is built with FastAPI and provides two weather endpoints:

1. `/weather` - A standard endpoint that returns weather information based on the provided prompt
2. `/weather-streaming` - A streaming endpoint that delivers weather information in real-time as it's being generated

## Prerequisites

- [AWS CLI](https://aws.amazon.com/cli/) installed and configured
- [eksctl](https://eksctl.io/installation/) (v0.208.x or later) installed
- [Helm](https://helm.sh/) (v3 or later) installed
- [kubectl](https://docs.aws.amazon.com/eks/latest/userguide/install-kubectl.html) installed
- Either:
    - [Podman](https://podman.io/) installed and running
    - (or) [Docker](https://www.docker.com/) installed and running
- Amazon Bedrock Anthropic Claude 4 model enabled in your AWS environment

## Project Structure

- `chart/` - Contains the Helm chart
    - `values.yaml` - Helm chart default values
- `docker/` - Contains the Dockerfile and application code for the container:
     - `Dockerfile` - Docker image definition
     - `app/` - Application code
     - `requirements.txt` - Python dependencies for the container & local development

## Create EKS Auto Mode cluster

Set environment variables
```bash
export AWS_ACCOUNT_ID=$(aws sts get-caller-identity --query 'Account' --output text)
export AWS_REGION=us-east-1
export CLUSTER_NAME=eks-strands-agents-demo
```

Create EKS Auto Mode cluster
```bash
eksctl create cluster --name $CLUSTER_NAME --enable-auto-mode
```
Configure kubeconfig context
```bash
aws eks update-kubeconfig --name $CLUSTER_NAME
```

## Building and Pushing Docker Image to ECR

Follow these steps to build the Docker image and push it to Amazon ECR:

1. Authenticate to Amazon ECR:
```bash
aws ecr get-login-password --region ${AWS_REGION} | docker login --username AWS --password-stdin ${AWS_ACCOUNT_ID}.dkr.ecr.${AWS_REGION}.amazonaws.com
```

2. Create the ECR repository if it doesn't exist:
```bash
aws ecr create-repository --repository-name strands-agents-weather --region ${AWS_REGION}
```

3. Build the Docker image:
```bash
docker build --platform linux/amd64 -t strands-agents-weather:latest docker/
```

4. Tag the image for ECR:
```bash
docker tag strands-agents-weather:latest ${AWS_ACCOUNT_ID}.dkr.ecr.${AWS_REGION}.amazonaws.com/strands-agents-weather:latest
```

5. Push the image to ECR:
```bash
docker push ${AWS_ACCOUNT_ID}.dkr.ecr.${AWS_REGION}.amazonaws.com/strands-agents-weather:latest
```

## Configure EKS Pod Identity to access Amazon Bedrock

Create an IAM policy to allow InvokeModel & InvokeModelWithResponseStream to all Amazon Bedrock models
```bash
cat > bedrock-policy.json << EOF
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Effect": "Allow",
      "Action": [
        "bedrock:InvokeModel",
        "bedrock:InvokeModelWithResponseStream"
      ],
      "Resource": "*"
    }
  ]
}
EOF

aws iam create-policy \
  --policy-name strands-agents-weather-bedrock-policy \
  --policy-document file://bedrock-policy.json
rm -f bedrock-policy.json
```

Create an EKS Pod Identity association
```bash
eksctl create podidentityassociation --cluster $CLUSTER_NAME \
  --namespace default \
  --service-account-name strands-agents-weather \
  --permission-policy-arns arn:aws:iam::$AWS_ACCOUNT_ID:policy/strands-agents-weather-bedrock-policy \
  --role-name eks-strands-agents-weather
```

## Deploy strands-agents-weather application

Deploy the helm chart with the image from ECR
```bash
helm install strands-agents-weather ./chart \
  --set image.repository=${AWS_ACCOUNT_ID}.dkr.ecr.${AWS_REGION}.amazonaws.com/strands-agents-weather --set image.tag=latest
```

Wait for Deployment to be available (Pods Running)
```bash
kubectl wait --for=condition=available deployments strands-agents-weather --all
```

## Test the Agent

Using kubernetes port-forward
```
kubectl --namespace default port-forward service/strands-agents-weather 8080:80 &
```

Call the weather service
```
curl -X POST \
  http://localhost:8080/weather \
  -H 'Content-Type: application/json' \
  -d '{"prompt": "What is the weather in Seattle?"}'
```

Call the weather streaming endpoint
```
curl -X POST \
  http://localhost:8080/weather-streaming \
  -H 'Content-Type: application/json' \
  -d '{"prompt": "What is the weather in New York in Celsius?"}'
```

## Expose Agent through Application Load Balancer

[Create an IngressClass to configure an Application Load Balancer](https://docs.aws.amazon.com/eks/latest/userguide/auto-configure-alb.html)
```bash
cat <<EOF | kubectl apply -f -
apiVersion: eks.amazonaws.com/v1
kind: IngressClassParams
metadata:
  name: alb
spec:
  scheme: internet-facing
EOF
```

```bash
cat <<EOF | kubectl apply -f -
apiVersion: networking.k8s.io/v1
kind: IngressClass
metadata:
  name: alb
  annotations:
    ingressclass.kubernetes.io/is-default-class: "true"
spec:
  controller: eks.amazonaws.com/alb
  parameters:
    apiGroup: eks.amazonaws.com
    kind: IngressClassParams
    name: alb
EOF
```

Update helm deployment to create Ingress using the IngressClass created
```bash
helm upgrade strands-agents-weather ./chart \
  --set image.repository=${AWS_ACCOUNT_ID}.dkr.ecr.${AWS_REGION}.amazonaws.com/strands-agents-weather --set image.tag=latest \
  --set ingress.enabled=true \
  --set ingress.className=alb 
```

Get the ALB URL
```bash
export ALB_URL=$(kubectl get ingress strands-agents-weather -o jsonpath='{.status.loadBalancer.ingress[0].hostname}')
echo "The shared ALB is available at: http://$ALB_URL"
```

Wait for ALB to be active
```bash
aws elbv2 wait load-balancer-available --load-balancer-arns $(aws elbv2 describe-load-balancers --query 'LoadBalancers[?DNSName==`'"$ALB_URL"'`].LoadBalancerArn' --output text)
```

Call the weather service Application Load Balancer endpoint
```bash
curl -X POST \
  http://$ALB_URL/weather \
  -H 'Content-Type: application/json' \
  -d '{"prompt": "What is the weather in Portland?"}'
```

## Configure High Availability and Resiliency

- Increase replicas to 3
- [Topology Spread Constraints](https://kubernetes.io/docs/concepts/scheduling-eviction/topology-spread-constraints/): Spread workload across multi-az
- [Pod Disruption Budgets](https://kubernetes.io/docs/concepts/workloads/pods/disruptions/#pod-disruption-budgets): Tolerate minAvailable of 1

```bash 
helm upgrade strands-agents-weather ./chart -f - <<EOF
image:
  repository: ${AWS_ACCOUNT_ID}.dkr.ecr.${AWS_REGION}.amazonaws.com/strands-agents-weather 
  tag: latest

ingress:
  enabled: true 
  className: alb

replicaCount: 3

topologySpreadConstraints:
  - maxSkew: 1
    minDomains: 3
    topologyKey: topology.kubernetes.io/zone
    whenUnsatisfiable: DoNotSchedule
    labelSelector:
      matchLabels:
        app.kubernetes.io/name: strands-agents-weather
  - maxSkew: 1
    topologyKey: kubernetes.io/hostname
    whenUnsatisfiable: ScheduleAnyway
    labelSelector:
      matchLabels:
        app.kubernetes.io/instance: strands-agents-weather
          
podDisruptionBudget:
  enabled: true
  minAvailable: 1
EOF
```

## Cleanup

Uninstall helm chart
```bash
helm uninstall strands-agents-weather
```

Delete EKS Auto Mode cluster
```bash
eksctl delete cluster --name $CLUSTER_NAME --wait
```

Delete IAM policy
```bash
aws iam delete-policy --policy-arn arn:aws:iam::$AWS_ACCOUNT_ID:policy/strands-agents-weather-bedrock-policy
```