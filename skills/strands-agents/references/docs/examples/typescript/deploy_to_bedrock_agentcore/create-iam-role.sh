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

# Create trust policy documentf
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
