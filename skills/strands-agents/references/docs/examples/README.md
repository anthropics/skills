# Examples Overview

The examples directory provides a collection of sample implementations to help you get started with building intelligent agents using Strands Agents. This directory contains two main subdirectories: `/examples/python` for Python-based agent examples and `/examples/cdk` for Cloud Development Kit integration examples.

## Purpose

These examples demonstrate how to leverage Strands Agents to build intelligent agents for various use cases. From simple file operations to complex multi-agent systems, each example illustrates key concepts, patterns, and best practices in agent development.

By exploring these reference implementations, you'll gain practical insights into Strands Agents' capabilities and learn how to apply them to your own projects. The examples emphasize real-world applications that you can adapt and extend for your specific needs.

## Prerequisites

- Python 3.10 or higher
- Strands Agents SDK
- AWS credentials configured with access to a Bedrock model provider using the Claude 4 model (modifiable as needed)
- For specific examples, additional requirements may be needed (see individual example READMEs)

For more information, see the [Getting Started](../user-guide/quickstart.md) guide.

## Getting Started

1. Clone the repository containing these examples
2. Install the required dependencies:
   - [strands-agents](https://github.com/strands-agents/sdk-python)
   - [strands-agents-tools](https://github.com/strands-agents/tools)
3. Navigate to the examples directory:
   ```bash
   cd /path/to/examples/
   ```
4. Browse the available examples in the `/examples/python` and `/examples/cdk` directories
5. Each example includes its own README or documentation file with specific instructions
6. Follow the documentation to run the example and understand its implementation

## Directory Structure

### Python Examples

The `/examples/python` directory contains various Python-based examples demonstrating different agent capabilities. Each example includes detailed documentation explaining its purpose, implementation details, and instructions for running it.

These examples cover a diverse range of agent capabilities and patterns, showcasing the flexibility and power of Strands Agents. The directory is regularly updated with new examples as additional features and use cases are developed.

Available Python examples:

- [Agents Workflows](python/agents_workflows.md) - Example of a sequential agent workflow pattern
- [CLI Reference Agent](python/cli-reference-agent.md) - Example of Command-line reference agent implementation
- [File Operations](python/file_operations.md) - Example of agent with file manipulation capabilities
- [MCP Calculator](python/mcp_calculator.md) - Example of agent with Model Context Protocol capabilities
- [Meta Tooling](python/meta_tooling.md) - Example of agent with Meta tooling capabilities 
- [Multi-Agent Example](python/multi_agent_example/multi_agent_example.md) - Example of a multi-agent system
- [Weather Forecaster](python/weather_forecaster.md) - Example of a weather forecasting agent with http_request capabilities

### CDK Examples

The `/examples/cdk` directory contains examples for using the AWS Cloud Development Kit (CDK) with agents. The CDK is an open-source software development framework for defining cloud infrastructure as code and provisioning it through AWS CloudFormation. These examples demonstrate how to deploy agent-based applications to AWS using infrastructure as code principles.

Each CDK example includes its own documentation with instructions for setup and deployment.

Available CDK examples:

- [Deploy to EC2](cdk/deploy_to_ec2/README.md) - Guide for deploying agents to Amazon EC2 instances
- [Deploy to Fargate](cdk/deploy_to_fargate/README.md) - Guide for deploying agents to AWS Fargate
- [Deploy to App Runner](cdk/deploy_to_apprunner/README.md) - Guide for deploying agents to AWS App Runner
- [Deploy to Lambda](cdk/deploy_to_lambda/README.md) - Guide for deploying agents to AWS Lambda

### TypeScript Examples

The `/examples/typescript` directory contains TypeScript-based examples demonstrating agent deployment and integration patterns. These examples showcase how to build and Deploy Typescript agents.

Available TypeScript examples:

- [Deploy to Bedrock AgentCore](typescript/deploy_to_bedrock_agentcore/README.md) - Complete example for deploying TypeScript agents to Amazon Bedrock AgentCore Runtime.

### Amazon EKS Example

The `/examples/deploy_to_eks` directory contains examples for using Amazon EKS with agents.   
The [Deploy to Amazon EKS](deploy_to_eks/README.md) includes its own documentation with instruction for setup and deployment.

## Example Structure

Each example typically follows this structure:

- Python implementation file(s) (`.py`)
- Documentation file (`.md`) explaining the example's purpose, architecture, and usage
- Any additional resources needed for the example

To run any specific example, refer to its associated documentation for detailed instructions and requirements.
