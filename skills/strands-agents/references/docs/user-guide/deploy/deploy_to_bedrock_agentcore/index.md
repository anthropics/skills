# Deploying Strands Agents to Amazon Bedrock AgentCore Runtime

Amazon Bedrock AgentCore Runtime is a secure, serverless runtime purpose-built for deploying and scaling dynamic AI agents and tools using any open-source framework including Strands Agents, LangChain, LangGraph and CrewAI. It supports any protocol such as MCP and A2A, and any model from any provider including Amazon Bedrock, OpenAI, Gemini, etc. Developers can securely and reliably run any type of agent including multi-modal, real-time, or long-running agents. AgentCore Runtime helps protect sensitive data with complete session isolation, providing dedicated microVMs for each user session - critical for AI agents that maintain complex state and perform privileged operations on users' behalf. It is highly reliable with session persistence and it can scale up to thousands of agent sessions in seconds so developers don't have to worry about managing infrastructure and only pay for actual usage. AgentCore Runtime, using AgentCore Identity, also seamlessly integrates with the leading identity providers such as Amazon Cognito, Microsoft Entra ID, and Okta, as well as popular OAuth providers such as Google and GitHub. It supports all authentication methods, from OAuth tokens and API keys to IAM roles, so developers don't have to build custom security infrastructure.

## Prerequisites

Before you start, you need:

- An AWS account with appropriate [permissions](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/runtime-permissions.html)
- Python 3.10+ or Node.js 20+
- Optional: A container engine (Docker, Finch, or Podman) - only required for local testing and advanced deployment scenarios

---


## Choose Strands SDK Your Language

Select your preferred programming language to get started with deploying Strands agents to Amazon Bedrock AgentCore Runtime:

## :material-language-python: **Python Deployment**

Deploy your Python Strands agent to AgentCore Runtime!

[**→ Start with Python**](python.md)

---

## :material-language-typescript: **TypeScript Deployment**

Deploy your TypeScript Strands agent to AgentCore Runtime!

[**→ Start with TypeScript**](typescript.md)

---

## Additional Resources

- [Amazon Bedrock AgentCore Runtime Documentation](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/what-is-bedrock-agentcore.html)
- [Strands Documentation](https://strandsagents.com/latest/)
- [AWS IAM Documentation](https://docs.aws.amazon.com/IAM/latest/UserGuide/introduction.html)
- [Docker Documentation](https://docs.docker.com/)
- [Amazon Bedrock AgentCore Observability](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/observability.html)
