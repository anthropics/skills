---
name: strands-agents
description: "Build, test, and deploy AI agents using the AWS Strands Agents framework (Python). Use this skill when: (1) Building new AI agents with Strands Agents SDK, (2) Creating custom tools for Strands agents, (3) Setting up multi-agent systems (Graph, Swarm, Workflow patterns), (4) Deploying agents to Amazon Bedrock AgentCore Runtime, (5) Deploying agents to AWS Lambda, Fargate, App Runner, EKS, EC2, or Docker, (6) Configuring model providers (Bedrock, Anthropic, OpenAI, Ollama, etc.), (7) Adding observability, evaluation, or guardrails to agents, (8) Working with MCP tools in Strands, (9) Setting up bidirectional streaming agents (voice/audio), (10) Any task involving strands-agents, strands-agents-tools, strands-agents-builder, or strands-agents-evals packages."
---

# Strands Agents

## Skill Directory

This skill is located at: `C:\Users\Administrator\.claude\skills\strands-agents`

## Documentation Reference

Full Strands Agents documentation is bundled at `references/docs/`. Use Grep/Read to search these docs as needed.

### Doc Navigation Map

| Topic | Path (relative to `references/docs/`) |
|---|---|
| **Quickstart** | `user-guide/quickstart/python.md` |
| **Agent Loop** | `user-guide/concepts/agents/agent-loop.md` |
| **State & Sessions** | `user-guide/concepts/agents/state.md`, `session-management.md` |
| **System Prompts** | `user-guide/concepts/agents/prompts.md` |
| **Hooks** | `user-guide/concepts/agents/hooks.md` |
| **Structured Output** | `user-guide/concepts/agents/structured-output.md` |
| **Conversation Mgmt** | `user-guide/concepts/agents/conversation-management.md` |
| **Retry Strategies** | `user-guide/concepts/agents/retry-strategies.md` |
| **Custom Tools** | `user-guide/concepts/tools/custom-tools.md` |
| **MCP Tools** | `user-guide/concepts/tools/mcp-tools.md` |
| **Community Tools** | `user-guide/concepts/tools/community-tools-package.md` |
| **Tool Executors** | `user-guide/concepts/tools/executors.md` |
| **Multi-Agent: Graph** | `user-guide/concepts/multi-agent/graph.md` |
| **Multi-Agent: Swarm** | `user-guide/concepts/multi-agent/swarm.md` |
| **Multi-Agent: Workflow** | `user-guide/concepts/multi-agent/workflow.md` |
| **Multi-Agent: A2A** | `user-guide/concepts/multi-agent/agent-to-agent.md` |
| **Agents as Tools** | `user-guide/concepts/multi-agent/agents-as-tools.md` |
| **Multi-Agent Patterns** | `user-guide/concepts/multi-agent/multi-agent-patterns.md` |
| **Streaming** | `user-guide/concepts/streaming/index.md` |
| **Async Iterators** | `user-guide/concepts/streaming/async-iterators.md` |
| **Callback Handlers** | `user-guide/concepts/streaming/callback-handlers.md` |
| **Interrupts** | `user-guide/concepts/interrupts.md` |
| **Bidi Streaming** | `user-guide/concepts/bidirectional-streaming/quickstart.md` |
| **Model: Bedrock** | `user-guide/concepts/model-providers/amazon-bedrock.md` |
| **Model: Anthropic** | `user-guide/concepts/model-providers/anthropic.md` |
| **Model: OpenAI** | `user-guide/concepts/model-providers/openai.md` |
| **Model: Ollama** | `user-guide/concepts/model-providers/ollama.md` |
| **Model: Custom** | `user-guide/concepts/model-providers/custom_model_provider.md` |
| **All Model Providers** | `user-guide/concepts/model-providers/` |
| **Deploy: AgentCore** | `user-guide/deploy/deploy_to_bedrock_agentcore/python.md` |
| **Deploy: Lambda** | `user-guide/deploy/deploy_to_aws_lambda.md` |
| **Deploy: Fargate** | `user-guide/deploy/deploy_to_aws_fargate.md` |
| **Deploy: App Runner** | `user-guide/deploy/deploy_to_aws_apprunner.md` |
| **Deploy: EKS** | `user-guide/deploy/deploy_to_amazon_eks.md` |
| **Deploy: EC2** | `user-guide/deploy/deploy_to_amazon_ec2.md` |
| **Deploy: Docker** | `user-guide/deploy/deploy_to_docker/python.md` |
| **Deploy: Kubernetes** | `user-guide/deploy/deploy_to_kubernetes.md` |
| **Deploy: Terraform** | `user-guide/deploy/deploy_to_terraform.md` |
| **Production Ops** | `user-guide/deploy/operating-agents-in-production.md` |
| **Observability** | `user-guide/observability-evaluation/observability.md` |
| **Traces** | `user-guide/observability-evaluation/traces.md` |
| **Metrics** | `user-guide/observability-evaluation/metrics.md` |
| **Logs** | `user-guide/observability-evaluation/logs.md` |
| **Evaluation** | `user-guide/observability-evaluation/evaluation.md` |
| **Evals SDK** | `user-guide/evals-sdk/quickstart.md` |
| **Guardrails** | `user-guide/safety-security/guardrails.md` |
| **PII Redaction** | `user-guide/safety-security/pii-redaction.md` |
| **Prompt Engineering** | `user-guide/safety-security/prompt-engineering.md` |
| **Agent Config** | `user-guide/concepts/experimental/agent-config.md` |
| **Steering** | `user-guide/concepts/experimental/steering.md` |
| **Examples (Python)** | `examples/` |
| **Community Packages** | `community/community-packages.md` |

## Project Scaffolding

To create a new Strands Agents project for the user, run the scaffold script:

```bash
python "C:\Users\Administrator\.claude\skills\strands-agents\scripts\scaffold_project.py" <project-name> --path <target-dir> [--extras bedrock-agentcore evals fastapi mcp bidi]
```

This creates a uv-managed project in the user's working directory with:
- `strands-agents`, `strands-agents-tools`, `strands-agents-builder`, `boto3` (always included)
- Optional: `bedrock-agentcore` + `bedrock-agentcore-starter-toolkit` (for AgentCore deployment)
- Optional: `strands-agents-evals` (for evaluation)
- Optional: `fastapi`, `uvicorn`, `pydantic`, `httpx` (for custom HTTP agents)
- Optional: `strands-agents[mcp]` (for MCP tool support)
- Optional: `strands-agents[bidi-all]` (for bidirectional voice/audio streaming)
- Starter `src/agent.py`, `tools/example_tool.py`, and `tests/` directory

If the user already has a project, add dependencies directly with `uv add strands-agents strands-agents-tools boto3`.

## Core Patterns

### Minimal Agent

```python
from strands import Agent
agent = Agent()
result = agent("Hello!")
print(result.message)
```

### Agent with Custom Tools

```python
from strands import Agent, tool

@tool
def my_tool(param: str) -> str:
    """Description for the LLM.

    Args:
        param: What this parameter does
    """
    return f"Result: {param}"

agent = Agent(tools=[my_tool])
```

### Agent with Model Provider

```python
from strands import Agent
from strands.models import BedrockModel

model = BedrockModel(model_id="anthropic.claude-sonnet-4-20250514-v1:0", region_name="us-west-2")
agent = Agent(model=model)
```

Default model: `us.anthropic.claude-sonnet-4-20250514-v1:0` via Bedrock cross-region inference.

### AgentCore Deployment (Quick)

```python
from bedrock_agentcore.runtime import BedrockAgentCoreApp
from strands import Agent

app = BedrockAgentCoreApp()
agent = Agent()

@app.entrypoint
def invoke(payload):
    result = agent(payload.get("prompt", "Hello"))
    return {"result": result.message}

if __name__ == "__main__":
    app.run()
```

Deploy: `agentcore configure --entrypoint agent.py && agentcore launch`

## Workflow

1. **Read relevant docs** before writing code - use the Doc Navigation Map above to find the right reference file, then Read it
2. **Scaffold or add deps** - use the scaffold script for new projects, or `uv add` for existing ones
3. **Write agent code** in the user's project directory
4. **Test locally** with `uv run python src/agent.py`
5. **Deploy** per the user's target platform (read the relevant deploy doc first)

## Key SDK Facts

- Python 3.10+ required (3.12+ for Nova Sonic bidi streaming)
- Tools: `@tool` decorator auto-generates schema from docstrings + type hints
- Agent returns `AgentResult` with `.message`, `.metrics`, `.stop_reason`
- Streaming: `agent.stream_async(prompt)` for async iterators, `callback_handler=` for callbacks
- Session persistence: `FileSessionManager`, `S3SessionManager`
- Multi-agent: Graph (conditional flows), Swarm (autonomous handoffs), Workflow (DAG pipelines)
- Hooks: lifecycle callbacks via `agent.hooks.add_callback(EventType, fn)`
- Conversation mgmt: `SlidingWindowConversationManager` (default, prevents context overflow)
- Observability: OpenTelemetry traces, `result.metrics.get_summary()`
- Debug: `logging.getLogger("strands").setLevel(logging.DEBUG)`
