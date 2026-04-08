# Agent-to-Agent (A2A) Protocol

Strands Agents supports the [Agent-to-Agent (A2A) protocol](https://a2aproject.github.io/A2A/latest/), enabling seamless communication between AI agents across different platforms and implementations.

## What is Agent-to-Agent (A2A)?

The Agent-to-Agent protocol is an open standard that defines how AI agents can discover, communicate, and collaborate with each other.

### Use Cases

A2A protocol support enables several powerful use cases:

- **Multi-Agent Workflows**: Chain multiple specialized agents together
- **Agent Marketplaces**: Discover and use agents from different providers
- **Cross-Platform Integration**: Connect Strands agents with other A2A-compatible systems
- **Distributed AI Systems**: Build scalable, distributed agent architectures

Learn more about the A2A protocol:

- [A2A GitHub Organization](https://github.com/a2aproject/A2A)
- [A2A Python SDK](https://github.com/a2aproject/a2a-python)
- [A2A Documentation](https://a2aproject.github.io/A2A/latest/)

!!! tip "Complete Examples Available"
    Check out the [Native A2A Support samples](https://github.com/strands-agents/samples/tree/main/03-integrations/Native-A2A-Support) for complete, ready-to-run client, server and tool implementations.

## Installation

To use A2A functionality with Strands, install the package with the A2A extra:

```bash
pip install 'strands-agents[a2a]'
```

This installs the core Strands SDK along with the necessary A2A protocol dependencies.

## Consuming Remote Agents

{{ ts_not_supported("`A2AAgent` class is not currently supported in the TypeScript SDK.") }}

The `A2AAgent` class provides the simplest way to consume remote A2A agents. It wraps the A2A protocol communication and presents a familiar interface—you can invoke it just like a regular Strands `Agent`.

Without `A2AAgent`, you need to manually resolve agent cards, configure HTTP clients, build protocol messages, and parse responses. The `A2AAgent` class handles all of this automatically.

### Basic Usage

```python
from strands.agent.a2a_agent import A2AAgent

# Create an A2AAgent pointing to a remote A2A server
a2a_agent = A2AAgent(endpoint="http://localhost:9000")

# Invoke it just like a regular Agent
result = a2a_agent("Show me 10 ^ 6")
print(result.message)
# {'role': 'assistant', 'content': [{'text': '10^6 = 1,000,000'}]}
```

The `A2AAgent` returns an `AgentResult` just like a local `Agent`, making it easy to integrate remote agents into your existing code.

### Configuration Options

The `A2AAgent` constructor accepts these parameters.

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `endpoint` | `str` | Required | Base URL of the remote A2A agent |
| `name` | `str` | None | Agent name (auto-populated from agent card if not provided) |
| `description` | `str` | None | Agent description (auto-populated from agent card if not provided) |
| `timeout` | `int` | 300 | Timeout for HTTP operations in seconds |
| `a2a_client_factory` | `ClientFactory` | None | Optional pre-configured A2A client factory |

### Asynchronous Invocation

For async workflows, use `invoke_async`:

```python
import asyncio
from strands.agent.a2a_agent import A2AAgent

async def main():
    a2a_agent = A2AAgent(endpoint="http://localhost:9000")
    result = await a2a_agent.invoke_async("Calculate the square root of 144")
    print(result.message)

asyncio.run(main())
```

### Streaming Responses

For real-time streaming of responses, use `stream_async`:

```python
import asyncio
from strands.agent.a2a_agent import A2AAgent

async def main():
    a2a_agent = A2AAgent(endpoint="http://localhost:9000")
    
    async for event in a2a_agent.stream_async("Explain quantum computing"):
        if "data" in event:
            print(event["data"], end="", flush=True)

asyncio.run(main())
```

### Fetching the Agent Card

You can retrieve the remote agent's metadata using `get_agent_card`:

```python
import asyncio
from strands.agent.a2a_agent import A2AAgent

async def main():
    a2a_agent = A2AAgent(endpoint="http://localhost:9000")
    card = await a2a_agent.get_agent_card()
    print(f"Agent: {card.name}")
    print(f"Description: {card.description}")
    print(f"Skills: {card.skills}")

asyncio.run(main())
```

## A2AAgent in Multi-Agent Patterns

The `A2AAgent` class integrates with Strands multi-agent patterns that support it. Currently, you can use remote A2A agents in [Graph](graph.md) workflows and as [tools in an orchestrator agent](#as-a-tool).

### As a Tool

You can wrap an `A2AAgent` as a tool in an orchestrator agent's toolkit:

```python
from strands import Agent, tool
from strands.agent.a2a_agent import A2AAgent

calculator_agent = A2AAgent(
    endpoint="http://calculator-service:9000",
    name="calculator"
)

@tool
def calculate(expression: str) -> str:
    """Perform a mathematical calculation."""
    result = calculator_agent(expression)
    return str(result.message["content"][0]["text"])

orchestrator = Agent(
    system_prompt="You are a helpful assistant. Use the calculate tool for math.",
    tools=[calculate]
)
```

### In Graph Workflows

The `A2AAgent` works as a node in [Graph](graph.md) workflows. See [Remote Agents with A2AAgent](graph.md#remote-agents-with-a2aagent) for detailed examples of mixing local and remote agents in graph-based pipelines.

### In Swarm Patterns

!!! note "Not yet supported"
    `A2AAgent` is not currently supported in Swarm patterns. Swarm coordination relies on tool-based handoffs that require capabilities not yet available in the A2A protocol. Use [Graph](graph.md) workflows for multi-agent patterns with remote A2A agents.

## Creating an A2A Server

### Basic Server Setup

Create a Strands agent and expose it as an A2A server:

```python
import logging
from strands_tools.calculator import calculator
from strands import Agent
from strands.multiagent.a2a import A2AServer

logging.basicConfig(level=logging.INFO)

# Create a Strands agent
strands_agent = Agent(
    name="Calculator Agent",
    description="A calculator agent that can perform basic arithmetic operations.",
    tools=[calculator],
    callback_handler=None
)

# Create A2A server (streaming enabled by default)
a2a_server = A2AServer(agent=strands_agent)

# Start the server
a2a_server.serve()
```

> NOTE: the server supports both `SendMessageRequest` and `SendStreamingMessageRequest` client requests!

### Server Configuration Options

The `A2AServer` constructor accepts several configuration options:

- `agent`: The Strands agent to wrap with A2A compatibility
- `host`: Hostname or IP address to bind to (default: "127.0.0.1")
- `port`: Port to bind to (default: 9000)
- `version`: Version of the agent (default: "0.0.1")
- `skills`: Custom list of agent skills (default: auto-generated from tools)
- `http_url`: Public HTTP URL where this agent will be accessible (optional, enables path-based mounting)
- `serve_at_root`: Forces server to serve at root path regardless of http_url path (default: False)
- `task_store`: Custom task storage implementation (defaults to InMemoryTaskStore)
- `queue_manager`: Custom message queue management (optional)
- `push_config_store`: Custom push notification configuration storage (optional)
- `push_sender`: Custom push notification sender implementation (optional)

### Advanced Server Customization

The `A2AServer` provides access to the underlying FastAPI or Starlette application objects allowing you to further customize server behavior.

```python
from contextlib import asynccontextmanager
from strands import Agent
from strands.multiagent.a2a import A2AServer
import uvicorn

# Create your agent and A2A server
agent = Agent(name="My Agent", description="A customizable agent", callback_handler=None)
a2a_server = A2AServer(agent=agent)

@asynccontextmanager
async def lifespan(app: FastAPI):
    """Manage application lifespan with proper error handling."""
    # Startup tasks
    yield  # Application runs here
    # Shutdown tasks

# Access the underlying FastAPI app
# Allows passing keyword arguments to FastAPI constructor for further customization
fastapi_app = a2a_server.to_fastapi_app(app_kwargs={"lifespan": lifespan})
# Add custom middleware, routes, or configuration
fastapi_app.add_middleware(...)

# Or access the Starlette app
# Allows passing keyword arguments to FastAPI constructor for further customization
starlette_app = a2a_server.to_starlette_app(app_kwargs={"lifespan": lifespan})
# Customize as needed

# You can then serve the customized app directly
uvicorn.run(fastapi_app, host="127.0.0.1", port=9000)
```

#### Configurable Request Handler Components

The `A2AServer` supports configurable request handler components for advanced customization:

```python
from strands import Agent
from strands.multiagent.a2a import A2AServer
from a2a.server.tasks import TaskStore, PushNotificationConfigStore, PushNotificationSender
from a2a.server.events import QueueManager

# Custom task storage implementation
class CustomTaskStore(TaskStore):
    # Implementation details...
    pass

# Custom queue manager
class CustomQueueManager(QueueManager):
    # Implementation details...
    pass

# Create agent with custom components
agent = Agent(name="My Agent", description="A customizable agent", callback_handler=None)

a2a_server = A2AServer(
    agent=agent,
    task_store=CustomTaskStore(),
    queue_manager=CustomQueueManager(),
    push_config_store=MyPushConfigStore(),
    push_sender=MyPushSender()
)
```

**Interface Requirements:**

Custom implementations must follow these interfaces:

- `task_store`: Must implement `TaskStore` interface from `a2a.server.tasks`
- `queue_manager`: Must implement `QueueManager` interface from `a2a.server.events`
- `push_config_store`: Must implement `PushNotificationConfigStore` interface from `a2a.server.tasks`
- `push_sender`: Must implement `PushNotificationSender` interface from `a2a.server.tasks`

#### Path-Based Mounting for Containerized Deployments

The `A2AServer` supports automatic path-based mounting for deployment scenarios involving load balancers or reverse proxies. This allows you to deploy agents behind load balancers with different path prefixes.

```python
from strands import Agent
from strands.multiagent.a2a import A2AServer

# Create an agent
agent = Agent(
    name="Calculator Agent",
    description="A calculator agent",
    callback_handler=None
)

# Deploy with path-based mounting
# The agent will be accessible at http://my-alb.amazonaws.com/calculator/
a2a_server = A2AServer(
    agent=agent,
    http_url="http://my-alb.amazonaws.com/calculator"
)

# For load balancers that strip path prefixes, use serve_at_root=True
a2a_server_with_root = A2AServer(
    agent=agent,
    http_url="http://my-alb.amazonaws.com/calculator",
    serve_at_root=True  # Serves at root even though URL has /calculator path
)
```

This flexibility allows you to:

- Add custom middleware
- Implement additional API endpoints
- Deploy agents behind load balancers with different path prefixes
- Configure custom task storage and event handling components

## A2A Client Examples

### Synchronous Client

Here's how to create a client that communicates with an A2A server synchronously:

```python
import asyncio
import logging
from uuid import uuid4

import httpx
from a2a.client import A2ACardResolver, ClientConfig, ClientFactory
from a2a.types import Message, Part, Role, TextPart

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

DEFAULT_TIMEOUT = 300 # set request timeout to 5 minutes

def create_message(*, role: Role = Role.user, text: str) -> Message:
    return Message(
        kind="message",
        role=role,
        parts=[Part(TextPart(kind="text", text=text))],
        message_id=uuid4().hex,
    )

async def send_sync_message(message: str, base_url: str = "http://127.0.0.1:9000"):
    async with httpx.AsyncClient(timeout=DEFAULT_TIMEOUT) as httpx_client:
        # Get agent card
        resolver = A2ACardResolver(httpx_client=httpx_client, base_url=base_url)
        agent_card = await resolver.get_agent_card()

        # Create client using factory
        config = ClientConfig(
            httpx_client=httpx_client,
            streaming=False,  # Use non-streaming mode for sync response
        )
        factory = ClientFactory(config)
        client = factory.create(agent_card)

        # Create and send message
        msg = create_message(text=message)

        # With streaming=False, this will yield exactly one result
        async for event in client.send_message(msg):
            if isinstance(event, Message):
                logger.info(event.model_dump_json(exclude_none=True, indent=2))
                return event
            elif isinstance(event, tuple) and len(event) == 2:
                # (Task, UpdateEvent) tuple
                task, update_event = event
                logger.info(f"Task: {task.model_dump_json(exclude_none=True, indent=2)}")
                if update_event:
                    logger.info(f"Update: {update_event.model_dump_json(exclude_none=True, indent=2)}")
                return task
            else:
                # Fallback for other response types
                logger.info(f"Response: {str(event)}")
                return event

# Usage
asyncio.run(send_sync_message("what is 101 * 11"))
```

### Streaming Client

For streaming responses, use the streaming client:

```python
import asyncio
import logging
from uuid import uuid4

import httpx
from a2a.client import A2ACardResolver, ClientConfig, ClientFactory
from a2a.types import Message, Part, Role, TextPart

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

DEFAULT_TIMEOUT = 300 # set request timeout to 5 minutes

def create_message(*, role: Role = Role.user, text: str) -> Message:
    return Message(
        kind="message",
        role=role,
        parts=[Part(TextPart(kind="text", text=text))],
        message_id=uuid4().hex,
    )

async def send_streaming_message(message: str, base_url: str = "http://127.0.0.1:9000"):
    async with httpx.AsyncClient(timeout=DEFAULT_TIMEOUT) as httpx_client:
        # Get agent card
        resolver = A2ACardResolver(httpx_client=httpx_client, base_url=base_url)
        agent_card = await resolver.get_agent_card()

        # Create client using factory
        config = ClientConfig(
            httpx_client=httpx_client,
            streaming=True,  # Use streaming mode
        )
        factory = ClientFactory(config)
        client = factory.create(agent_card)

        # Create and send message
        msg = create_message(text=message)

        async for event in client.send_message(msg):
            if isinstance(event, Message):
                logger.info(event.model_dump_json(exclude_none=True, indent=2))
            elif isinstance(event, tuple) and len(event) == 2:
                # (Task, UpdateEvent) tuple
                task, update_event = event
                logger.info(f"Task: {task.model_dump_json(exclude_none=True, indent=2)}")
                if update_event:
                    logger.info(f"Update: {update_event.model_dump_json(exclude_none=True, indent=2)}")
            else:
                # Fallback for other response types
                logger.info(f"Response: {str(event)}")

# Usage
asyncio.run(send_streaming_message("what is 101 * 11"))
```

## Strands A2A Tool

### Installation

To use the A2A client tool, install strands-agents-tools with the A2A extra:

```bash
pip install 'strands-agents-tools[a2a_client]'
```

Strands provides this tool for discovering and interacting with A2A agents without manually writing client code:

```python
import asyncio
import logging
from strands import Agent
from strands_tools.a2a_client import A2AClientToolProvider

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Create A2A client tool provider with known agent URLs
# Assuming you have an A2A server running on 127.0.0.1:9000
# known_agent_urls is optional
provider = A2AClientToolProvider(known_agent_urls=["http://127.0.0.1:9000"])

# Create agent with A2A client tools
agent = Agent(tools=provider.tools)

# The agent can now discover and interact with A2A servers
# Standard usage
response = agent("pick an agent and make a sample call")
logger.info(response)

# Alternative Async usage
# async def main():
#     response = await agent.invoke_async("pick an agent and make a sample call")
#     logger.info(response)
# asyncio.run(main())
```

The A2A client tool provides three main capabilities:

- **Agent Discovery**: Automatically discover available A2A agents and their capabilities
- **Protocol Communication**: Send messages to A2A agents using the standardized protocol
- **Natural Language Interface**: Interact with remote agents using natural language commands

## A2A Agent as a Tool (Manual Approach)

!!! note "Consider using A2AAgent"
    The `A2AAgent` class (described above) provides a simpler way to consume remote A2A agents. The manual approach below gives you more control but requires more code.

A2A agents can be wrapped as tools within your agent's toolkit, similar to the [Agents as Tools](agents-as-tools.md) pattern but leveraging the A2A protocol for cross-platform communication.

You can use a class-based approach to discover agent cards upfront and avoid repeated discovery calls:

```python
import asyncio
from uuid import uuid4
import httpx
from a2a.client import A2ACardResolver, ClientConfig, ClientFactory
from a2a.types import Message, Part, Role, TextPart
from strands import Agent, tool

class A2AAgentTool:
    def __init__(self, agent_url: str, agent_name: str):
        self.agent_url = agent_url
        self.agent_name = agent_name
        self.agent_card = None
        self.client = None

        async with httpx.AsyncClient(timeout=300) as httpx_client:
            resolver = A2ACardResolver(httpx_client=httpx_client, base_url=self.agent_url)
            self.agent_card = await resolver.get_agent_card()
            
            config = ClientConfig(httpx_client=httpx_client, streaming=False)
            factory = ClientFactory(config)
            self.client = factory.create(self.agent_card)
    
    @tool
    async def call_agent(self, message: str) -> str:
        """
        Send a message to the A2A agent.
        
        Args:
            message: The message to send to the agent
            
        Returns:
            Response from the A2A agent
        """
        try:            
            msg = Message(
                kind="message",
                role=Role.user,
                parts=[Part(TextPart(kind="text", text=message))],
                message_id=uuid4().hex,
            )
            
            async for event in self.client.send_message(msg):
                if isinstance(event, Message):
                    response_text = ""
                    for part in event.parts:
                        if hasattr(part, 'text'):
                            response_text += part.text
                    return response_text
                    
            return f"No response received from {self.agent_name}"
            
        except Exception as e:
            return f"Error contacting {self.agent_name}: {str(e)}"

# Usage
research_agent = A2AAgentTool("http://research-agent.example.com:9000", "Research Agent")
calculator_agent = A2AAgentTool("http://calculator-agent.example.com:9000", "Calculator Agent")

orchestrator = Agent(
    tools=[research_agent.call_agent, calculator_agent.call_agent]
)
```

## Troubleshooting

If you encounter bugs or need to request features for A2A support:

1. Check the [A2A documentation](https://a2aproject.github.io/A2A/latest/) for protocol-specific issues
2. Report Strands-specific issues on [GitHub](https://github.com/strands-agents/sdk-python/issues/new/choose)
3. Include relevant error messages and code samples in your reports
