# AgentCore Memory Session Manager

{{ community_contribution_banner }}

The [AgentCore Memory Session Manager](https://github.com/aws/bedrock-agentcore-sdk-python/tree/main/src/bedrock_agentcore/memory/integrations/strands) leverages Amazon Bedrock AgentCore Memory to provide advanced memory capabilities with intelligent retrieval for Strands Agents. It supports both short-term memory (STM) for conversation persistence and long-term memory (LTM) with multiple strategies for learning user preferences, facts, and session summaries.

## Installation

```bash
pip install 'bedrock-agentcore[strands-agents]'
```

## Usage

### Basic Setup (STM)


Short-term memory provides basic conversation persistence within a session. This is the simplest way to get started with AgentCore Memory.

#### Creating the Memory Resource

!!! note "One-time Setup"
    The memory resource creation shown below is typically done once, separately from your agent application. In production, you would create the memory resource through the AWS Console or a separate setup script, then use the memory ID in your agent application.

```python
import os
from bedrock_agentcore.memory import MemoryClient

# This is typically done once, separately from your agent application
client = MemoryClient(region_name="us-east-1")
basic_memory = client.create_memory(
    name="BasicTestMemory",
    description="Basic memory for testing short-term functionality"
)

# Export the memory ID as an environment variable for reuse
memory_id = basic_memory.get('id')
print(f"Created memory with ID: {memory_id}")
os.environ['AGENTCORE_MEMORY_ID'] = memory_id
```


### Using the Session Manager with Existing Memory

```python
import uuid
import boto3
from datetime import datetime
from strands import Agent
from bedrock_agentcore.memory.integrations.strands.config import AgentCoreMemoryConfig
from bedrock_agentcore.memory.integrations.strands.session_manager import AgentCoreMemorySessionManager


MEM_ID = os.environ.get("AGENTCORE_MEMORY_ID", "your-existing-memory-id")
ACTOR_ID = "test_actor_id_%s" % datetime.now().strftime("%Y%m%d%H%M%S")
SESSION_ID = "test_session_id_%s" % datetime.now().strftime("%Y%m%d%H%M%S")

agentcore_memory_config = AgentCoreMemoryConfig(
    memory_id=MEM_ID,
    session_id=SESSION_ID,
    actor_id=ACTOR_ID
)

# Use context manager to ensure messages are flushed on exit
with AgentCoreMemorySessionManager(
    agentcore_memory_config=agentcore_memory_config,
    region_name="us-east-1"
) as session_manager:
    # Create agent with session manager
    agent = Agent(
        system_prompt="You are a helpful assistant. Use all you know about the user to provide helpful responses.",
        session_manager=session_manager,
    )

    # Use the agent - conversations are automatically persisted
    agent("I like sushi with tuna")
    agent("What should I buy for lunch today?")
```


## Long-Term Memory (LTM)

Long-term memory provides advanced capabilities with multiple strategies for learning and storing user preferences, facts, and session summaries across conversations.

### Creating LTM Memory with Strategies

!!! note "One-time Setup"
    Similar to STM, the LTM memory resource creation is typically done once, separately from your agent application. In production, you would create the memory resource with strategies through the AWS Console or a separate setup script.

Bedrock AgentCore Memory supports three built-in memory strategies:

1. **`summaryMemoryStrategy`**: Summarizes conversation sessions
2. **`userPreferenceMemoryStrategy`**: Learns and stores user preferences
3. **`semanticMemoryStrategy`**: Extracts and stores factual information

```python
import os
from bedrock_agentcore.memory import MemoryClient

# This is typically done once, separately from your agent application
client = MemoryClient(region_name="us-east-1")
comprehensive_memory = client.create_memory_and_wait(
    name="ComprehensiveAgentMemory",
    description="Full-featured memory with all built-in strategies",
    strategies=[
        {
            "summaryMemoryStrategy": {
                "name": "SessionSummarizer",
                "namespaces": ["/summaries/{actorId}/{sessionId}"]
            }
        },
        {
            "userPreferenceMemoryStrategy": {
                "name": "PreferenceLearner",
                "namespaces": ["/preferences/{actorId}"]
            }
        },
        {
            "semanticMemoryStrategy": {
                "name": "FactExtractor",
                "namespaces": ["/facts/{actorId}"]
            }
        }
    ]
)

# Export the LTM memory ID as an environment variable for reuse
ltm_memory_id = comprehensive_memory.get('id')
print(f"Created LTM memory with ID: {ltm_memory_id}")
os.environ['AGENTCORE_LTM_MEMORY_ID'] = ltm_memory_id
```


### Configuring Retrieval

You can configure how the agent retrieves information from different memory namespaces:

#### Single Namespace Retrieval

```python
from datetime import datetime
from bedrock_agentcore.memory.integrations.strands.config import AgentCoreMemoryConfig, RetrievalConfig
from bedrock_agentcore.memory.integrations.strands.session_manager import AgentCoreMemorySessionManager
from strands import Agent

MEM_ID = os.environ.get("AGENTCORE_LTM_MEMORY_ID", "your-existing-ltm-memory-id")
ACTOR_ID = "test_actor_id_%s" % datetime.now().strftime("%Y%m%d%H%M%S")
SESSION_ID = "test_session_id_%s" % datetime.now().strftime("%Y%m%d%H%M%S")

config = AgentCoreMemoryConfig(
    memory_id=MEM_ID,
    session_id=SESSION_ID,
    actor_id=ACTOR_ID,
    retrieval_config={
        "/preferences/{actorId}": RetrievalConfig(
            top_k=5,
            relevance_score=0.7
        )
    }
)

session_manager = AgentCoreMemorySessionManager(config, region_name='us-east-1')
ltm_agent = Agent(session_manager=session_manager)
```

#### Multiple Namespace Retrieval

```python
config = AgentCoreMemoryConfig(
    memory_id=MEM_ID,
    session_id=SESSION_ID,
    actor_id=ACTOR_ID,
    retrieval_config={
        "/preferences/{actorId}": RetrievalConfig(
            top_k=5,
            relevance_score=0.7
        ),
        "/facts/{actorId}": RetrievalConfig(
            top_k=10,
            relevance_score=0.3
        ),
        "/summaries/{actorId}/{sessionId}": RetrievalConfig(
            top_k=5,
            relevance_score=0.5
        )
    }
)

session_manager = AgentCoreMemorySessionManager(config, region_name='us-east-1')
agent_with_multiple_namespaces = Agent(session_manager=session_manager)
```


## Configuration Options


### Memory Strategies

AgentCore Memory supports three built-in strategies:

1. **`summaryMemoryStrategy`**: Automatically summarizes conversation sessions for efficient context retrieval
2. **`userPreferenceMemoryStrategy`**: Learns and stores user preferences across sessions
3. **`semanticMemoryStrategy`**: Extracts and stores factual information from conversations

### AgentCoreMemoryConfig Parameters

The `AgentCoreMemoryConfig` class accepts the following parameters:

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `memory_id` | `str` | Yes | ID of the Bedrock AgentCore Memory resource |
| `session_id` | `str` | Yes | Unique identifier for the conversation session |
| `actor_id` | `str` | Yes | Unique identifier for the user/actor |
| `retrieval_config` | `Dict[str, RetrievalConfig]` | No | Dictionary mapping namespaces to retrieval configurations |
| `batch_size` | `int` | No (default: 1) | Number of messages to buffer before sending (1-100). Set to 1 for immediate sending. |

### RetrievalConfig Parameters

Configure retrieval behavior for each namespace:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `top_k` | `int` | 10 | Number of top-scoring records to return from semantic search (1-1000) |
| `relevance_score` | `float` | 0.2 | Minimum relevance threshold for filtering results (0.0-1.0) |
| `strategy_id` | `Optional[str]` | None | Optional parameter to filter memory strategies |

### Namespace Patterns

Namespaces follow specific patterns with variable substitution:

- `/preferences/{actorId}`: User-specific preferences across sessions
- `/facts/{actorId}`: User-specific facts across sessions
- `/summaries/{actorId}/{sessionId}`: Session-specific summaries

The `{actorId}` and `{sessionId}` placeholders are automatically replaced with the values from your configuration.

See the following docs for more on namespaces: [Memory scoping with namespaces](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/session-actor-namespace.html)


## Message Batching

By default, each message is sent to AgentCore Memory immediately (`batch_size=1`). When you set `batch_size` to a value greater than 1, messages are buffered locally and sent in a single API call once the buffer reaches the configured size. This reduces the number of API calls and can improve throughput for high-volume conversations.

!!! warning "Flush buffered messages before exiting"
    When using `batch_size > 1`, messages remain in a local buffer until the batch is full. You **must** use a `with` block (recommended) or call `close()` explicitly to flush any remaining messages at the end of your session. Otherwise, buffered messages will be lost.

### Context Manager (Recommended)

The context manager pattern automatically flushes pending messages when the block exits, even if an exception occurs:

```python
from strands import Agent
from bedrock_agentcore.memory.integrations.strands.config import AgentCoreMemoryConfig
from bedrock_agentcore.memory.integrations.strands.session_manager import AgentCoreMemorySessionManager

config = AgentCoreMemoryConfig(
    memory_id="your-memory-id",
    session_id="your-session-id",
    actor_id="your-actor-id",
    batch_size=10,  # Buffer 10 messages before sending
)

with AgentCoreMemorySessionManager(config, region_name="us-east-1") as session_manager:
    agent = Agent(
        system_prompt="You are a helpful assistant.",
        session_manager=session_manager,
    )
    agent("Hello!")
    agent("Tell me about Python.")
# All buffered messages are automatically flushed here
```

### Explicit close()

If you cannot use a context manager, call `close()` in a `finally` block to ensure messages are flushed:

```python
session_manager = AgentCoreMemorySessionManager(config, region_name="us-east-1")
try:
    agent = Agent(
        system_prompt="You are a helpful assistant.",
        session_manager=session_manager,
    )
    agent("Hello!")
    agent("Tell me about Python.")
finally:
    session_manager.close()  # Flush any remaining buffered messages
```

### Checking Buffer Status

Use `pending_message_count()` to check how many messages are waiting in the buffer:

```python
count = session_manager.pending_message_count()
print(f"{count} messages pending in buffer")
```


## Important Notes

!!! note "Session Limitations"
    Currently, only **one** agent per session is supported when using AgentCoreMemorySessionManager. Creating multiple agents with the same session will show a warning.

!!! note "Flush Buffered Messages"
    When using `batch_size > 1`, always use a `with` block or call `close()` when your session is complete. Any messages remaining in the buffer that are not flushed will be lost.

## Resources

- **GitHub**: [bedrock-agentcore-sdk-python](https://github.com/aws/bedrock-agentcore-sdk-python/)
- **Documentation**: [Strands Integration Examples](https://github.com/aws/bedrock-agentcore-sdk-python/tree/main/src/bedrock_agentcore/memory/integrations/strands)
- **Issues**: Report bugs and feature requests in the [bedrock-agentcore-sdk-python repository](https://github.com/aws/bedrock-agentcore-sdk-python/issues/new/choose)
