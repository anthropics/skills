# Strands Valkey Session Manager

{{ community_contribution_banner }}

The [Strands Valkey Session Manager](https://github.com/jeromevdl/strands-valkey-session-manager) is a high-performance session manager for Strands Agents that uses Valkey/Redis for persistent storage. Valkey is a very-low latency cache that enables agents to maintain conversation history and state across multiple interactions, even in distributed environments.

Tested with Amazon ElastiCache Serverless (Redis 7.1, Valkey 8.1), ElastiCache (Redis 7.1, Valkey 8.2), and Upstash.

## Installation

```bash
pip install strands-valkey-session-manager
```

## Usage

### Basic Setup

```python
from strands import Agent
from strands_valkey_session_manager import ValkeySessionManager
from uuid import uuid4
import valkey

# Create a Valkey client
client = valkey.Valkey(host="localhost", port=6379, decode_responses=True)

# Create a session manager with a unique session ID
session_id = str(uuid4())
session_manager = ValkeySessionManager(
    session_id=session_id,
    client=client
)

# Create an agent with the session manager
agent = Agent(session_manager=session_manager)

# Use the agent - all messages are automatically persisted
agent("Hello! Tell me about Valkey.")

# The conversation is now stored in Valkey and can be resumed later using the same session_id

# Display conversation history
messages = session_manager.list_messages(session_id, agent.agent_id)
for msg in messages:
    role = msg.message["role"]
    content = msg.message["content"][0]["text"]
    print(f"** {role.upper()}**: {content}")
```

## Key Features

- **Persistent Sessions**: Store agent conversations and state in Valkey/Redis
- **Distributed Ready**: Share sessions across multiple application instances
- **High Performance**: Leverage Valkey's speed for fast session operations
- **JSON Storage**: Native JSON support for complex data structures
- **Automatic Cleanup**: Built-in session management and cleanup capabilities

## Configuration

### ValkeySessionManager Parameters

- `session_id`: Unique identifier for the session
- `client`: Configured Valkey client instance (only synchronous versions are supported)

### Storage Structure

The ValkeySessionManager stores data using the following key structure:

```
session:<session_id>                                        # Session metadata
session:<session_id>:agent:<agent_id>                       # Agent state and metadata
session:<session_id>:agent:<agent_id>:message:<message_id>  # Individual messages
```

## Available Methods

The following methods are used transparently by Strands:

- `create_session(session)`: Create a new session
- `read_session(session_id)`: Retrieve session data
- `delete_session(session_id)`: Remove session and all associated data
- `create_agent(session_id, agent)`: Store agent in session
- `read_agent(session_id, agent_id)`: Retrieve agent data
- `update_agent(session_id, agent)`: Update agent state
- `create_message(session_id, agent_id, message)`: Store message
- `read_message(session_id, agent_id, message_id)`: Retrieve message
- `update_message(session_id, agent_id, message)`: Update message
- `list_messages(session_id, agent_id, limit=None)`: List all messages

## Requirements

- Python 3.10+
- Valkey/Redis server
- strands-agents >= 1.0.0
- valkey >= 6.0.0

## References

- **PyPI**: [strands-valkey-session-manager](https://pypi.org/project/strands-valkey-session-manager/)
- **GitHub**: [jeromevdl/strands-valkey-session-manager](https://github.com/jeromevdl/strands-valkey-session-manager)
- **Issues**: Report bugs and feature requests in the [GitHub repository](https://github.com/jeromevdl/strands-valkey-session-manager/issues)
