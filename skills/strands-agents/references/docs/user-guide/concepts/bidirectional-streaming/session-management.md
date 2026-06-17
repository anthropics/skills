# Session Management [Experimental]

{{ experimental_feature_warning() }}

Session management for `BidiAgent` provides a mechanism for persisting conversation history and agent state across bidirectional streaming sessions. This enables voice assistants and interactive applications to maintain context and continuity even when connections are restarted or the application is redeployed.

## Overview

A bidirectional streaming session represents all stateful information needed by the agent to function, including:

- Conversation history (messages with audio transcripts)
- Agent state (key-value storage)
- Connection state and configuration
- Tool execution history

Strands provides built-in session persistence capabilities that automatically capture and restore this information, allowing `BidiAgent` to seamlessly continue conversations where they left off, even after connection timeouts or application restarts.

For a comprehensive introduction to session management concepts and general patterns, see the [Session Management documentation](../agents/session-management.md). This guide focuses on bidirectional streaming-specific considerations and use cases.

## Basic Usage

Create a `BidiAgent` with a session manager and use it:

```python
from strands.experimental.bidi import BidiAgent, BidiAudioIO
from strands.experimental.bidi.models import BidiNovaSonicModel
from strands.session.file_session_manager import FileSessionManager

# Create a session manager with a unique session ID
session_manager = FileSessionManager(session_id="user_123_voice_session")

# Create the agent with session management
model = BidiNovaSonicModel()
agent = BidiAgent(
    model=model,
    session_manager=session_manager
)

# Use the agent - all messages are automatically persisted
audio_io = BidiAudioIO()
await agent.run(
    inputs=[audio_io.input()],
    outputs=[audio_io.output()]
)
```

The conversation history is automatically persisted and will be restored on the next session.

## Provider-Specific Considerations

### Gemini Live

!!! warning "Limited Session Management Support"
    Gemini Live does not yet have full session management support due to message history recording limitations in the current implementation. For connection restarts, Gemini Live uses Google's [session handlers](https://ai.google.dev/gemini-api/docs/live-session) to maintain conversation continuity within a single session, but conversation history is not persisted across application restarts.

When using Gemini Live with connection restarts, the model leverages Google's built-in session handler mechanism to maintain context during reconnections within the same session lifecycle.

## Built-in Session Managers

Strands offers two built-in session managers for persisting bidirectional streaming sessions:

1. **FileSessionManager**: Stores sessions in the local filesystem
2. **S3SessionManager**: Stores sessions in Amazon S3 buckets

### FileSessionManager

The `FileSessionManager` provides a simple way to persist sessions to the local filesystem:

```python
from strands.experimental.bidi import BidiAgent
from strands.session.file_session_manager import FileSessionManager

# Create a session manager
session_manager = FileSessionManager(
    session_id="user_123_session",
    storage_dir="/path/to/sessions"  # Optional, defaults to temp directory
)

agent = BidiAgent(
    model=model,
    session_manager=session_manager
)
```

**Use cases:**

- Development and testing
- Single-server deployments
- Local voice assistants
- Prototyping

### S3SessionManager

The `S3SessionManager` stores sessions in Amazon S3 for distributed deployments:

```python
from strands.experimental.bidi import BidiAgent
from strands.session.s3_session_manager import S3SessionManager

# Create an S3 session manager
session_manager = S3SessionManager(
    session_id="user_123_session",
    bucket="my-voice-sessions",
    prefix="sessions/"  # Optional prefix for organization
)

agent = BidiAgent(
    model=model,
    session_manager=session_manager
)
```

**Use cases:**

- Production deployments
- Multi-server environments
- Serverless applications
- High availability requirements

## Session Lifecycle

### Session Creation

Sessions are created automatically when the agent starts:

```python
session_manager = FileSessionManager(session_id="new_session")
agent = BidiAgent(model=model, session_manager=session_manager)

# Session created on first start
await agent.start()
```

### Session Restoration

When an agent starts with an existing session ID, the conversation history is automatically restored:

```python
# First conversation
session_manager = FileSessionManager(session_id="user_123")
agent = BidiAgent(model=model, session_manager=session_manager)
await agent.start()
await agent.send("My name is Alice")
# ... conversation continues ...
await agent.stop()

# Later - conversation history restored
session_manager = FileSessionManager(session_id="user_123")
agent = BidiAgent(model=model, session_manager=session_manager)
await agent.start()  # Previous messages automatically loaded
await agent.send("What's my name?")  # Agent remembers: "Alice"
```

### Session Updates

Messages are persisted automatically as they're added:

```python
agent = BidiAgent(model=model, session_manager=session_manager)
await agent.start()

# Each message automatically saved
await agent.send("Hello")  # Saved
# Model response received and saved
# Tool execution saved
# All transcripts saved
```

## Connection Restart Behavior

When a connection times out and restarts, the session manager ensures continuity:

```python
agent = BidiAgent(model=model, session_manager=session_manager)
await agent.start()

async for event in agent.receive():
    if isinstance(event, BidiConnectionRestartEvent):
        # Connection restarting due to timeout
        # Session manager ensures:
        # 1. All messages up to this point are saved
        # 2. Full history sent to restarted connection
        # 3. Conversation continues seamlessly
        print("Reconnecting with full history preserved")
```

## Integration with Hooks

Session management works seamlessly with hooks:

```python
from strands.experimental.bidi.hooks.events import BidiMessageAddedEvent

class SessionLogger:
    async def on_message_added(self, event: BidiMessageAddedEvent):
        # Message already persisted by session manager
        print(f"Message persisted: {event.message['role']}")

agent = BidiAgent(
    model=model,
    session_manager=session_manager,
    hooks=[SessionLogger()]
)
```

The `BidiMessageAddedEvent` is emitted after the message is persisted, ensuring hooks see the saved state.

For best practices on session ID management, session cleanup, error handling, storage considerations, and troubleshooting, see the [Session Management documentation](../agents/session-management.md).

## Next Steps

- [Agent](agent.md) - Learn about BidiAgent configuration and lifecycle
- [Hooks](hooks.md) - Extend agent functionality with hooks
- [Events](events.md) - Complete guide to bidirectional streaming events
- [API Reference](../../../api-reference/python/experimental/bidi/agent/agent.md) - Complete API documentation
