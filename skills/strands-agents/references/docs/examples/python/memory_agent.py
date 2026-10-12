#!/usr/bin/env python3
"""
# 🧠 Memory Agent

A demonstration of using Strands Agents' memory capabilities to store and retrieve information.

## What This Example Shows

This example demonstrates:
- Creating an agent with memory capabilities
- Storing information for later retrieval
- Retrieving relevant memories based on context
- Using memory to create personalized responses

## Usage Examples

Basic usage:
```
python memory_agent.py
```

Import in your code:
```python
from examples.basic.memory_agent import memory_agent

# Store a memory
response = memory_agent("Remember that I prefer tea over coffee")
print(response["message"]["content"][0]["text"])

# Retrieve memories
response = memory_agent("What do I prefer to drink?")
print(response["message"]["content"][0]["text"])
```

## Memory Operations

1. **Store Information**:
   - "Remember that I like hiking"
   - "Note that I have a dog named Max"
   - "I want you to know I prefer window seats"

2. **Retrieve Information**:
   - "What do you know about me?"
   - "What are my hobbies?"
   - "Do I have any pets?"

3. **List All Memories**:
   - "Show me everything you remember"
   - "What memories do you have stored?"
"""

import os
import logging
from dotenv import load_dotenv

from strands import Agent
from strands_tools import mem0_memory, use_llm

logger = logging.getLogger(__name__)

# Load environment variables from .env file if it exists
load_dotenv()

# Set AWS credentials and configuration
# os.environ["AWS_REGION"] = "us-west-2"
# os.environ['OPENSEARCH_HOST'] = "your-opensearch-host.us-west-2.aoss.amazonaws.com"
# os.environ['AWS_ACCESS_KEY_ID'] = "your-aws-access-key-id"
# os.environ['AWS_SECRET_ACCESS_KEY'] = "your-aws-secret-access-key"

# For graph memory with Neptune, see:
# https://docs.mem0.ai/open-source/features/graph-memory
# Two options are available for Neptune integration:

# Setup option 1: Neptune Database as graph backend
# os.environ['NEPTUNE_DATABASE_ENDPOINT'] = "your-neptune-host.us-west-2.neptune.amazonaws.com"
# Setup option 2: Neptune Analytics as vector and graph backend
# os.environ['NEPTUNE_ANALYTICS_GRAPH_IDENTIFIER'] = "g-sample-graph-id"
USER_ID = "mem0_user"

# System prompt for the memory agent
MEMORY_SYSTEM_PROMPT = f"""You are a personal assistant that maintains context by remembering user details.

Capabilities:
- Store new information using mem0_memory tool (action="store")
- Retrieve relevant memories (action="retrieve")
- List all memories (action="list")
- Provide personalized responses

Key Rules:
- Always include user_id={USER_ID} in tool calls
- Be conversational and natural in responses
- Format output clearly
- Acknowledge stored information
- Only share relevant information
- Politely indicate when information is unavailable
"""

# Create an agent with memory capabilities
memory_agent = Agent(
    system_prompt=MEMORY_SYSTEM_PROMPT,
    tools=[mem0_memory, use_llm],
)

# Initialize some demo memories
def initialize_demo_memories():
    """Initialize some demo memories to showcase functionality."""
    content = """My name is Alex. I like to travel and stay in Airbnbs rather than hotels. I am planning a trip to Japan next spring. I enjoy hiking and outdoor photography as hobbies. I have a dog named Max. My favorite cuisine is Italian food."""  # noqa
    memory_agent.tool.mem0_memory(action="store", content=content, user_id=USER_ID)

# Example usage
if __name__ == "__main__":
    print("\n🧠 Memory Agent 🧠\n")
    print("This example demonstrates using Strands Agents' memory capabilities")
    print("to store and retrieve information.")
    print("\nOptions:")
    print("  'demo' - Initialize demo memories")
    print("  'exit' - Exit the program")
    print("\nOr try these examples:")
    print("  - Remember that I prefer window seats on flights")
    print("  - What do you know about me?")
    print("  - What are my travel preferences?")
    print("  - Do I have any pets?")

    # Interactive loop
    while True:
        try:
            user_input = input("\n> ")

            if user_input.lower() == "exit":
                print("\nGoodbye! 👋")
                break
            elif user_input.lower() == "demo":
                initialize_demo_memories()
                print("\nDemo memories initialized!")
                continue

            # Call the memory agent
            memory_agent(user_input)

        except KeyboardInterrupt:
            print("\n\nExecution interrupted. Exiting...")
            break
        except Exception as e:
            print(f"\nAn error occurred: {str(e)}")
            print("Please try a different request.")
