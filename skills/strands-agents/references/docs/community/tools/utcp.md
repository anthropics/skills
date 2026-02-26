# Universal Tool Calling Protocol (UTCP)

{{ community_contribution_banner }}

The [Universal Tool Calling Protocol (UTCP)](https://www.utcp.io/) is a lightweight, secure, and scalable standard that enables AI agents to discover and call tools directly using their native protocols - **no wrapper servers required**. UTCP acts as a "manual" that tells agents how to call your tools directly, extending OpenAPI for AI agents while maintaining full backward compatibility.

This community plugin integrates UTCP with [Strands Agents SDK](https://github.com/strands-agents/sdk-python), providing standardized tool discovery and execution capabilities.

## Installation

```bash
pip install strands-agents strands-utcp
```

## Usage

```python
from strands import Agent
from strands_utcp import UtcpToolAdapter

# Configure UTCP tool adapter
config = {
    "manual_call_templates": [
        {
            "name": "weather_api",
            "call_template_type": "http",
            "url": "https://api.weather.com/utcp",
            "http_method": "GET"
        }
    ]
}

# Use UTCP tools with Strands agent
async def main():
    async with UtcpToolAdapter(config) as adapter:
        # Get available tools
        tools = adapter.list_tools()
        print(f"Found {len(tools)} UTCP tools")
        
        # Create agent with UTCP tools
        agent = Agent(tools=adapter.to_strands_tools())
        
        # Use the agent
        response = await agent.invoke_async("What's the weather like today?")
        print(response.message)

import asyncio
asyncio.run(main())
```

## Key Features

- **Universal Tool Access**: Connect to any UTCP-compatible tool source
- **OpenAPI/Swagger Support**: Automatic tool discovery from API specifications
- **Multiple Sources**: Connect to multiple tool sources simultaneously
- **Async/Await Support**: Full async support with context managers
- **Type Safe**: Full type hints and validation
- **Easy Integration**: Drop-in tool adapter for Strands agents

## Resources

- **GitHub**: [universal-tool-calling-protocol/python-utcp](https://github.com/universal-tool-calling-protocol/python-utcp)
- **PyPI**: [strands-utcp](https://pypi.org/project/strands-utcp/)