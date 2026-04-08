"""
MCP Calculator Example

This example demonstrates how to:
1. Create a simple MCP server that provides calculator functionality
2. Connect a Strands agent to the MCP server
3. Use the calculator tools through natural language
"""

import threading
import time

from mcp.client.streamable_http import streamablehttp_client
from mcp.server import FastMCP
from strands import Agent
from strands.tools.mcp.mcp_client import MCPClient


def start_calculator_server():
    """
    Initialize and start an MCP calculator server.

    This function creates a FastMCP server instance that provides calculator tools
    for performing basic arithmetic operations. The server uses Streamable HTTP
    transport for communication.
    """
    # Create an MCP server with a descriptive name
    mcp = FastMCP("Calculator Server")

    # Define a simple addition tool
    @mcp.tool(description="Add two numbers together")
    def add(x: int, y: int) -> int:
        """Add two numbers and return the result.

        Args:
            x: First number
            y: Second number

        Returns:
            The sum of x and y
        """
        return x + y

    # Define a subtraction tool
    @mcp.tool(description="Subtract one number from another")
    def subtract(x: int, y: int) -> int:
        """Subtract y from x and return the result.

        Args:
            x: Number to subtract from
            y: Number to subtract

        Returns:
            The difference (x - y)
        """
        return x - y

    # Define a multiplication tool
    @mcp.tool(description="Multiply two numbers together")
    def multiply(x: int, y: int) -> int:
        """Multiply two numbers and return the result.

        Args:
            x: First number
            y: Second number

        Returns:
            The product of x and y
        """
        return x * y

    # Define a division tool
    @mcp.tool(description="Divide one number by another")
    def divide(x: float, y: float) -> float:
        """Divide x by y and return the result.

        Args:
            x: Numerator
            y: Denominator (must not be zero)

        Returns:
            The quotient (x / y)

        Raises:
            ValueError: If y is zero
        """
        if y == 0:
            raise ValueError("Cannot divide by zero")
        return x / y

    # Run the server with Streamable HTTP transport on the default port (8000)
    print("Starting MCP Calculator Server on http://localhost:8000")
    mcp.run(transport="streamable-http")


def main():
    """
    Main function that starts the MCP server in a background thread
    and creates a Strands agent that uses the MCP tools.
    """
    # Start the MCP server in a background thread
    server_thread = threading.Thread(target=start_calculator_server, daemon=True)
    server_thread.start()

    # Wait for the server to start
    print("Waiting for MCP server to start...")
    time.sleep(2)

    # Connect to the MCP server using Streamable HTTP transport
    print("Connecting to MCP server...")

    def create_streamable_http_transport():
        return streamablehttp_client("http://localhost:8000/mcp/")

    streamable_http_mcp_client = MCPClient(create_streamable_http_transport)

    # Create a system prompt that explains the calculator capabilities
    system_prompt = """
    You are a helpful calculator assistant that can perform basic arithmetic operations.
    You have access to the following calculator tools:
    - add: Add two numbers together
    - subtract: Subtract one number from another
    - multiply: Multiply two numbers together
    - divide: Divide one number by another
    
    When asked to perform calculations, use the appropriate tool rather than calculating the result yourself.
    Explain the calculation and show the result clearly.
    """

    # Use the MCP client in a context manager
    with streamable_http_mcp_client:
        # Get the tools from the MCP server
        tools = streamable_http_mcp_client.list_tools_sync()

        print(f"Available MCP tools: {[tool.tool_name for tool in tools]}")

        # Create an agent with the MCP tools
        agent = Agent(system_prompt=system_prompt, tools=tools)

        # Interactive loop
        print("\nCalculator Agent Ready! Type 'exit' to quit.\n")
        while True:
            # Get user input
            user_input = input("Question: ")

            # Check if the user wants to exit
            if user_input.lower() in ["exit", "quit"]:
                break

            # Process the user's request
            print("\nThinking...\n")
            response = agent(user_input)

            # Print the agent's response
            print(f"Answer: {response}\n")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nExiting...")
