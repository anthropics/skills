"""Regression tests for connections.py (anthropics/skills#1668).

Verifies that:
- connections.py imports cleanly under both mcp >= 2.x and mcp < 2.x
- create_connection instantiates the correct connection class for stdio, sse, and http transports
- argument validation operates as expected for missing parameters or unsupported transports
"""

import pytest
import sys
from pathlib import Path

# Add scripts directory to sys.path
SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from connections import (
    create_connection,
    MCPConnectionStdio,
    MCPConnectionSSE,
    MCPConnectionHTTP,
    streamable_http_client,
)


def test_streamable_http_client_imported():
    """Verify that streamable_http_client function is successfully resolved."""
    assert callable(streamable_http_client)


def test_create_stdio_connection():
    """Verify stdio connection creation."""
    conn = create_connection("stdio", command="node", args=["server.js"])
    assert isinstance(conn, MCPConnectionStdio)
    assert conn.command == "node"
    assert conn.args == ["server.js"]


def test_create_sse_connection():
    """Verify sse connection creation."""
    conn = create_connection("sse", url="http://localhost:8000/sse")
    assert isinstance(conn, MCPConnectionSSE)
    assert conn.url == "http://localhost:8000/sse"


def test_create_http_connection():
    """Verify http and streamable_http transport variants."""
    for transport in ["http", "streamable_http", "streamable-http", "HTTP"]:
        conn = create_connection(transport, url="http://localhost:8000/mcp")
        assert isinstance(conn, MCPConnectionHTTP)
        assert conn.url == "http://localhost:8000/mcp"
        # Verify context manager can be created
        ctx = conn._create_context()
        assert ctx is not None


def test_validation_errors():
    """Verify parameter validation."""
    with pytest.raises(ValueError, match="Command is required"):
        create_connection("stdio")

    with pytest.raises(ValueError, match="URL is required"):
        create_connection("sse")

    with pytest.raises(ValueError, match="URL is required"):
        create_connection("http")

    with pytest.raises(ValueError, match="Unsupported transport type"):
        create_connection("invalid_transport")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
