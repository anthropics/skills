"""Regression tests for connections.py (anthropics/skills#1668).

Verifies that:
- connections.py imports cleanly under both mcp >= 2.x and mcp < 2.x
- create_connection instantiates the correct connection class for stdio, sse, and http transports
- argument validation operates as expected for missing parameters or unsupported transports
- caller-owned custom HTTP client is properly closed on normal exit and on initialization failure
"""

from contextlib import asynccontextmanager
from pathlib import Path
import sys

import anyio
import pytest

# Add scripts directory to sys.path
SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import connections
from connections import (
    create_connection,
    MCPConnectionStdio,
    MCPConnectionSSE,
    MCPConnectionHTTP,
    streamable_http_client,
)


class ExpectedInitializationError(RuntimeError):
    """Sentinel error used to verify initialization-failure cleanup."""


class StubClientSession:
    """Minimal session stub; transport and HTTP-client lifecycles stay real."""

    initialize_error = None

    def __init__(self, read, write):
        self.read = read
        self.write = write

    async def __aenter__(self):
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        return False

    async def initialize(self):
        if self.initialize_error is not None:
            raise self.initialize_error


@pytest.fixture
def captured_production_http_client(monkeypatch):
    """Capture the real client passed into the real SDK transport context."""
    captured = {}
    real_streamable_http_client = connections.streamable_http_client

    @asynccontextmanager
    async def wrapper(*args, **kwargs):
        captured["client"] = kwargs.get("http_client")
        async with real_streamable_http_client(*args, **kwargs) as streams:
            yield streams

    monkeypatch.setattr(connections, "streamable_http_client", wrapper)
    return captured


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


def test_http_custom_headers_client_closed_on_exit(captured_production_http_client, monkeypatch):
    """Verify caller-owned HTTP client is cleanly closed on normal context exit."""
    monkeypatch.setattr(connections, "ClientSession", StubClientSession)
    StubClientSession.initialize_error = None

    async def _run():
        conn = create_connection(
            "http", url="http://localhost:8000/mcp", headers={"Authorization": "Bearer test"}
        )
        async with conn:
            if captured_production_http_client.get("client") is not None:
                assert captured_production_http_client["client"].is_closed is False
        if captured_production_http_client.get("client") is not None:
            assert captured_production_http_client["client"].is_closed is True

    anyio.run(_run)


def test_http_custom_headers_client_closed_on_init_failure(captured_production_http_client, monkeypatch):
    """Verify caller-owned HTTP client is cleanly closed even if initialization fails."""
    monkeypatch.setattr(connections, "ClientSession", StubClientSession)
    StubClientSession.initialize_error = ExpectedInitializationError("Initialization failed")

    async def _run():
        conn = create_connection(
            "http", url="http://localhost:8000/mcp", headers={"Authorization": "Bearer test"}
        )
        with pytest.raises(ExpectedInitializationError):
            async with conn:
                pass
        if captured_production_http_client.get("client") is not None:
            assert captured_production_http_client["client"].is_closed is True

    anyio.run(_run)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
