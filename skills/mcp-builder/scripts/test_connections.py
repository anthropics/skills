"""Tests for mcp-builder connections factory."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from connections import (
    MCPConnection,
    MCPConnectionHTTP,
    MCPConnectionSSE,
    MCPConnectionStdio,
    create_connection,
)


def test_streamable_http_import_resolved():
    """The streamable HTTP client must be importable regardless of whether the
    installed mcp version exports streamablehttp_client or streamable_http_client."""
    import connections as conn_mod
    assert conn_mod.streamablehttp_client is not None


def test_create_stdio_connection():
    c = create_connection(transport="stdio", command="python", args=["-m", "server"])
    assert isinstance(c, MCPConnectionStdio)
    assert c.command == "python"


def test_create_stdio_requires_command():
    import pytest
    with pytest.raises(ValueError, match="Command is required"):
        create_connection(transport="stdio")


def test_create_sse_connection():
    c = create_connection(transport="sse", url="https://example.com/mcp")
    assert isinstance(c, MCPConnectionSSE)
    assert c.url == "https://example.com/mcp"


def test_create_http_connection():
    c = create_connection(transport="http", url="https://example.com/mcp")
    assert isinstance(c, MCPConnectionHTTP)
    assert c.url == "https://example.com/mcp"


def test_create_http_aliases():
    for alias in ("streamable_http", "streamable-http"):
        c = create_connection(transport=alias, url="https://example.com/mcp")
        assert isinstance(c, MCPConnectionHTTP)


def test_create_sse_requires_url():
    import pytest
    with pytest.raises(ValueError, match="URL is required"):
        create_connection(transport="sse")


def test_unsupported_transport():
    import pytest
    with pytest.raises(ValueError, match="Unsupported transport"):
        create_connection(transport="ftp")
