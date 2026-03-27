---
name: install-mcp
description: Install and configure the markitdown-mcp server, which provides an MCP (Model Context Protocol) server for converting files to Markdown using the MarkItDown library. Use when setting up markitdown-mcp for integration with LLM applications like Claude Desktop.
---

# Install MarkItDown MCP Server

## Overview

The `markitdown-mcp` package provides a lightweight MCP server for converting various file formats to Markdown using the MarkItDown library. It supports STDIO, Streamable HTTP, and SSE transports.

It exposes one tool: `convert_to_markdown(uri)`, where `uri` can be any `http:`, `https:`, `file:`, or `data:` URI.

## Supported File Formats

- PDF
- PowerPoint (.pptx)
- Word (.docx)
- Excel (.xlsx, .xls)
- Images (EXIF metadata and OCR)
- Audio (EXIF metadata and speech transcription)
- HTML
- Text-based formats (CSV, JSON, XML)
- ZIP files
- YouTube URLs
- EPubs

---

## Installation

### Via pip (recommended)

```bash
pip install markitdown-mcp
```

This will install the MCP server along with the markitdown library and all dependencies.

### From source

```bash
git clone https://github.com/microsoft/markitdown.git
cd markitdown
pip install -e 'packages/markitdown[all]'
pip install -e 'packages/markitdown-mcp'
```

Or use the provided install script:

```bash
./install-mcp.sh
```

### Via Docker

```bash
docker build -t markitdown-mcp:latest -f packages/markitdown-mcp/Dockerfile packages/markitdown-mcp/
docker run -it --rm markitdown-mcp:latest
```

---

## Running the Server

### STDIO (default)

```bash
markitdown-mcp
```

### Streamable HTTP / SSE

```bash
markitdown-mcp --http --host 127.0.0.1 --port 3001
```

---

## Configuration for Claude Desktop

Edit `claude_desktop_config.json` to include:

### Using pip install

```json
{
  "mcpServers": {
    "markitdown": {
      "command": "markitdown-mcp"
    }
  }
}
```

### Using Docker

```json
{
  "mcpServers": {
    "markitdown": {
      "command": "docker",
      "args": ["run", "--rm", "-i", "markitdown-mcp:latest"]
    }
  }
}
```

### With local file access (Docker)

```json
{
  "mcpServers": {
    "markitdown": {
      "command": "docker",
      "args": [
        "run", "--rm", "-i",
        "-v", "/path/to/local/data:/workdir",
        "markitdown-mcp:latest"
      ]
    }
  }
}
```

---

## Environment Variables

- `MARKITDOWN_ENABLE_PLUGINS` - Set to `true` to enable third-party MarkItDown plugins (default: `false`)

## Debugging

Use the MCP Inspector:

```bash
npx @modelcontextprotocol/inspector
```

Then connect using STDIO with command `markitdown-mcp`, or Streamable HTTP at `http://127.0.0.1:3001/mcp`.
