#!/usr/bin/env bash
# Bootstrap + run the skill_eval MCP server (stdio transport).
# Stdio is JSON-RPC only — all logging goes to stderr.
set -euo pipefail

cd "$(dirname "$0")"

if [ ! -d .venv ]; then
  python3 -m venv .venv >&2
fi

if ! .venv/bin/python -c "import mcp" 2>/dev/null; then
  .venv/bin/pip install --upgrade pip >&2 >/dev/null
  .venv/bin/pip install -r requirements.txt >&2
fi

exec .venv/bin/python -u server.py
