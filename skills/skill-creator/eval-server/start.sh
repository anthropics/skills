#!/usr/bin/env bash
# Bootstrap + run the skill-creator eval dashboard server.
# Use `portless eval ./start.sh` from this directory to expose at http://eval.local
set -euo pipefail

cd "$(dirname "$0")"

if [ ! -d .venv ]; then
  python3 -m venv .venv
fi

# Install deps if not present
if ! .venv/bin/python -c "import fastapi, uvicorn" 2>/dev/null; then
  .venv/bin/pip install --upgrade pip >/dev/null
  .venv/bin/pip install -r requirements.txt
fi

# Bind 0.0.0.0 so portless can reach it from the host network namespace
HOST="${HOST:-127.0.0.1}"
PORT="${PORT:-8765}"
exec .venv/bin/python -m uvicorn server:app --host "$HOST" --port "$PORT" --log-level info
