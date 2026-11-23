#!/bin/sh
# Playwright MCP only reads script files inside the project (allowed roots), not the skill folder.
# Run this once per session from the project root; then pass .playwright-mcp/qa/<script>.js as `filename`.
set -e
DEST="${1:-.playwright-mcp/qa}"
mkdir -p "$DEST"
cp "$(dirname "$0")"/*.js "$DEST"/
echo "staged $(ls "$(dirname "$0")"/*.js | wc -l | tr -d ' ') browser scripts into $DEST"
