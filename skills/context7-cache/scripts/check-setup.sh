#!/bin/bash
# Check if context7-skill is installed and configured
# Returns 0 if ready, 1 if setup needed

if ! command -v context7-skill &>/dev/null; then
  echo "NOT_INSTALLED"
  echo "Run: npm install -g @m2015agg/context7-skill && context7-skill install --init"
  exit 1
fi

if [ ! -d ".context7-cache" ]; then
  echo "NOT_INITIALIZED"
  echo "Run: context7-skill init"
  exit 1
fi

# Check freshness
context7-skill doctor 2>&1
exit 0
