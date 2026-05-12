#!/bin/bash
# Check if git-skill is installed and configured
# Returns 0 if ready, 1 if setup needed

if ! command -v git-skill &>/dev/null; then
  echo "NOT_INSTALLED"
  echo "Run: npm install -g @m2015agg/git-skill && git-skill config"
  exit 1
fi

if [ ! -d ".git-history" ]; then
  echo "NOT_INITIALIZED"
  echo "Run: git-skill init"
  exit 1
fi

# Check freshness
git-skill doctor 2>&1
exit 0
