#!/usr/bin/env bash
# Run the eval dashboard scoped to ONE skill, so the portless URL reflects
# the skill name. Useful when running multiple parallel optimizations across
# tmux windows — each gets its own subdomain instead of colliding on
# `skill-eval.localhost`.
#
# Usage:
#   ./start-for-skill.sh <skill-name>
#
# Examples:
#   ./start-for-skill.sh medusa-pro     → http://eval-medusa-pro.localhost:1355
#   ./start-for-skill.sh drizzle-pro    → http://eval-drizzle-pro.localhost:1355
#   ./start-for-skill.sh stripe-pro     → http://eval-stripe-pro.localhost:1355
#
# All can run simultaneously — different subdomains, different ephemeral
# ports, no portless route conflicts.
set -euo pipefail

SKILL="${1:-}"
if [ -z "$SKILL" ]; then
  echo "Usage: $0 <skill-name>" >&2
  echo "  e.g. $0 medusa-pro" >&2
  exit 1
fi

SKILL_DIR="$HOME/.claude/skills/$SKILL"
if [ ! -f "$SKILL_DIR/SKILL.md" ]; then
  echo "Error: no skill '$SKILL' at $SKILL_DIR (no SKILL.md found)" >&2
  echo "Available skills:" >&2
  ls -1 "$HOME/.claude/skills/" 2>/dev/null | head -20 >&2
  exit 1
fi

cd "$(dirname "$0")"

# Tell the FastAPI server to pre-select this skill in the dashboard
# and limit /api/skills to it.
export SKILL_FILTER="$SKILL"

# portless service name = "eval-<skill>" → "eval-<skill>.localhost:<proxy_port>"
exec portless "eval-$SKILL" ./start.sh
