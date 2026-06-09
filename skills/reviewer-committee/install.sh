#!/bin/bash
# Install reviewer-committee skill for Claude Code
# Run from any location: bash /path/to/reviewer-committee/install.sh

set -e

SKILL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
COMMANDS_DIR="$HOME/.claude/commands"

# --- Pre-flight checks ---
missing=()
command -v codex  >/dev/null 2>&1 || missing+=("codex  → npm install -g @openai/codex")
command -v gemini >/dev/null 2>&1 || missing+=("gemini → npm install -g @google/gemini-cli")
command -v python3 >/dev/null 2>&1 || missing+=("python3")

if [ ${#missing[@]} -ne 0 ]; then
  echo "Warning: the following dependencies were not found:"
  for m in "${missing[@]}"; do
    echo "  - $m"
  done
  echo ""
  echo "The skill will install, but reviews will fail until these are available."
  echo ""
fi

# --- Install command files ---
mkdir -p "$COMMANDS_DIR"

cp "$SKILL_DIR/SKILL.md"                "$COMMANDS_DIR/reviewer-committee.md"
cp "$SKILL_DIR/commands/review.md"       "$COMMANDS_DIR/review.md"
cp "$SKILL_DIR/commands/review-diff.md"  "$COMMANDS_DIR/review-diff.md"
cp "$SKILL_DIR/commands/review-commit.md" "$COMMANDS_DIR/review-commit.md"

# --- Set env var so commands can find the script directory ---
SETTINGS_FILE="$HOME/.claude/settings.json"
if [ -f "$SETTINGS_FILE" ]; then
  # Add env var to existing settings if not already present
  if python3 -c "
import json, sys
with open('$SETTINGS_FILE') as f:
    s = json.load(f)
env = s.setdefault('env', {})
if env.get('REVIEWER_COMMITTEE_DIR') == '$SKILL_DIR':
    sys.exit(1)
env['REVIEWER_COMMITTEE_DIR'] = '$SKILL_DIR'
with open('$SETTINGS_FILE', 'w') as f:
    json.dump(s, f, indent=2)
" 2>/dev/null; then
    echo "Set REVIEWER_COMMITTEE_DIR in $SETTINGS_FILE"
  fi
else
  # Create settings file with the env var
  mkdir -p "$(dirname "$SETTINGS_FILE")"
  cat > "$SETTINGS_FILE" <<EOJSON
{
  "env": {
    "REVIEWER_COMMITTEE_DIR": "$SKILL_DIR"
  }
}
EOJSON
  echo "Created $SETTINGS_FILE with REVIEWER_COMMITTEE_DIR"
fi

echo ""
echo "Installed reviewer-committee to $COMMANDS_DIR:"
echo "  reviewer-committee  — main skill (invoked by Skill tool)"
echo "  /review             — committee review of uncommitted changes"
echo "  /review-diff        — committee review vs a base branch"
echo "  /review-commit      — committee review of a specific commit"
echo ""
echo "Usage: open any project in Claude Code and run /review"
