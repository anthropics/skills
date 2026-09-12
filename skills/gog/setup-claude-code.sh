#!/usr/bin/env bash
# setup-claude-code.sh - Set up GOG skills for Claude Code
#
# Claude Code looks for skills in:
# - .claude/skills/ (project-specific)
# - ~/.claude/skills/ (global)
#
# This script creates symlinks so Claude Code can find the GOG skills.

set -euo pipefail

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

# Determine project root (parent of skills/gog)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

echo "GOG Skills Setup for Claude Code"
echo "================================="
echo
echo "Project root: $PROJECT_ROOT"
echo

# Check if skills exist
if [ ! -d "$PROJECT_ROOT/skills/gog" ]; then
  echo "Error: skills/gog directory not found at expected location"
  echo "Expected: $PROJECT_ROOT/skills/gog"
  exit 1
fi

# Count skills
SKILL_COUNT=$(find "$PROJECT_ROOT/skills/gog" -mindepth 1 -maxdepth 1 -type d -name "gog-*" | wc -l | tr -d ' ')
echo "Found $SKILL_COUNT GOG skills"
echo

# Ask user where to install
echo "Where would you like to install the skills?"
echo "1) Project-specific (.claude/skills/ in current directory)"
echo "2) Global (~/.claude/skills/ for all projects)"
echo "3) Both"
echo
read -p "Choice [1]: " choice
choice=${choice:-1}

install_skills() {
  local target_dir="$1"
  local display_name="$2"

  echo
  echo -e "${GREEN}Installing to: $target_dir${NC}"

  # Create target directory
  mkdir -p "$target_dir"

  # Remove existing GOG skill symlinks
  rm -f "$target_dir"/gog-* 2>/dev/null || true

  # Create symlinks for each skill
  for skill_path in "$PROJECT_ROOT"/skills/gog/gog-*/; do
    skill_name=$(basename "$skill_path")

    # Calculate relative path from target to skill
    if [[ "$target_dir" == "$PROJECT_ROOT"* ]]; then
      # Target is in project, use relative path
      rel_path=$(realpath --relative-to="$target_dir" "$skill_path" 2>/dev/null || \
                 python3 -c "import os.path; print(os.path.relpath('$skill_path', '$target_dir'))" 2>/dev/null || \
                 echo "$skill_path")
    else
      # Target is outside project, use absolute path
      rel_path="$skill_path"
    fi

    ln -s "$rel_path" "$target_dir/$skill_name"
    echo "  ✓ Linked: $skill_name"
  done

  echo -e "${GREEN}✓ Installed $SKILL_COUNT skills to $display_name${NC}"
}

case $choice in
  1)
    install_skills "$PROJECT_ROOT/.claude/skills" ".claude/skills/"

    # Add to .gitignore
    if [ -f "$PROJECT_ROOT/.gitignore" ]; then
      if ! grep -q "^\.claude/$" "$PROJECT_ROOT/.gitignore" 2>/dev/null; then
        echo ".claude/" >> "$PROJECT_ROOT/.gitignore"
        echo -e "${YELLOW}Added .claude/ to .gitignore${NC}"
      fi
    fi
    ;;
  2)
    install_skills "$HOME/.claude/skills" "~/.claude/skills/"
    ;;
  3)
    install_skills "$PROJECT_ROOT/.claude/skills" ".claude/skills/"
    install_skills "$HOME/.claude/skills" "~/.claude/skills/"

    # Add to .gitignore
    if [ -f "$PROJECT_ROOT/.gitignore" ]; then
      if ! grep -q "^\.claude/$" "$PROJECT_ROOT/.gitignore" 2>/dev/null; then
        echo ".claude/" >> "$PROJECT_ROOT/.gitignore"
        echo -e "${YELLOW}Added .claude/ to .gitignore${NC}"
      fi
    fi
    ;;
  *)
    echo "Invalid choice"
    exit 1
    ;;
esac

echo
echo "================================="
echo -e "${GREEN}Setup complete!${NC}"
echo
echo "Next steps:"
echo "1. Open Claude Code in this directory (or any directory if you chose global)"
echo "2. Type /skills to see available skills"
echo "3. Use skills by mentioning tasks like:"
echo "   - 'Triage my inbox'"
echo "   - 'What's on my calendar today?'"
echo "   - 'Create a task to follow up'"
echo
echo "For more information, see: skills/gog/README.md"
