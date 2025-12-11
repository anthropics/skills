#!/usr/bin/env bash
# Quick codebase analysis using tokei, fd, and rg
# Usage: ./analyze-codebase.sh [directory]

set -euo pipefail

DIR="${1:-.}"

echo "=== Codebase Analysis ==="
echo "Directory: $DIR"
echo ""

# Check required tools
MISSING=()
for cmd in tokei fd rg; do
    if ! command -v "$cmd" &> /dev/null; then
        MISSING+=("$cmd")
    fi
done

if [ ${#MISSING[@]} -gt 0 ]; then
    echo "Missing tools: ${MISSING[*]}"
    echo "Install with: brew install ${MISSING[*]}"
    exit 1
fi

cd "$DIR"

# Code statistics
echo "--- Code Statistics ---"
tokei . --sort lines
echo ""

# File counts
echo "--- File Counts ---"
echo "Total files: $(fd -t f | wc -l | tr -d ' ')"
echo "TypeScript files: $(fd -e ts -e tsx | wc -l | tr -d ' ')"
echo "JavaScript files: $(fd -e js -e jsx | wc -l | tr -d ' ')"
echo "Python files: $(fd -e py | wc -l | tr -d ' ')"
echo "Shell scripts: $(fd -e sh | wc -l | tr -d ' ')"
echo "YAML files: $(fd -e yaml -e yml | wc -l | tr -d ' ')"
echo "JSON files: $(fd -e json | wc -l | tr -d ' ')"
echo ""

# TODO/FIXME counts
echo "--- Code Health ---"
TODO_COUNT=$(rg -c "TODO" 2>/dev/null | awk -F: '{sum += $2} END {print sum}' || echo "0")
FIXME_COUNT=$(rg -c "FIXME" 2>/dev/null | awk -F: '{sum += $2} END {print sum}' || echo "0")
echo "TODO comments: $TODO_COUNT"
echo "FIXME comments: $FIXME_COUNT"
echo ""

# Shell script health (if any)
SHELL_SCRIPTS=$(fd -e sh | wc -l | tr -d ' ')
if [ "$SHELL_SCRIPTS" -gt 0 ] && command -v shellcheck &>/dev/null; then
    echo "--- Shell Script Health ---"
    echo "Total shell scripts: $SHELL_SCRIPTS"

    # Count scripts with issues
    ISSUES=0
    while IFS= read -r script; do
        if ! shellcheck "$script" &>/dev/null; then
            ((ISSUES++)) || true
        fi
    done < <(fd -e sh)

    echo "Scripts with shellcheck issues: $ISSUES"
    if [ "$ISSUES" -gt 0 ]; then
        echo "Run: fd -e sh -x shellcheck"
    fi
    echo ""
fi

# Git statistics (if in git repo)
if git rev-parse --git-dir > /dev/null 2>&1; then
    echo "--- Git Information ---"
    echo "Branch: $(git branch --show-current)"
    echo "Commits: $(git rev-list --count HEAD)"
    echo "Contributors: $(git log --format='%an' | sort -u | wc -l | tr -d ' ')"
    echo "Last commit: $(git log -1 --format='%ar')"
    echo ""
fi

# Dependencies (if package.json exists)
if [ -f "package.json" ] && command -v jq &>/dev/null; then
    echo "--- Dependencies (npm) ---"
    DEPS=$(jq -r '.dependencies // {} | keys | length' package.json)
    DEV_DEPS=$(jq -r '.devDependencies // {} | keys | length' package.json)
    echo "Production dependencies: $DEPS"
    echo "Dev dependencies: $DEV_DEPS"
    echo ""
fi

# Large files
echo "--- Largest Files (top 10) ---"
fd -t f -x du -h {} \; | sort -rh | head -10
echo ""

echo "=== Analysis Complete ==="
