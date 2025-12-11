#!/usr/bin/env bash
# AST-aware code search and replace workflow
# Usage: ./code-search-replace.sh <language> <pattern> [replacement]

set -euo pipefail

if [ $# -lt 2 ]; then
    echo "Usage: $0 <language> <pattern> [replacement]"
    echo ""
    echo "Example: $0 ts 'console.log(\$X)' 'logger.debug(\$X)'"
    echo ""
    echo "Supported languages: ts, js, jsx, tsx, py, go, rust, etc."
    exit 1
fi

LANG="$1"
PATTERN="$2"
REPLACEMENT="${3:-}"

# Check if ast-grep is installed
if ! command -v sg &> /dev/null; then
    echo "Error: ast-grep (sg) is not installed. Install with: brew install ast-grep"
    exit 1
fi

echo "Searching for pattern: $PATTERN"
echo "Language: $LANG"
echo ""

# Search and display matches
MATCHES=$(sg -l "$LANG" -p "$PATTERN" --json | jq -r 'length')

if [ "$MATCHES" -eq 0 ]; then
    echo "No matches found."
    exit 0
fi

echo "Found $MATCHES match(es):"
echo ""
sg -l "$LANG" -p "$PATTERN"
echo ""

# If replacement provided, offer to apply
if [ -n "$REPLACEMENT" ]; then
    echo "Replacement: $REPLACEMENT"
    echo ""
    echo "Preview of changes (dry-run):"
    sg -l "$LANG" -p "$PATTERN" -r "$REPLACEMENT" --update --dry-run
    echo ""

    read -p "Apply these changes? (y/N): " -n 1 -r
    echo

    if [[ $REPLY =~ ^[Yy]$ ]]; then
        sg -l "$LANG" -p "$PATTERN" -r "$REPLACEMENT" --update
        echo "Changes applied!"
    else
        echo "Changes cancelled."
    fi
fi
