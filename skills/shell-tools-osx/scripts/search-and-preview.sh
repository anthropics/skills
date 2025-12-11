#!/usr/bin/env bash
# Interactive file search with preview using fd, fzf, and bat
# Usage: ./search-and-preview.sh [directory]

set -euo pipefail

DIR="${1:-.}"

# Check required tools
for cmd in fd fzf bat; do
    if ! command -v "$cmd" &> /dev/null; then
        echo "Error: $cmd is not installed. Install with: brew install $cmd"
        exit 1
    fi
done

# Interactive file picker with preview
SELECTED=$(fd --type f . "$DIR" | \
    fzf --preview 'bat --color=always --style=numbers --line-range=:500 {}' \
        --preview-window=right:60%:wrap \
        --height=100% \
        --border \
        --prompt="Select file > " \
        --header="Enter to select, Esc to cancel")

if [ -n "$SELECTED" ]; then
    echo "Selected: $SELECTED"
    bat --paging=always "$SELECTED"
fi
