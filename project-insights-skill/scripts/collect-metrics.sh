#!/bin/bash
# collect-metrics.sh
# Helper script to collect project metrics for analysis

set -euo pipefail

PROJECT_DIR="${1:-.}"
OUTPUT_FILE="${2:-metrics.json}"

echo "🔍 Collecting metrics from: $PROJECT_DIR"
echo ""

cd "$PROJECT_DIR" || exit 1

# Initialize JSON structure
cat > "$OUTPUT_FILE" << 'EOF'
{
  "collection_date": "",
  "project_path": "",
  "code_statistics": {},
  "git_statistics": {},
  "project_structure": {},
  "file_counts": {},
  "dependencies": {}
}
EOF

# Temporary files
TMP_DIR=$(mktemp -d)
CLOC_FILE="$TMP_DIR/cloc.json"
GIT_LOG="$TMP_DIR/git.log"
GIT_CONTRIB="$TMP_DIR/contributors.txt"
STRUCTURE="$TMP_DIR/structure.txt"

echo "📊 Running code analysis..."

# Run cloc if available
if command -v cloc &> /dev/null; then
    cloc . --exclude-dir=node_modules,venv,__pycache__,.git,dist,build,target \
        --json --out="$CLOC_FILE" 2>/dev/null || echo "{}" > "$CLOC_FILE"
    echo "✓ Code statistics collected"
else
    echo "⚠️  cloc not found, skipping detailed code analysis"
    echo "{}" > "$CLOC_FILE"
fi

# Git statistics
if [ -d ".git" ]; then
    echo "📈 Analyzing git history..."

    # Commit history
    git log --oneline --all --date=short --pretty=format:'%h|%ad|%an|%s' > "$GIT_LOG" 2>/dev/null || touch "$GIT_LOG"

    # Contributors
    git shortlog -sn --all > "$GIT_CONTRIB" 2>/dev/null || touch "$GIT_CONTRIB"

    # Activity timeline
    git log --all --format="%ad" --date=short 2>/dev/null | sort | uniq -c > "$TMP_DIR/activity.txt" || touch "$TMP_DIR/activity.txt"

    echo "✓ Git statistics collected"
else
    echo "⚠️  Not a git repository, skipping git analysis"
    touch "$GIT_LOG" "$GIT_CONTRIB" "$TMP_DIR/activity.txt"
fi

# Project structure
echo "📁 Analyzing project structure..."
if command -v tree &> /dev/null; then
    tree -L 3 -I 'node_modules|venv|__pycache__|.git|dist|build|target' -a > "$STRUCTURE" 2>/dev/null || echo "Failed" > "$STRUCTURE"
else
    find . -type d -maxdepth 3 | grep -v "node_modules\|venv\|__pycache__\|\.git" > "$STRUCTURE" 2>/dev/null || touch "$STRUCTURE"
fi
echo "✓ Structure analyzed"

# File counts by extension
echo "📋 Counting files by type..."
find . -type f -not -path "*/node_modules/*" -not -path "*/venv/*" -not -path "*/.git/*" 2>/dev/null | \
    sed 's/.*\.//' | sort | uniq -c | sort -rn > "$TMP_DIR/extensions.txt"
echo "✓ File counts complete"

# Size analysis
echo "💾 Calculating sizes..."
du -sh . 2>/dev/null > "$TMP_DIR/total_size.txt" || echo "Unknown" > "$TMP_DIR/total_size.txt"
du -sh */ 2>/dev/null | sort -hr > "$TMP_DIR/dir_sizes.txt" || touch "$TMP_DIR/dir_sizes.txt"
echo "✓ Size analysis complete"

# Detect dependencies
echo "🔍 Detecting dependencies..."

# Python
if [ -f "requirements.txt" ]; then
    wc -l requirements.txt | awk '{print $1}' > "$TMP_DIR/python_deps.txt"
elif [ -f "pyproject.toml" ]; then
    echo "Poetry project" > "$TMP_DIR/python_deps.txt"
fi

# Node.js
if [ -f "package.json" ]; then
    if command -v jq &> /dev/null; then
        jq -r '.dependencies | keys | length' package.json > "$TMP_DIR/node_deps.txt" 2>/dev/null || echo "0" > "$TMP_DIR/node_deps.txt"
    else
        grep -c '"' package.json > "$TMP_DIR/node_deps.txt" 2>/dev/null || echo "Unknown" > "$TMP_DIR/node_deps.txt"
    fi
fi

# Rust
if [ -f "Cargo.toml" ]; then
    grep -c "\\[dependencies" Cargo.toml > "$TMP_DIR/rust_deps.txt" 2>/dev/null || echo "0" > "$TMP_DIR/rust_deps.txt"
fi

echo "✓ Dependencies detected"

# Combine into JSON
echo "📦 Generating final report..."

# Use jq if available for proper JSON
if command -v jq &> /dev/null; then
    jq -n \
        --arg date "$(date -u +"%Y-%m-%dT%H:%M:%SZ")" \
        --arg path "$PWD" \
        --slurpfile cloc "$CLOC_FILE" \
        '{
            collection_date: $date,
            project_path: $path,
            code_statistics: $cloc[0],
            raw_data_location: "'"$TMP_DIR"'"
        }' > "$OUTPUT_FILE"
else
    # Fallback to basic format
    cat > "$OUTPUT_FILE" << EOF
{
  "collection_date": "$(date -u +"%Y-%m-%dT%H:%M:%SZ")",
  "project_path": "$PWD",
  "raw_data_location": "$TMP_DIR",
  "note": "Install jq for structured JSON output"
}
EOF
fi

echo ""
echo "✅ Metrics collection complete!"
echo ""
echo "Output file: $OUTPUT_FILE"
echo "Raw data: $TMP_DIR"
echo ""
echo "Files generated:"
echo "  - cloc.json         Code statistics"
echo "  - git.log           Commit history"
echo "  - contributors.txt  Contributor list"
echo "  - structure.txt     Directory tree"
echo "  - extensions.txt    File type counts"
echo "  - dir_sizes.txt     Directory sizes"
echo ""
echo "Next: Use these files to generate the insights report"
