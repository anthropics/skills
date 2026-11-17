#!/bin/bash
# Audit Flow Setup Script
# Run this once to configure git drivers and initialize the audit database
#
# Works in two modes:
#   1. Installed as Claude Code skill: .claude/skills/audit-flow/setup.sh
#   2. Standalone: anywhere in your project

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Detect project root: if installed as .claude/skills/audit-flow/, go up 3 levels
# Otherwise, use git root or current directory
if [[ "$SCRIPT_DIR" == *".claude/skills/audit-flow"* ]]; then
    PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
else
    PROJECT_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
fi

echo "=== Audit Flow Setup ==="
echo "Project root: $PROJECT_ROOT"
echo "Skill dir:    $SCRIPT_DIR"
echo ""

# 1. Initialize the audit database (if not exists)
echo "[1/4] Initializing audit database..."
if [ -f "$PROJECT_ROOT/.audit/audit.db" ]; then
    echo "  Database already exists at .audit/audit.db"
else
    cd "$PROJECT_ROOT" && python "$SCRIPT_DIR/scripts/audit.py" init
    echo "  Created .audit/audit.db"
fi

# 2. Configure git merge/diff drivers
echo "[2/4] Configuring git drivers..."
cd "$PROJECT_ROOT" && python "$SCRIPT_DIR/scripts/audit.py" git-setup

# 3. Ensure .gitattributes has the audit.db entry
echo "[3/4] Checking .gitattributes..."
GITATTRIBUTES="$PROJECT_ROOT/.gitattributes"
if [ -f "$GITATTRIBUTES" ]; then
    if grep -q "\.audit/audit\.db" "$GITATTRIBUTES"; then
        echo "  .gitattributes already configured"
    else
        echo "  Adding audit.db entry to .gitattributes"
        echo "" >> "$GITATTRIBUTES"
        echo "# Audit database - custom merge/diff drivers" >> "$GITATTRIBUTES"
        echo ".audit/audit.db diff=sqlite merge=sqlite-audit" >> "$GITATTRIBUTES"
    fi
else
    echo "  Creating .gitattributes"
    cat > "$GITATTRIBUTES" << 'EOF'
# Git attributes

# Audit database - custom merge/diff drivers
.audit/audit.db diff=sqlite merge=sqlite-audit

# Ensure consistent line endings
* text=auto eol=lf
EOF
fi

# 4. Create audit output directory
echo "[4/4] Creating audit output directory..."
AUDIT_DIR="$PROJECT_ROOT/docs/audits"
mkdir -p "$AUDIT_DIR"
echo "  Created $AUDIT_DIR"

echo ""
echo "=== Setup Complete ==="
echo ""
echo "Usage:"
echo "  python $SCRIPT_DIR/scripts/audit.py list          # List sessions"
echo "  python $SCRIPT_DIR/scripts/audit.py show <name>   # Show session details"
echo "  python $SCRIPT_DIR/scripts/audit.py export <name> # Export session"
echo ""
echo "Git diff test:"
echo "  git diff .audit/audit.db"
echo ""
