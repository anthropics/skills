#!/usr/bin/env bash
# Bootstrap a new project with mise, just, pre-commit, and optionally direnv/sops
# Usage: ./project-setup.sh [project-directory]

set -euo pipefail

PROJECT_DIR="${1:-.}"
SKILL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "Setting up project in: $PROJECT_DIR"
echo ""

# Check required tools
MISSING=()
for cmd in mise just pre-commit; do
    if ! command -v "$cmd" &> /dev/null; then
        MISSING+=("$cmd")
    fi
done

if [ ${#MISSING[@]} -gt 0 ]; then
    echo "Missing required tools: ${MISSING[*]}"
    echo "Install with: brew install ${MISSING[*]}"
    exit 1
fi

# Check optional tools
OPTIONAL_MISSING=()
for cmd in direnv sops age; do
    if ! command -v "$cmd" &> /dev/null; then
        OPTIONAL_MISSING+=("$cmd")
    fi
done

if [ ${#OPTIONAL_MISSING[@]} -gt 0 ]; then
    echo "Optional tools not installed: ${OPTIONAL_MISSING[*]}"
    echo "Install with: brew install ${OPTIONAL_MISSING[*]}"
    echo ""
fi

cd "$PROJECT_DIR"

# 1. Setup mise
if [ ! -f ".mise.toml" ]; then
    echo "Creating .mise.toml..."
    cp "$SKILL_DIR/assets/.mise.toml" .mise.toml
    echo "✓ Created .mise.toml"
else
    echo "⊘ .mise.toml already exists"
fi

# 2. Setup direnv (optional)
if command -v direnv &> /dev/null; then
    if [ ! -f ".envrc" ]; then
        echo "Creating .envrc..."
        cp "$SKILL_DIR/assets/.envrc" .envrc
        echo "✓ Created .envrc"
        echo "  Run: direnv allow"
    else
        echo "⊘ .envrc already exists"
    fi
else
    echo "⊘ Skipping .envrc (direnv not installed)"
fi

# 3. Setup just
if [ ! -f "justfile" ]; then
    echo "Creating justfile..."
    cp "$SKILL_DIR/assets/justfile" justfile
    echo "✓ Created justfile"
else
    echo "⊘ justfile already exists"
fi

# 4. Setup pre-commit
if [ ! -f ".pre-commit-config.yaml" ]; then
    echo "Creating .pre-commit-config.yaml..."
    cp "$SKILL_DIR/assets/.pre-commit-config.yaml" .pre-commit-config.yaml
    echo "✓ Created .pre-commit-config.yaml"
    echo "  Run: pre-commit install"
else
    echo "⊘ .pre-commit-config.yaml already exists"
fi

# 5. Setup sops (optional)
if command -v sops &> /dev/null && command -v age-keygen &> /dev/null; then
    read -p "Setup sops for encrypted secrets? (y/N): " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        if [ ! -f ".sops.yaml" ]; then
            # Check if age key exists
            if [ ! -f "$HOME/.config/age/keys.txt" ]; then
                echo "Generating age key..."
                mkdir -p "$HOME/.config/age"
                age-keygen -o "$HOME/.config/age/keys.txt"
            fi

            # Get public key
            PUBKEY=$(age-keygen -y "$HOME/.config/age/keys.txt")

            echo "Creating .sops.yaml..."
            cp "$SKILL_DIR/assets/.sops.yaml" .sops.yaml
            # Update with actual public key
            if command -v sd &> /dev/null; then
                sd 'age1ql3z7hjy54pw3hyww5ayyfg7zqgvc7w3j2elw8zmrj2kg5sfn9aqmcac8p' "$PUBKEY" .sops.yaml
            else
                echo "  Note: Update .sops.yaml with your age public key: $PUBKEY"
            fi
            echo "✓ Created .sops.yaml"
            echo "  Your private key is at: ~/.config/age/keys.txt"
            echo "  Your public key: $PUBKEY"
        else
            echo "⊘ .sops.yaml already exists"
        fi
    fi
else
    echo "⊘ Skipping sops setup (sops/age not installed)"
fi

echo ""
echo "Project setup complete!"
echo ""
echo "Next steps:"
echo "  1. Review and customize the generated config files"
if command -v direnv &> /dev/null && [ -f ".envrc" ]; then
    echo "  2. Run: direnv allow"
fi
echo "  3. Run: mise install"
echo "  4. Run: pre-commit install"
echo "  5. Run: just --list"
echo ""
echo "Useful commands:"
echo "  - Analyze codebase: tokei ."
echo "  - Lint shell scripts: fd -e sh -x shellcheck"
echo "  - Search code: rg 'pattern'"
echo "  - Quick replace: sd 'old' 'new' file.txt -p"
